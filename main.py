import os
import sys
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
from PIL import Image, ImageTk, ImageDraw, ImageEnhance, ImageFont
from queue import Queue, Empty
from threading import Thread, Lock, Event
from datetime import datetime, timedelta
import sqlite3
import cv2
import numpy as np
from pathlib import Path
import json
import logging
import requests
from io import BytesIO
import re
import time

# DTK imports
from DTKLPR5 import DTKLPRLibrary, LPREngine, LPRParams, BURN_POS, LicensePlate
from DTKVID import DTKVIDLibrary, VideoCapture, VideoFrame

# Setup logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    filename='lpr_system.log',
    filemode='a'
)
logger = logging.getLogger(__name__)

# Library path configuration
lib_path = '../../lib/windows/x64/'
os.environ['PATH'] = lib_path + os.pathsep + os.environ['PATH']

# Telegram configuration
TELEGRAM_BOT_TOKEN = "7663972479:AAFeABshDdOhWNY62Nt0W5C_lbjWH1csOJg"
TELEGRAM_CHAT_ID = "738339858"

# Global configurations
CONFIG = {
    'camera_index': 1,
    'camera_width': 1920,
    'camera_height': 1080,
    'levenshtein_threshold': 2,
    'suspicious_duration_minutes': 2,
    'min_plate_width': 80,
    'max_plate_width': 400,
    'countries': 'AZ,RU,GE,AM,TR',
    'fps_limit': 0,
    'duplicate_delay': 2000,
    'confirmation_count': 1,
    'num_threads': 0,
    'telegram_enabled': True,
    'save_images': True,
    'image_quality': 95,
    'preprocessing': {
        'contrast': 1,
        'brightness': 1,
        'sharpness': 1
    },
    'plate_validation': {
        'min_length': 3,
        'max_length': 10,
        'allowed_chars': 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789'
    }
}

# Thread-safe queues and flags
plate_queue = Queue()
telegram_queue = Queue()
db_queue = Queue()
image_queue = Queue()  # Убираем ограничение, чтобы не блокировать основной поток
stop_flag = Event()
camera_lock = Lock()

class DatabaseManager:
    def __init__(self, db_path='lpr_surveillance.db'):
        self.db_path = db_path
        self.conn = None
        self.db_lock = Lock()  # Добавляем блокировку для потокобезопасности
        self.init_database()
        
    def init_database(self):
        """Initialize database with all required tables"""
        self.conn = sqlite3.connect(self.db_path, check_same_thread=False, timeout=30.0)
        self.conn.execute("PRAGMA journal_mode = WAL")
        self.conn.execute("PRAGMA synchronous = NORMAL")
        self.conn.execute("PRAGMA cache_size = -10000")  # 10MB cache
        
        cursor = self.conn.cursor()
        
        # Recognized plates table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS recognized_plates (
                plate_text_canonical TEXT PRIMARY KEY,
                first_appearance_ts DATETIME,
                last_appearance_ts DATETIME,
                detection_count INTEGER DEFAULT 1,
                country_code TEXT,
                highest_confidence_achieved REAL,
                is_suspiciously_present BOOLEAN DEFAULT 0,
                is_blacklisted BOOLEAN DEFAULT 0,
                last_detection_image_path TEXT,
                last_detection_confidence REAL
            )
        ''')
        
        # Original detections table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS original_detections (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                canonical_plate_text_ref TEXT,
                raw_detected_text TEXT,
                detection_ts DATETIME,
                confidence REAL,
                image_path TEXT,
                FOREIGN KEY (canonical_plate_text_ref) REFERENCES recognized_plates(plate_text_canonical)
            )
        ''')
        
        # Blacklist table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS blacklist_plates (
                plate_text TEXT PRIMARY KEY,
                reason TEXT,
                danger_level TEXT CHECK(danger_level IN ('LOW', 'MEDIUM', 'HIGH', 'CRITICAL')),
                date_added DATETIME,
                notes TEXT
            )
        ''')
        
        # Application settings table
        cursor.execute('''
            CREATE TABLE IF NOT EXISTS application_settings (
                key TEXT PRIMARY KEY,
                value TEXT
            )
        ''')
        
        # Create indexes for faster queries
        cursor.execute('''
            CREATE INDEX IF NOT EXISTS idx_plates_last_seen 
            ON recognized_plates(last_appearance_ts DESC)
        ''')
        cursor.execute('''
            CREATE INDEX IF NOT EXISTS idx_blacklist_plate 
            ON blacklist_plates(plate_text)
        ''')
        cursor.execute('''
            CREATE INDEX IF NOT EXISTS idx_detections_canonical 
            ON original_detections(canonical_plate_text_ref)
        ''')
        
        self.conn.commit()
        self.load_settings()
        
    def load_settings(self):
        """Load settings from database"""
        with self.db_lock:
            cursor = self.conn.cursor()
            cursor.execute("SELECT key, value FROM application_settings")
            for key, value in cursor.fetchall():
                if key in CONFIG:
                    try:
                        if isinstance(CONFIG[key], bool):
                            CONFIG[key] = value.lower() == 'true'
                        elif isinstance(CONFIG[key], int):
                            CONFIG[key] = int(value)
                        elif isinstance(CONFIG[key], float):
                            CONFIG[key] = float(value)
                        elif key in ['preprocessing', 'plate_validation']:
                            try:
                                loaded_data = json.loads(value)
                                if isinstance(loaded_data, dict):
                                    CONFIG[key] = loaded_data
                                else:
                                    logger.warning(f"Invalid JSON data type for {key}, keeping default")
                            except json.JSONDecodeError as e:
                                logger.warning(f"Failed to parse JSON for {key}: {e}")
                        else:
                            CONFIG[key] = value
                    except Exception as e:
                        logger.warning(f"Failed to load setting {key}: {e}")

                    
    def save_settings(self):
        """Save current settings to database"""
        with self.db_lock:
            cursor = self.conn.cursor()
            for key, value in CONFIG.items():
                if key == 'preprocessing' or key == 'plate_validation':
                    value = json.dumps(value)
                else:
                    value = str(value)
                
            cursor.execute(
                "INSERT OR REPLACE INTO application_settings (key, value) VALUES (?, ?)",
                (key, value)
            )
        self.conn.commit()
        
    def close(self):
        if self.conn:
            with self.db_lock:
                self.conn.close()

def levenshtein_distance(s1, s2):
    """Calculate Levenshtein distance between two strings"""
    if len(s1) < len(s2):
        return levenshtein_distance(s2, s1)
    
    if len(s2) == 0:
        return len(s1)
    
    previous_row = range(len(s2) + 1)
    for i, c1 in enumerate(s1):
        current_row = [i + 1]
        for j, c2 in enumerate(s2):
            insertions = previous_row[j + 1] + 1
            deletions = current_row[j] + 1
            substitutions = previous_row[j] + (c1 != c2)
            current_row.append(min(insertions, deletions, substitutions))
        previous_row = current_row
    
    return previous_row[-1]

def preprocess_image(image):
    """Apply preprocessing to improve recognition quality"""
    try:
        # Контраст
        enhancer = ImageEnhance.Contrast(image)
        image = enhancer.enhance(CONFIG['preprocessing']['contrast'])
        
        # Яркость
        enhancer = ImageEnhance.Brightness(image)
        image = enhancer.enhance(CONFIG['preprocessing']['brightness'])
        
        # Резкость
        enhancer = ImageEnhance.Sharpness(image)
        image = enhancer.enhance(CONFIG['preprocessing']['sharpness'])
        
        return image
    except Exception as e:
        logger.error(f"Image preprocessing failed: {e}")
        return image

class TelegramNotifier:
    def __init__(self, bot_token, chat_id):
        self.bot_token = bot_token
        self.chat_id = chat_id
        self.base_url = f"https://api.telegram.org/bot{bot_token}"
        self.enabled = CONFIG['telegram_enabled']
        self.message_queue = Queue()
        self.last_message_time = {}
        
    def send_message(self, text, plate=None):
        """Send text message to Telegram with rate limiting"""
        if not self.enabled:
            return
            
        try:
            # Rate limiting per plate (1 message per 2 minutes)
            if plate:
                now = time.time()
                if plate in self.last_message_time and now - self.last_message_time[plate] < 120:
                    logger.info(f"Skipping duplicate Telegram alert for plate: {plate}")
                    return
                self.last_message_time[plate] = now
                
                # Очистка старых записей (старше 10 минут)
                old_plates = [p for p, t in self.last_message_time.items() if now - t > 600]
                for old_plate in old_plates:
                    del self.last_message_time[old_plate]
            
            url = f"{self.base_url}/sendMessage"
            data = {
                'chat_id': self.chat_id,
                'text': text,
                'parse_mode': 'HTML'
            }
            response = requests.post(url, data=data, timeout=10)
            if response.status_code != 200:
                logger.error(f"Telegram API error: {response.status_code} - {response.text}")
            return response.json()
        except Exception as e:
            logger.error(f"Failed to send Telegram message: {e}")
            return None
            
    def send_photo(self, photo_path, caption=""):
        """Send photo to Telegram with compression"""
        if not self.enabled:
            return
            
        try:
            # Compress image before sending
            with Image.open(photo_path) as img:
                img.thumbnail((1024, 768))
                buffer = BytesIO()
                img.save(buffer, format="JPEG", quality=85)
                buffer.seek(0)
                
                url = f"{self.base_url}/sendPhoto"
                files = {'photo': ('plate.jpg', buffer, 'image/jpeg')}
                data = {
                    'chat_id': self.chat_id,
                    'caption': caption,
                    'parse_mode': 'HTML'
                }
                response = requests.post(url, data=data, files=files, timeout=15)
            return response.json()
        except Exception as e:
            logger.error(f"Failed to send Telegram photo: {e}")
            return None

class PlateProcessor:
    def __init__(self, db_manager, telegram_notifier):
        self.db = db_manager
        self.telegram = telegram_notifier
        self.processing_lock = Lock()
        
    def process_plate(self, plate: LicensePlate):
        """Process detected plate with validation and Levenshtein consolidation"""
        with self.processing_lock:
            try:
                plate_text = plate.Text().upper().replace(' ', '')
                confidence = plate.Confidence()
                timestamp = datetime.now()
                
                # Skip low confidence detections
                if confidence < 70:
                    logger.info(f"Low confidence plate skipped: {plate_text} ({confidence}%)")
                    return None
                
                # Find canonical plate using Levenshtein distance
                with self.db.db_lock:
                    cursor = self.db.conn.cursor()
                    cursor.execute("SELECT plate_text_canonical FROM recognized_plates")
                    canonical_plates = [row[0] for row in cursor.fetchall()]
                
                canonical_match = None
                min_distance = float('inf')
                
                for canonical in canonical_plates:
                    distance = levenshtein_distance(plate_text, canonical)
                    if distance <= CONFIG['levenshtein_threshold'] and distance < min_distance:
                        min_distance = distance
                        canonical_match = canonical
                
                # Save image if enabled
                image_path = None
                if CONFIG['save_images']:
                    # Save image synchronously to ensure path is available
                    try:
                        image_path = self.save_plate_image(plate, timestamp, canonical_match or plate_text)
                        if not image_path:
                            logger.warning(f"Failed to save image for plate {canonical_match or plate_text}")
                    except Exception as e:
                        logger.error(f"Error saving plate image: {e}")
                        image_path = None
                
                if canonical_match:
                    # Update existing canonical plate
                    self._update_canonical_plate(canonical_match, confidence, timestamp, image_path)
                    canonical_text = canonical_match
                else:
                    # Create new canonical plate
                    self._create_canonical_plate(plate_text, plate, timestamp, image_path)
                    canonical_text = plate_text
                
                # Save original detection
                with self.db.db_lock:
                    cursor.execute('''
                        INSERT INTO original_detections 
                        (canonical_plate_text_ref, raw_detected_text, detection_ts, confidence, image_path)
                        VALUES (?, ?, ?, ?, ?)
                    ''', (canonical_text, plate.Text(), timestamp, confidence, image_path))
                    
                    self.db.conn.commit()
                
                # Check for alerts
                self._check_alerts(canonical_text, timestamp, image_path)
                
                return canonical_text
                
            except Exception as e:
                logger.error(f"Plate processing error: {e}")
                return None
                
    def _update_canonical_plate(self, canonical_text, confidence, timestamp, image_path):
        """Update existing canonical plate record"""
        with self.db.db_lock:
            cursor = self.db.conn.cursor()
        
        cursor.execute('''
            UPDATE recognized_plates 
            SET last_appearance_ts = ?,
                detection_count = detection_count + 1,
                highest_confidence_achieved = MAX(highest_confidence_achieved, ?),
                last_detection_image_path = ?,
                last_detection_confidence = ?
            WHERE plate_text_canonical = ?
        ''', (timestamp, confidence, image_path, confidence, canonical_text))
        
        # Check suspicious presence
        cursor.execute('''
            SELECT first_appearance_ts, last_appearance_ts FROM recognized_plates 
            WHERE plate_text_canonical = ?
        ''', (canonical_text,))
        
        row = cursor.fetchone()
        if row:
            try:
                first_appearance = datetime.fromisoformat(row[0])
                last_appearance = datetime.fromisoformat(row[1])
            except (ValueError, TypeError) as e:
                logger.error(f"Invalid timestamp: {e}")
                return
            duration = last_appearance - first_appearance
            
            if duration > timedelta(minutes=CONFIG['suspicious_duration_minutes']):
                cursor.execute('''
                    UPDATE recognized_plates 
                    SET is_suspiciously_present = 1 
                    WHERE plate_text_canonical = ?
                ''', (canonical_text,))
                
    def _create_canonical_plate(self, plate_text, plate, timestamp, image_path):
        """Create new canonical plate record"""
        with self.db.db_lock:
            cursor = self.db.conn.cursor()
        
        # Check if blacklisted
        cursor.execute(
            "SELECT 1 FROM blacklist_plates WHERE plate_text = ?", 
            (plate_text,)
        )
        is_blacklisted = cursor.fetchone() is not None
        
        cursor.execute('''
            INSERT INTO recognized_plates 
            (plate_text_canonical, first_appearance_ts, last_appearance_ts, 
             detection_count, country_code, highest_confidence_achieved, 
             is_blacklisted, last_detection_image_path, last_detection_confidence)
            VALUES (?, ?, ?, 1, ?, ?, ?, ?, ?)
        ''', (plate_text, timestamp, timestamp, plate.CountryCode(), 
              plate.Confidence(), is_blacklisted, image_path, plate.Confidence()))
              
    def _check_alerts(self, canonical_text, timestamp, image_path):
        """Check and send alerts for blacklist and suspicious presence"""
        with self.db.db_lock:
            cursor = self.db.conn.cursor()
        
        # Check blacklist
        cursor.execute('''
            SELECT b.reason, b.danger_level 
            FROM blacklist_plates b 
            WHERE b.plate_text = ?
        ''', (canonical_text,))
        
        blacklist_info = cursor.fetchone()
        if blacklist_info:
            reason, danger_level = blacklist_info
            alert_msg = f"🚨 <b>BLACKLIST ALERT</b> 🚨\n"
            alert_msg += f"Plate: <b>{canonical_text}</b>\n"
            alert_msg += f"Danger Level: <b>{danger_level}</b>\n"
            alert_msg += f"Reason: {reason}\n"
            alert_msg += f"Time: {timestamp.strftime('%Y-%m-%d %H:%M:%S')}"
            
            telegram_queue.put(('message', alert_msg, canonical_text))
            if image_path:
                telegram_queue.put(('photo', image_path, alert_msg))
                
        # Check suspicious presence
        cursor.execute('''
            SELECT first_appearance_ts, is_suspiciously_present 
            FROM recognized_plates 
            WHERE plate_text_canonical = ?
        ''', (canonical_text,))
        
        row = cursor.fetchone()
        if row:
            first_appearance_str, was_suspicious = row
            try:
                first_appearance = datetime.fromisoformat(first_appearance_str)
            except (ValueError, TypeError) as e:
                logger.error(f"Invalid timestamp: {e}")
                return
            duration = timestamp - first_appearance
            
            if duration > timedelta(minutes=CONFIG['suspicious_duration_minutes']) and not was_suspicious:
                alert_msg = f"⚠️ <b>SUSPICIOUS PRESENCE ALERT</b> ⚠️\n"
                alert_msg += f"Plate: <b>{canonical_text}</b>\n"
                alert_msg += f"Duration: <b>{int(duration.total_seconds() / 60)} minutes</b>\n"
                alert_msg += f"First seen: {first_appearance.strftime('%H:%M:%S')}\n"
                alert_msg += f"Current time: {timestamp.strftime('%H:%M:%S')}"
                
                telegram_queue.put(('message', alert_msg, canonical_text))
                if image_path:
                    telegram_queue.put(('photo', image_path, alert_msg))
                    
    def save_plate_image(self, plate: LicensePlate, timestamp, canonical_text):
        """Save plate detection image with preprocessing"""
        try:
            date_dir = timestamp.strftime('%Y-%m-%d')
            # Санитизация имени директории
            safe_text = re.sub(r'[<>:"/\\|?*]', '_', canonical_text)
            safe_text = safe_text[:50]  # Ограничиваем длину
            save_dir = Path('detections') / date_dir / safe_text
            save_dir.mkdir(parents=True, exist_ok=True)
            filename = f"{timestamp.strftime('%H%M%S_%f')}.jpg"
            filepath = save_dir / filename
            # Get full frame image
            frame_image = plate.GetImage()
            # Apply preprocessing
            frame_image = preprocess_image(frame_image)
            # Draw bounding box and text
            draw = ImageDraw.Draw(frame_image)
            try:
                font = ImageFont.truetype("arial.ttf", 20)
            except Exception:
                font = ImageFont.load_default()
            draw.rectangle(
                [(plate.X(), plate.Y()), 
                 (plate.X() + plate.Width(), plate.Y() + plate.Height())],
                outline="red", width=3
            )
            draw.text((plate.X(), max(0, plate.Y() - 20)), 
                     f"{plate.Text()} ({plate.Confidence()}%)", 
                     fill="red", font=font)
            # Save processed image
            frame_image.save(str(filepath), 'JPEG', quality=int(CONFIG['image_quality']))
            # Also save cropped plate
            plate_image = plate.GetPlateImage()
            plate_filepath = save_dir / f"plate_{filename}"
            plate_image.save(str(plate_filepath), 'JPEG', quality=int(CONFIG['image_quality']))
            return str(filepath)
        except Exception as e:
            logger.error(f"Failed to save image: {e}")
            return None

class LPRApp:
    def __init__(self, root):
        self.root = root
        self.root.title("LPR Counter-Surveillance System v2.0")
        self.root.geometry("1400x800")
        
        # Initialize components
        self.db = DatabaseManager()
        self.telegram = TelegramNotifier(TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID)
        self.processor = PlateProcessor(self.db, self.telegram)
        
        # Camera info
        self.camera_info_lock = Lock()
        self.camera_info = {
            "status": "Initializing...",
            "fps": 0,
            "frames_processed": 0,
            "plates_detected": 0,
            "last_frame_time": time.time()
        }
        
        # Initialize UI
        self.setup_ui()
        
        # Initialize LPR engine
        self.engine = self.initialize_lpr_engine()
        self.video_capture = None
        self.is_paused = False
        
        # Start worker threads
        self.start_workers()
        
    def setup_ui(self):
        """Setup the main UI"""
        # Configure style
        style = ttk.Style()
        style.configure('TFrame', background='#f0f0f0')
        style.configure('TLabel', background='#f0f0f0')
        style.configure('TButton', font=('Arial', 10))
        style.configure('Title.TLabel', font=('Arial', 14, 'bold'))
        style.configure('Status.TLabel', font=('Arial', 10, 'bold'))
        
        # Main container
        main_container = ttk.PanedWindow(self.root, orient=tk.HORIZONTAL)
        main_container.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Left panel - Video and info
        left_panel = ttk.Frame(main_container)
        main_container.add(left_panel, weight=1)
        
        # Camera status
        status_frame = ttk.LabelFrame(left_panel, text="System Status", padding=10)
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.status_label = ttk.Label(status_frame, text="Initializing...", style='Status.TLabel')
        self.status_label.pack(anchor='w')
        
        # Stats frame
        stats_frame = ttk.Frame(status_frame)
        stats_frame.pack(fill=tk.X, pady=5)
        
        ttk.Label(stats_frame, text="FPS:").pack(side=tk.LEFT, padx=5)
        self.fps_label = ttk.Label(stats_frame, text="0.0", width=6)
        self.fps_label.pack(side=tk.LEFT)
        
        ttk.Label(stats_frame, text="Frames:").pack(side=tk.LEFT, padx=5)
        self.frames_label = ttk.Label(stats_frame, text="0", width=8)
        self.frames_label.pack(side=tk.LEFT)
        
        ttk.Label(stats_frame, text="Plates:").pack(side=tk.LEFT, padx=5)
        self.plates_label = ttk.Label(stats_frame, text="0", width=8)
        self.plates_label.pack(side=tk.LEFT)
        
        # Video display
        video_frame = ttk.LabelFrame(left_panel, text="Live Feed", padding=5)
        video_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        self.video_label = ttk.Label(video_frame)
        self.video_label.pack(fill=tk.BOTH, expand=True)
        
        # Control buttons
        control_frame = ttk.Frame(left_panel)
        control_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.connect_btn = ttk.Button(control_frame, text="Connect Camera", 
                                     command=self.connect_camera)
        self.connect_btn.pack(side=tk.LEFT, padx=5)
        
        self.pause_btn = ttk.Button(control_frame, text="Pause", 
                                   command=self.toggle_pause)
        self.pause_btn.pack(side=tk.LEFT, padx=5)
        
        ttk.Button(control_frame, text="Settings", 
                  command=self.show_settings_dialog).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(control_frame, text="Export Report", 
                  command=self.export_report).pack(side=tk.LEFT, padx=5)
        
        # Right panel - Results
        right_panel = ttk.Frame(main_container)
        main_container.add(right_panel, weight=2)
        
        # Title
        title_frame = ttk.Frame(right_panel)
        title_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(title_frame, text="License Plate Recognition", style='Title.TLabel').pack(side=tk.LEFT)
        
        # Search bar
        search_frame = ttk.Frame(right_panel)
        search_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(search_frame, text="Search:").pack(side=tk.LEFT, padx=5)
        self.search_var = tk.StringVar()
        search_entry = ttk.Entry(search_frame, textvariable=self.search_var)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        search_entry.bind('<KeyRelease>', self.on_search)
        
        # Results table
        results_frame = ttk.LabelFrame(right_panel, text="Real-Time Results", padding=5)
        results_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Treeview for results
        columns = ('Plate', 'Count', 'Last Seen', 'Duration', 'Confidence', 'Status')
        self.results_tree = ttk.Treeview(results_frame, columns=columns, show='headings', selectmode='browse')
        
        for col in columns:
            self.results_tree.heading(col, text=col)
            self.results_tree.column(col, width=100)
            
        # Configure column widths
        self.results_tree.column('Plate', width=120)
        self.results_tree.column('Count', width=60)
        self.results_tree.column('Last Seen', width=100)
        self.results_tree.column('Duration', width=80)
        self.results_tree.column('Confidence', width=80)
        self.results_tree.column('Status', width=100)
        
        # Scrollbars
        vsb = ttk.Scrollbar(results_frame, orient="vertical", command=self.results_tree.yview)
        hsb = ttk.Scrollbar(results_frame, orient="horizontal", command=self.results_tree.xview)
        self.results_tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        
        # Pack treeview and scrollbars
        self.results_tree.grid(row=0, column=0, sticky='nsew')
        vsb.grid(row=0, column=1, sticky='ns')
        hsb.grid(row=1, column=0, sticky='ew')
        
        results_frame.grid_rowconfigure(0, weight=1)
        results_frame.grid_columnconfigure(0, weight=1)
        
        # Bind double-click to show details
        self.results_tree.bind('<Double-1>', self.show_plate_details)
        
        # Status bar
        self.status_bar = ttk.Label(self.root, text="Ready", relief=tk.SUNKEN)
        self.status_bar.pack(side=tk.BOTTOM, fill=tk.X)
        
    def initialize_lpr_engine(self):
        """Initialize LPR engine with parameters"""
        try:
            params = LPRParams(DTKLPRLibrary(lib_path))
            params.MinPlateWidth = CONFIG['min_plate_width']
            params.MaxPlateWidth = CONFIG['max_plate_width']
            params.Countries = CONFIG['countries']
            params.FormatPlateText = True
            params.RotateAngle = 0
            params.FPSLimit = CONFIG['fps_limit']
            params.DuplicateResultsDelay = CONFIG['duplicate_delay']
            params.ResultConfirmationsCount = CONFIG['confirmation_count']
            params.NumThreads = CONFIG['num_threads']
            params.RecognitionOnMotion = True
            
            engine = LPREngine(params, True, self.license_plate_detected_callback)
            
            if engine.IsLicensed() != 0:
                logger.warning("LPR License is invalid")
                self.status_bar.config(text="Warning: LPR license is invalid")
                
            return engine
        except Exception as e:
            logger.error(f"Failed to initialize LPR engine: {e}")
            messagebox.showerror("Initialization Error", f"Failed to initialize LPR engine: {e}")
            return None
            
    def license_plate_detected_callback(self, engine: LPREngine, plate: LicensePlate):
        """Callback for plate detection"""
        if self.is_paused:
            return 0
            
        with self.camera_info_lock:
            self.camera_info['plates_detected'] += 1
        plate_queue.put(plate)
        return 0
        
    def frame_captured_callback(self, video_capture: VideoCapture, frame: VideoFrame, engine):
        """Callback for frame capture"""
        if self.is_paused or frame.GetHeight() <= 0 or frame.GetWidth() <= 0:
            return
            
        # Calculate FPS
        with self.camera_info_lock:
            current_time = time.time()
            elapsed = current_time - self.camera_info['last_frame_time']
            self.camera_info['last_frame_time'] = current_time
            if elapsed > 0:
                self.camera_info['fps'] = 0.9 * self.camera_info['fps'] + 0.1 * (1 / elapsed)
            
            self.camera_info['frames_processed'] += 1
        ret = self.engine.PutFrame(frame, frame.Timestamp())
        
        # Update video display
        if self.camera_info['frames_processed'] % 2 == 0:  # Update every 2 frames
            try:
                # Get PIL Image from frame
                pil_image = frame.GetImage()
                
                # Resize for display
                display_size = (640, 480)
                pil_image = pil_image.resize(display_size, Image.Resampling.LANCZOS)
                
                # Convert to PhotoImage
                photo = ImageTk.PhotoImage(pil_image)
                
                # Update label in main thread
                self.root.after_idle(self.update_video_display, photo)
            except Exception as e:
                logger.error(f"Error updating video display: {e}")
            
    def update_video_display(self, photo):
        """Update video display in main thread"""
        # Освобождаем предыдущее изображение
        if hasattr(self.video_label, 'image'):
            del self.video_label.image
        self.video_label.configure(image=photo)
        self.video_label.image = photo
        
    def capture_error_callback(self, video_capture: VideoCapture, error_code: int, engine):
        """Callback for capture errors"""
        error_messages = {
            1: "Failed to open camera",
            2: "Failed to read frame",
            3: "End of video file"
        }
        
        error_msg = error_messages.get(error_code, f"Unknown error: {error_code}")
        with self.camera_info_lock:
            self.camera_info['status'] = f"Error: {error_msg}"
        logger.error(f"Camera error: {error_msg}")
        
        self.root.after(0, lambda: messagebox.showerror("Camera Error", error_msg))
        
    def connect_camera(self):
        """Connect to camera"""
        if self.video_capture:
            self.video_capture.StopCapture()
            
        try:
            self.video_capture = VideoCapture(
                self.frame_captured_callback,
                self.capture_error_callback,
                self.engine,
                DTKVIDLibrary(lib_path)
            )
            
            with self.camera_info_lock:
                self.camera_info['status'] = f"Connecting to camera {CONFIG['camera_index']}..."
            self.update_status()
            
            # Start capture in separate thread
            def start_capture():
                try:
                    ret = self.video_capture.StartCaptureFromDevice(
                        CONFIG['camera_index'],
                        CONFIG['camera_width'],
                        CONFIG['camera_height'])
                    
                    if ret == 0:
                        with self.camera_info_lock:
                            self.camera_info['status'] = "Connected"
                            self.camera_info['fps'] = self.video_capture.GetVideoFPS()
                    else:
                        with self.camera_info_lock:
                            self.camera_info['status'] = "Connection failed"
                except Exception as e:
                    with self.camera_info_lock:
                        self.camera_info['status'] = f"Connection error: {str(e)}"
                    logger.error(f"Camera connection error: {e}")
                
                self.root.after(0, self.update_status)
                
            Thread(target=start_capture, daemon=True).start()
        except Exception as e:
            with self.camera_info_lock:
                self.camera_info['status'] = f"Connection error: {str(e)}"
            logger.error(f"Camera connection error: {e}")
            self.update_status()
        
    def toggle_pause(self):
        """Toggle pause/resume processing"""
        self.is_paused = not self.is_paused
        self.pause_btn.config(text="Resume" if self.is_paused else "Pause")
        status = "PAUSED" if self.is_paused else "ACTIVE"
        self.status_bar.config(text=f"System status: {status}")
        
    def start_workers(self):
        """Start worker threads"""
        # Plate processing thread
        def plate_worker():
            while not stop_flag.is_set():
                try:
                    plate = plate_queue.get(timeout=0.1)
                    canonical = self.processor.process_plate(plate)
                    if canonical:
                        self.root.after(0, self.update_results)
                except Empty:
                    continue
                except Exception as e:
                    logger.error(f"Plate processing error: {e}")
                    
        # Telegram notification thread
        def telegram_worker():
            while not stop_flag.is_set():
                try:
                    item = telegram_queue.get(timeout=0.1)
                    if item[0] == 'message':
                        self.telegram.send_message(item[1], item[2] if len(item) > 2 else None)
                    elif item[0] == 'photo':
                        self.telegram.send_photo(item[1], item[2])
                except Empty:
                    continue
                except Exception as e:
                    logger.error(f"Telegram error: {e}")
                    
        # Image saving thread - now handles image path updates
        def image_worker():
            while not stop_flag.is_set():
                try:
                    plate_data = db_queue.get(timeout=0.5)
                    if plate_data[0] == 'update_image_path':
                        canonical_text, image_path = plate_data[1], plate_data[2]
                        # Update image path in database
                        cursor = self.db.conn.cursor()
                        cursor.execute('''
                            UPDATE recognized_plates 
                            SET last_detection_image_path = ?
                            WHERE plate_text_canonical = ?
                        ''', (image_path, canonical_text))
                        self.db.conn.commit()
                except Empty:
                    continue
                except Exception as e:
                    logger.error(f"Image path update error: {e}")
                    
        # UI update timer (instead of thread)
        def schedule_updates():
            if not stop_flag.is_set():
                self.update_status()
                self.root.after(1000, schedule_updates)
                
        def schedule_results():
            if not stop_flag.is_set():
                self.update_results()
                self.root.after(2000, schedule_results)
        
        # Schedule initial updates
        self.root.after(1000, schedule_updates)
        self.root.after(2000, schedule_results)
                
        # Start threads
        Thread(target=plate_worker, daemon=True).start()
        Thread(target=telegram_worker, daemon=True).start()
        Thread(target=image_worker, daemon=True).start()
        
    def update_status(self):
        """Update status display"""
        with self.camera_info_lock:
            status_text = f"Status: {self.camera_info['status']}"
            self.status_label.config(text=status_text)
            
            # Update stats
            self.fps_label.config(text=f"{self.camera_info['fps']:.1f}")
            self.frames_label.config(text=str(self.camera_info['frames_processed']))
            self.plates_label.config(text=str(self.camera_info['plates_detected']))
        
    def update_results(self):
        """Update results table"""
        # Clear existing items
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
            
        # Get search filter
        search_term = self.search_var.get().upper()
        
        # Query database
        with self.db.db_lock:
            cursor = self.db.conn.cursor()
            query = '''
                SELECT plate_text_canonical, detection_count, last_appearance_ts,
                       first_appearance_ts, is_suspiciously_present, is_blacklisted,
                       last_detection_confidence
                FROM recognized_plates
                WHERE plate_text_canonical LIKE ?
                ORDER BY last_appearance_ts DESC
                LIMIT 100
            '''
            
            cursor.execute(query, (f'%{search_term}%',))
            rows = cursor.fetchall()
        
        for row in rows:
            plate, count, last_ts, first_ts, suspicious, blacklisted, confidence = row
            
            # Calculate duration
            try:
                first_dt = datetime.fromisoformat(first_ts)
                last_dt = datetime.fromisoformat(last_ts)
            except (ValueError, TypeError) as e:
                logger.error(f"Invalid timestamp for plate {plate}: {e}")
                continue
            duration = last_dt - first_dt
            duration_str = f"{int(duration.total_seconds() / 60)}m"
            
            # Format last seen
            last_seen = last_dt.strftime('%H:%M:%S')
            
            # Status
            status = []
            if blacklisted:
                status.append("BLACKLIST")
            if suspicious:
                status.append("SUSPICIOUS")
            status_str = ", ".join(status) if status else "Normal"
            
            # Confidence
            confidence_str = f"{confidence}%"
            
            # Insert with color coding
            item = self.results_tree.insert('', 'end', values=(
                plate, count, last_seen, duration_str, confidence_str, status_str
            ))
            
            # Color code based on status
            if blacklisted:
                self.results_tree.item(item, tags=('blacklist',))
            elif suspicious:
                self.results_tree.item(item, tags=('suspicious',))
                
        # Configure tags
        self.results_tree.tag_configure('blacklist', background='#ffcccc')
        self.results_tree.tag_configure('suspicious', background='#ffffcc')
        
    def on_search(self, event):
        """Handle search input"""
        self.update_results()
        
    def show_plate_details(self, event):
        """Show detailed information for selected plate"""
        selection = self.results_tree.selection()
        if not selection:
            return
            
        item = self.results_tree.item(selection[0])
        plate_text = item['values'][0]
        
        # Create details window
        details_window = tk.Toplevel(self.root)
        details_window.title(f"Plate Details: {plate_text}")
        details_window.geometry("800x600")
        
        # Query detailed information
        with self.db.db_lock:
            cursor = self.db.conn.cursor()
            cursor.execute('''
                SELECT * FROM recognized_plates WHERE plate_text_canonical = ?
            ''', (plate_text,))
            
            plate_info = cursor.fetchone()
        
        # Create notebook for tabs
        notebook = ttk.Notebook(details_window)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Info tab
        info_frame = ttk.Frame(notebook)
        notebook.add(info_frame, text="Information")
        
        # Create info text
        info_text = scrolledtext.ScrolledText(info_frame, wrap=tk.WORD)
        info_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Add information
        info_text.insert('end', f"Plate: {plate_text}\n")
        info_text.insert('end', f"First seen: {plate_info[1]}\n")
        info_text.insert('end', f"Last seen: {plate_info[2]}\n")
        info_text.insert('end', f"Detection count: {plate_info[3]}\n")
        info_text.insert('end', f"Country: {plate_info[4]}\n")
        info_text.insert('end', f"Highest confidence: {plate_info[5]}%\n")
        info_text.insert('end', f"Suspicious: {'Yes' if plate_info[6] else 'No'}\n")
        info_text.insert('end', f"Blacklisted: {'Yes' if plate_info[7] else 'No'}\n")
        
        # Show all detections
        info_text.insert('end', "\n\nAll detections:\n")
        with self.db.db_lock:
            cursor.execute('''
                SELECT raw_detected_text, detection_ts, confidence
                FROM original_detections
                WHERE canonical_plate_text_ref = ?
                ORDER BY detection_ts DESC
                LIMIT 50
            ''', (plate_text,))
            
            detections = cursor.fetchall()
        
        for detection in detections:
            info_text.insert('end', f"  {detection[1]}: {detection[0]} ({detection[2]}%)\n")
            
        info_text.config(state='disabled')
        
        # Images tab
        images_frame = ttk.Frame(notebook)
        notebook.add(images_frame, text="Images")
        
        if plate_info[8]:  # last_detection_image_path
            try:
                image = Image.open(plate_info[8])
                image.thumbnail((600, 400), Image.Resampling.LANCZOS)
                photo = ImageTk.PhotoImage(image)
                
                image_label = ttk.Label(images_frame, image=photo)
                image_label.image = photo
                image_label.pack(pady=10)
                
                # Освобождаем изображение при закрытии окна
                def cleanup():
                    if hasattr(image_label, 'image'):
                        del image_label.image
                    image.close()
                
                details_window.protocol("WM_DELETE_WINDOW", lambda: [cleanup(), details_window.destroy()])
                
                # Add plate text
                ttk.Label(images_frame, text=f"Plate: {plate_text}").pack()
            except Exception as e:
                ttk.Label(images_frame, text=f"Error loading image: {e}").pack()
        else:
            ttk.Label(images_frame, text="No image available").pack()
            
    def show_settings_dialog(self):
        """Show comprehensive settings dialog"""
        settings_window = tk.Toplevel(self.root)
        settings_window.title("System Settings")
        settings_window.geometry("600x500")
        
        # Create notebook for settings categories
        notebook = ttk.Notebook(settings_window)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        # Camera settings tab
        camera_frame = ttk.Frame(notebook)
        notebook.add(camera_frame, text="Camera")
        
        ttk.Label(camera_frame, text="Camera Index:").grid(row=0, column=0, padx=10, pady=5, sticky='w')
        camera_var = tk.IntVar(value=CONFIG['camera_index'])
        camera_spin = ttk.Spinbox(camera_frame, from_=0, to=10, textvariable=camera_var)
        camera_spin.grid(row=0, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(camera_frame, text="Resolution:").grid(row=1, column=0, padx=10, pady=5, sticky='w')
        res_var = tk.StringVar(value=f"{CONFIG['camera_width']}x{CONFIG['camera_height']}")
        res_combo = ttk.Combobox(camera_frame, textvariable=res_var,
                                values=['640x480', '1280x720', '1920x1080'])
        res_combo.grid(row=1, column=1, padx=10, pady=5, sticky='ew')
        
        # LPR settings tab
        lpr_frame = ttk.Frame(notebook)
        notebook.add(lpr_frame, text="LPR")
        
        ttk.Label(lpr_frame, text="Min Plate Width:").grid(row=0, column=0, padx=10, pady=5, sticky='w')
        min_width_var = tk.IntVar(value=CONFIG['min_plate_width'])
        ttk.Spinbox(lpr_frame, from_=10, to=200, textvariable=min_width_var).grid(row=0, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(lpr_frame, text="Max Plate Width:").grid(row=1, column=0, padx=10, pady=5, sticky='w')
        max_width_var = tk.IntVar(value=CONFIG['max_plate_width'])
        ttk.Spinbox(lpr_frame, from_=100, to=800, textvariable=max_width_var).grid(row=1, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(lpr_frame, text="Countries:").grid(row=2, column=0, padx=10, pady=5, sticky='w')
        countries_var = tk.StringVar(value=CONFIG['countries'])
        ttk.Entry(lpr_frame, textvariable=countries_var).grid(row=2, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(lpr_frame, text="FPS Limit:").grid(row=3, column=0, padx=10, pady=5, sticky='w')
        fps_var = tk.IntVar(value=CONFIG['fps_limit'])
        ttk.Spinbox(lpr_frame, from_=1, to=60, textvariable=fps_var).grid(row=3, column=1, padx=10, pady=5, sticky='ew')
        
        # Alert settings tab
        alert_frame = ttk.Frame(notebook)
        notebook.add(alert_frame, text="Alerts")
        
        ttk.Label(alert_frame, text="Suspicious Duration (min):").grid(row=0, column=0, padx=10, pady=5, sticky='w')
        duration_var = tk.IntVar(value=CONFIG['suspicious_duration_minutes'])
        ttk.Spinbox(alert_frame, from_=1, to=60, textvariable=duration_var).grid(row=0, column=1, padx=10, pady=5, sticky='ew')
        
        telegram_var = tk.BooleanVar(value=CONFIG['telegram_enabled'])
        ttk.Checkbutton(alert_frame, text="Enable Telegram Notifications", 
                       variable=telegram_var).grid(row=1, column=0, columnspan=2, padx=10, pady=5, sticky='w')
        
        images_var = tk.BooleanVar(value=CONFIG['save_images'])
        ttk.Checkbutton(alert_frame, text="Save Detection Images", 
                       variable=images_var).grid(row=2, column=0, columnspan=2, padx=10, pady=5, sticky='w')
        
        ttk.Label(alert_frame, text="Image Quality:").grid(row=3, column=0, padx=10, pady=5, sticky='w')
        quality_var = tk.IntVar(value=CONFIG['image_quality'])
        ttk.Scale(alert_frame, from_=50, to=100, orient=tk.HORIZONTAL, variable=quality_var).grid(row=3, column=1, padx=10, pady=5, sticky='ew')
        
        # Preprocessing tab
        prep_frame = ttk.Frame(notebook)
        notebook.add(prep_frame, text="Preprocessing")
        
        ttk.Label(prep_frame, text="Contrast:").grid(row=0, column=0, padx=10, pady=5, sticky='w')
        contrast_var = tk.DoubleVar(value=CONFIG['preprocessing']['contrast'])
        ttk.Scale(prep_frame, from_=0.5, to=2.0, orient=tk.HORIZONTAL, variable=contrast_var).grid(row=0, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(prep_frame, text="Brightness:").grid(row=1, column=0, padx=10, pady=5, sticky='w')
        brightness_var = tk.DoubleVar(value=CONFIG['preprocessing']['brightness'])
        ttk.Scale(prep_frame, from_=0.5, to=2.0, orient=tk.HORIZONTAL, variable=brightness_var).grid(row=1, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(prep_frame, text="Sharpness:").grid(row=2, column=0, padx=10, pady=5, sticky='w')
        sharpness_var = tk.DoubleVar(value=CONFIG['preprocessing']['sharpness'])
        ttk.Scale(prep_frame, from_=0.5, to=3.0, orient=tk.HORIZONTAL, variable=sharpness_var).grid(row=2, column=1, padx=10, pady=5, sticky='ew')
        
        # Plate validation tab
        valid_frame = ttk.Frame(notebook)
        notebook.add(valid_frame, text="Validation")
        
        ttk.Label(valid_frame, text="Min Length:").grid(row=0, column=0, padx=10, pady=5, sticky='w')
        min_len_var = tk.IntVar(value=CONFIG['plate_validation']['min_length'])
        ttk.Spinbox(valid_frame, from_=3, to=15, textvariable=min_len_var).grid(row=0, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(valid_frame, text="Max Length:").grid(row=1, column=0, padx=10, pady=5, sticky='w')
        max_len_var = tk.IntVar(value=CONFIG['plate_validation']['max_length'])
        ttk.Spinbox(valid_frame, from_=5, to=20, textvariable=max_len_var).grid(row=1, column=1, padx=10, pady=5, sticky='ew')
        
        ttk.Label(valid_frame, text="Allowed Characters:").grid(row=2, column=0, padx=10, pady=5, sticky='w')
        chars_var = tk.StringVar(value=CONFIG['plate_validation']['allowed_chars'])
        ttk.Entry(valid_frame, textvariable=chars_var).grid(row=2, column=1, padx=10, pady=5, sticky='ew')
        
        # Save button
        def save_settings():
            CONFIG['camera_index'] = camera_var.get()
            
            res = res_var.get().split('x')
            CONFIG['camera_width'] = int(res[0])
            CONFIG['camera_height'] = int(res[1])
            
            CONFIG['min_plate_width'] = min_width_var.get()
            CONFIG['max_plate_width'] = max_width_var.get()
            CONFIG['countries'] = countries_var.get()
            CONFIG['fps_limit'] = fps_var.get()
            
            CONFIG['suspicious_duration_minutes'] = duration_var.get()
            CONFIG['telegram_enabled'] = telegram_var.get()
            CONFIG['save_images'] = images_var.get()
            CONFIG['image_quality'] = quality_var.get()
            
            CONFIG['preprocessing']['contrast'] = contrast_var.get()
            CONFIG['preprocessing']['brightness'] = brightness_var.get()
            CONFIG['preprocessing']['sharpness'] = sharpness_var.get()
            
            CONFIG['plate_validation']['min_length'] = min_len_var.get()
            CONFIG['plate_validation']['max_length'] = max_len_var.get()
            CONFIG['plate_validation']['allowed_chars'] = chars_var.get()
            
            self.telegram.enabled = CONFIG['telegram_enabled']
            
            self.db.save_settings()
            messagebox.showinfo("Success", "Settings saved. Restart may be required for some changes.")
            settings_window.destroy()
            
        ttk.Button(settings_window, text="Save Settings", 
                  command=save_settings).pack(pady=10)
        
    def export_report(self):
        """Export detection report"""
        file_path = filedialog.asksaveasfilename(
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("Excel files", "*.xlsx"), ("All files", "*.*")]
        )
        
        if not file_path:
            return
            
        try:
            with self.db.db_lock:
                cursor = self.db.conn.cursor()
                cursor.execute('''
                    SELECT plate_text_canonical, first_appearance_ts, last_appearance_ts,
                           detection_count, country_code, highest_confidence_achieved,
                           is_suspiciously_present, is_blacklisted
                    FROM recognized_plates
                    ORDER BY last_appearance_ts DESC
                ''')
                rows = cursor.fetchall()
            
            if file_path.endswith('.csv'):
                import csv
                with open(file_path, 'w', newline='', encoding='utf-8') as csvfile:
                    writer = csv.writer(csvfile)
                    writer.writerow(['Plate', 'First Seen', 'Last Seen', 'Count', 
                                   'Country', 'Max Confidence', 'Suspicious', 'Blacklisted'])
                    
                    for row in rows:
                        writer.writerow(row)
            else:
                try:
                    from openpyxl import Workbook
                    wb = Workbook()
                    ws = wb.active
                    ws.append(['Plate', 'First Seen', 'Last Seen', 'Count', 
                              'Country', 'Max Confidence', 'Suspicious', 'Blacklisted'])
                    
                    for row in rows:
                        ws.append(row)
                    
                    wb.save(file_path)
                except ImportError:
                    messagebox.showerror("Import Error", "openpyxl is not installed. Please install it to export Excel files.")
                    return
                    
            messagebox.showinfo("Success", f"Report exported to {file_path}")
            
        except Exception as e:
            messagebox.showerror("Export Error", str(e))
            
    def on_closing(self):
        """Handle application closing"""
        if messagebox.askokcancel("Quit", "Do you want to quit?"):
            stop_flag.set()
            # Дать потокам время завершиться
            time.sleep(0.5)
            if self.video_capture:
                try:
                    self.video_capture.StopCapture()
                except Exception as e:
                    logger.error(f"Error stopping video capture: {e}")
            try:
                self.db.close()
            except Exception as e:
                logger.error(f"Error closing DB: {e}")
            self.root.destroy()
            
def main():
    root = tk.Tk()
    app = LPRApp(root)
    
    # Handle window closing
    root.protocol("WM_DELETE_WINDOW", app.on_closing)
    
    # Start main loop
    root.mainloop()

if __name__ == "__main__":
    main()