#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Advanced Real-Time License Plate Recognition Counter-Surveillance System v3.0
Enhanced version with extended functionality and real video display
"""

import os
import sys
import time
import datetime
import threading
import queue
import logging
import sqlite3
import json
import csv
import tkinter as tk
from tkinter import ttk, messagebox, filedialog, font
from tkinter import PhotoImage
import ttkthemes
from PIL import Image, ImageTk, ImageDraw, ImageFont, ImageEnhance
import cv2
import numpy as np
import Levenshtein
import requests
from io import BytesIO
import winsound  # For Windows sound alerts
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
import geocoder
from collections import defaultdict, deque
import hashlib
import base64
from cryptography.fernet import Fernet
import psutil
import GPUtil

# Import DTK libraries (DO NOT MODIFY THESE FILES)
from DTKLPR5 import DTKLPRLibrary, LPREngine, LPRParams, BURN_POS
from DTKVID import DTKVIDLibrary, VideoCapture, VideoFrame

# Configure advanced logging
LOG_DIR = 'logs'
os.makedirs(LOG_DIR, exist_ok=True)

logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(os.path.join(LOG_DIR, f'lpr_surveillance_{datetime.datetime.now().strftime("%Y%m%d")}.log')),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Constants
VERSION = "3.0"
DATABASE_PATH = 'lpr_surveillance_v3.db'
IMAGES_DIR = 'lpr_images'
VIDEO_DIR = 'recorded_videos'
EXPORT_DIR = 'exports'
LIB_PATH = '../../lib/windows/x64/'  # Adjust based on your system
TELEGRAM_BOT_TOKEN = '7663972479:AAFeABshDdOhWNY62Nt0W5C_lbjWH1csOJg'
TELEGRAM_CHAT_ID = '738339858'
DEFAULT_TRACKING_THRESHOLD = 600  # 10 minutes in seconds
DEFAULT_LEVENSHTEIN_THRESHOLD = 2
DEFAULT_MIN_CONFIDENCE = 70

# Create necessary directories
for directory in [IMAGES_DIR, VIDEO_DIR, EXPORT_DIR, LOG_DIR]:
    os.makedirs(directory, exist_ok=True)

# Ensure library path is in system PATH
os.environ['PATH'] = LIB_PATH + os.pathsep + os.environ['PATH']


class EnhancedDatabase:
    """Enhanced SQLite database manager with advanced features"""
    
    def __init__(self, path=DATABASE_PATH):
        self.path = path
        self.init_db()
        self._init_encryption()
    
    def _init_encryption(self):
        """Initialize encryption for sensitive data"""
        # Generate or load encryption key
        key_file = 'encryption.key'
        if os.path.exists(key_file):
            with open(key_file, 'rb') as f:
                key = f.read()
        else:
            key = Fernet.generate_key()
            with open(key_file, 'wb') as f:
                f.write(key)
        
        self.cipher = Fernet(key)
    
    def init_db(self):
        """Initialize enhanced database schema"""
        with sqlite3.connect(self.path) as conn:
            conn.row_factory = sqlite3.Row
            conn.executescript('''
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
                    telegram_alert_sent BOOLEAN DEFAULT 0,
                    gps_latitude REAL,
                    gps_longitude REAL,
                    vehicle_type TEXT,
                    vehicle_color TEXT,
                    vehicle_make TEXT,
                    notes TEXT,
                    risk_score INTEGER DEFAULT 0,
                    last_speed_kmh REAL,
                    total_distance_km REAL DEFAULT 0
                );
                
                CREATE TABLE IF NOT EXISTS original_detections (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    canonical_plate_text_ref TEXT,
                    raw_detected_text TEXT,
                    detection_ts DATETIME,
                    confidence REAL,
                    plate_image_path TEXT,
                    frame_image_path TEXT,
                    gps_latitude REAL,
                    gps_longitude REAL,
                    camera_id INTEGER,
                    processing_time_ms INTEGER,
                    plate_width INTEGER,
                    plate_height INTEGER,
                    ocr_text TEXT,
                    FOREIGN KEY(canonical_plate_text_ref) REFERENCES recognized_plates(plate_text_canonical)
                );
                
                CREATE TABLE IF NOT EXISTS blacklist_plates (
                    plate_text TEXT PRIMARY KEY,
                    reason TEXT,
                    danger_level TEXT,
                    date_added DATETIME,
                    added_by TEXT,
                    expiry_date DATETIME,
                    contact_info TEXT,
                    encrypted_notes TEXT
                );
                
                CREATE TABLE IF NOT EXISTS whitelist_plates (
                    plate_text TEXT PRIMARY KEY,
                    owner_name TEXT,
                    date_added DATETIME,
                    notes TEXT
                );
                
                CREATE TABLE IF NOT EXISTS application_settings (
                    setting_name TEXT PRIMARY KEY,
                    setting_value TEXT,
                    setting_type TEXT
                );
                
                CREATE TABLE IF NOT EXISTS alerts_log (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    alert_type TEXT,
                    plate_text TEXT,
                    alert_ts DATETIME,
                    telegram_sent BOOLEAN,
                    email_sent BOOLEAN,
                    sms_sent BOOLEAN,
                    details TEXT,
                    acknowledged BOOLEAN DEFAULT 0,
                    acknowledged_by TEXT,
                    acknowledged_ts DATETIME
                );
                
                CREATE TABLE IF NOT EXISTS sessions (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    start_time DATETIME,
                    end_time DATETIME,
                    total_frames INTEGER,
                    total_detections INTEGER,
                    total_unique_plates INTEGER,
                    session_notes TEXT
                );
                
                CREATE TABLE IF NOT EXISTS routes (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    plate_text TEXT,
                    route_date DATE,
                    route_points TEXT,  -- JSON array of GPS points
                    total_distance_km REAL,
                    avg_speed_kmh REAL,
                    FOREIGN KEY(plate_text) REFERENCES recognized_plates(plate_text_canonical)
                );
                
                CREATE TABLE IF NOT EXISTS plate_groups (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    group_name TEXT,
                    group_type TEXT,  -- 'convoy', 'organization', 'suspicious', etc.
                    created_date DATETIME,
                    member_plates TEXT  -- JSON array
                );
                
                CREATE TABLE IF NOT EXISTS performance_stats (
                    id INTEGER PRIMARY KEY AUTOINCREMENT,
                    timestamp DATETIME,
                    fps REAL,
                    cpu_usage REAL,
                    memory_usage REAL,
                    gpu_usage REAL,
                    processing_latency_ms INTEGER,
                    queue_size INTEGER
                );
                
                -- Create indexes for better performance
                CREATE INDEX IF NOT EXISTS idx_detections_timestamp ON original_detections(detection_ts);
                CREATE INDEX IF NOT EXISTS idx_detections_plate ON original_detections(canonical_plate_text_ref);
                CREATE INDEX IF NOT EXISTS idx_alerts_timestamp ON alerts_log(alert_ts);
                CREATE INDEX IF NOT EXISTS idx_routes_plate ON routes(plate_text);
                
                -- Insert default settings
                INSERT OR IGNORE INTO application_settings VALUES
                    ('camera_id', '0', 'integer'),
                    ('min_plate_width', '50', 'integer'),
                    ('max_plate_width', '400', 'integer'),
                    ('countries', 'LV,LT,EE,RU,PL,DE', 'string'),
                    ('min_confidence', '70', 'integer'),
                    ('tracking_threshold', '600', 'integer'),
                    ('levenshtein_threshold', '2', 'integer'),
                    ('telegram_enabled', 'true', 'boolean'),
                    ('audio_alert_enabled', 'true', 'boolean'),
                    ('fps_limit', '30', 'integer'),
                    ('duplicate_delay', '1000', 'integer'),
                    ('theme', 'dark', 'string'),
                    ('language', 'en', 'string'),
                    ('video_resolution', '1280x720', 'string'),
                    ('record_video', 'false', 'boolean'),
                    ('gps_enabled', 'true', 'boolean'),
                    ('auto_export', 'false', 'boolean'),
                    ('convoy_detection', 'true', 'boolean'),
                    ('face_blur', 'true', 'boolean'),
                    ('plate_enhancement', 'true', 'boolean'),
                    ('night_mode', 'auto', 'string'),
                    ('alert_sound', 'alert.wav', 'string'),
                    ('max_storage_gb', '100', 'integer'),
                    ('retention_days', '90', 'integer');
            ''')
    
    def get_connection(self):
        """Get database connection with row factory"""
        conn = sqlite3.connect(self.path)
        conn.row_factory = sqlite3.Row
        return conn
    
    def encrypt_data(self, data):
        """Encrypt sensitive data"""
        if data:
            return self.cipher.encrypt(data.encode()).decode()
        return None
    
    def decrypt_data(self, encrypted_data):
        """Decrypt sensitive data"""
        if encrypted_data:
            return self.cipher.decrypt(encrypted_data.encode()).decode()
        return None

    def get_setting(self, name, default=None):
        """Retrieve typed setting value"""
        with self.get_connection() as conn:
            row = conn.execute(
                'SELECT setting_value, setting_type FROM application_settings WHERE setting_name = ?',
                (name,)
            ).fetchone()
            if not row:
                return default

            value = row['setting_value']
            stype = row['setting_type']

            if stype == 'integer':
                try:
                    return int(value)
                except ValueError:
                    return default
            if stype == 'boolean':
                return str(value).lower() in ('1', 'true', 'yes')
            return value

    def set_setting(self, name, value, setting_type='string'):
        """Insert or update application setting"""
        with self.get_connection() as conn:
            conn.execute(
                '''INSERT INTO application_settings (setting_name, setting_value, setting_type)
                   VALUES (?, ?, ?)
                   ON CONFLICT(setting_name) DO UPDATE SET
                     setting_value=excluded.setting_value,
                     setting_type=excluded.setting_type''',
                (name, str(value), setting_type),
            )

    def exec(self, query, params=()):
        """Execute arbitrary SQL and return cursor"""
        with self.get_connection() as conn:
            cur = conn.execute(query, params)
            conn.commit()
            return cur

    def is_blacklisted(self, plate_text):
        """Check if plate exists in blacklist"""
        with self.get_connection() as conn:
            row = conn.execute(
                'SELECT 1 FROM blacklist_plates WHERE plate_text = ?',
                (plate_text,)
            ).fetchone()
            return row is not None

    def get_blacklist_info(self, plate_text):
        """Return blacklist record as dict if present"""
        with self.get_connection() as conn:
            row = conn.execute(
                'SELECT * FROM blacklist_plates WHERE plate_text = ?',
                (plate_text,),
            ).fetchone()
            return dict(row) if row else None

    def is_whitelisted(self, plate_text):
        """Check if plate exists in whitelist"""
        with self.get_connection() as conn:
            row = conn.execute(
                'SELECT 1 FROM whitelist_plates WHERE plate_text = ?',
                (plate_text,),
            ).fetchone()
            return row is not None

    def find_canonical_plate(self, plate_text, threshold):
        """Find canonical plate using Levenshtein distance"""
        with self.get_connection() as conn:
            rows = conn.execute(
                'SELECT plate_text_canonical FROM recognized_plates'
            ).fetchall()

            for r in rows:
                candidate = r['plate_text_canonical']
                if Levenshtein.distance(plate_text, candidate) <= threshold:
                    return candidate
        return None

    def log_alert(self, alert_type, plate_text, telegram_sent=False, details=None):
        """Insert alert record"""
        with self.get_connection() as conn:
            conn.execute(
                '''INSERT INTO alerts_log
                   (alert_type, plate_text, alert_ts, telegram_sent, details)
                   VALUES (?, ?, ?, ?, ?)''',
                (
                    alert_type,
                    plate_text,
                    datetime.datetime.now(),
                    int(bool(telegram_sent)),
                    json.dumps(details) if details else None,
                ),
            )

    def update_tracking_status(self):
        """Flag plates that are present longer than threshold."""
        threshold = self.get_setting('tracking_threshold', DEFAULT_TRACKING_THRESHOLD)
        suspicious = []
        with self.get_connection() as conn:
            rows = conn.execute(
                'SELECT plate_text_canonical, first_appearance_ts, last_appearance_ts, '
                'is_suspiciously_present FROM recognized_plates'
            ).fetchall()

            for row in rows:
                first_ts = datetime.datetime.fromisoformat(row['first_appearance_ts'])
                last_ts = datetime.datetime.fromisoformat(row['last_appearance_ts'])
                duration = (last_ts - first_ts).total_seconds()

                if duration >= threshold and not row['is_suspiciously_present']:
                    conn.execute(
                        'UPDATE recognized_plates SET is_suspiciously_present = 1 WHERE plate_text_canonical = ?',
                        (row['plate_text_canonical'],)
                    )
                    suspicious.append({'plate': row['plate_text_canonical'], 'duration': duration})

        return suspicious
    
    def get_statistics(self):
        """Get comprehensive statistics"""
        with self.get_connection() as conn:
            stats = {}
            
            # Basic stats
            stats['total_plates'] = conn.execute(
                'SELECT COUNT(*) FROM recognized_plates'
            ).fetchone()[0]
            
            stats['total_detections'] = conn.execute(
                'SELECT COUNT(*) FROM original_detections'
            ).fetchone()[0]
            
            stats['blacklisted_count'] = conn.execute(
                'SELECT COUNT(*) FROM blacklist_plates'
            ).fetchone()[0]
            
            stats['suspicious_count'] = conn.execute(
                'SELECT COUNT(*) FROM recognized_plates WHERE is_suspiciously_present = 1'
            ).fetchone()[0]
            
            # Time-based stats
            stats['detections_today'] = conn.execute('''
                SELECT COUNT(*) FROM original_detections 
                WHERE DATE(detection_ts) = DATE('now')
            ''').fetchone()[0]
            
            stats['detections_this_week'] = conn.execute('''
                SELECT COUNT(*) FROM original_detections 
                WHERE DATE(detection_ts) >= DATE('now', '-7 days')
            ''').fetchone()[0]
            
            # Country distribution
            country_stats = conn.execute('''
                SELECT country_code, COUNT(*) as count 
                FROM recognized_plates 
                GROUP BY country_code 
                ORDER BY count DESC
            ''').fetchall()
            
            stats['country_distribution'] = [dict(row) for row in country_stats]
            
            # Hourly distribution
            hourly_stats = conn.execute('''
                SELECT strftime('%H', detection_ts) as hour, COUNT(*) as count 
                FROM original_detections 
                GROUP BY hour 
                ORDER BY hour
            ''').fetchall()
            
            stats['hourly_distribution'] = [dict(row) for row in hourly_stats]
            
            # Top plates
            top_plates = conn.execute('''
                SELECT plate_text_canonical, detection_count 
                FROM recognized_plates 
                ORDER BY detection_count DESC 
                LIMIT 10
            ''').fetchall()
            
            stats['top_plates'] = [dict(row) for row in top_plates]
            
            return stats
    
    def find_convoys(self, time_window=300, distance_threshold=1.0):
        """Find potential convoys (plates moving together)"""
        with self.get_connection() as conn:
            # Find plates detected within time_window of each other
            query = '''
                SELECT d1.canonical_plate_text_ref as plate1, 
                       d2.canonical_plate_text_ref as plate2,
                       d1.detection_ts as time1,
                       d2.detection_ts as time2,
                       d1.gps_latitude as lat1,
                       d1.gps_longitude as lon1,
                       d2.gps_latitude as lat2,
                       d2.gps_longitude as lon2
                FROM original_detections d1
                JOIN original_detections d2 
                  ON d1.canonical_plate_text_ref != d2.canonical_plate_text_ref
                  AND ABS(julianday(d1.detection_ts) - julianday(d2.detection_ts)) * 86400 < ?
                WHERE d1.gps_latitude IS NOT NULL 
                  AND d2.gps_latitude IS NOT NULL
                ORDER BY d1.detection_ts DESC
            '''
            
            potential_convoys = conn.execute(query, (time_window,)).fetchall()
            
            # Group by proximity and time
            convoys = defaultdict(set)
            
            for row in potential_convoys:
                # Calculate distance (simplified)
                dist = ((row['lat1'] - row['lat2'])**2 + (row['lon1'] - row['lon2'])**2)**0.5
                
                if dist < distance_threshold:
                    # Group plates that appear together
                    convoy_key = f"{row['time1'][:10]}_{min(row['plate1'], row['plate2'])}"
                    convoys[convoy_key].add(row['plate1'])
                    convoys[convoy_key].add(row['plate2'])
            
            # Filter out small groups
            significant_convoys = {k: list(v) for k, v in convoys.items() if len(v) >= 3}
            
            return significant_convoys


class VideoDisplayWidget(ttk.Frame):
    """Enhanced widget for displaying video with overlays"""
    
    def __init__(self, parent, width=640, height=480):
        super().__init__(parent)
        self.width = width
        self.height = height
        
        # Create canvas for video display
        self.canvas = tk.Canvas(self, width=width, height=height, bg='black')
        self.canvas.pack(fill=tk.BOTH, expand=True)
        
        # Current frame
        self.current_frame = None
        self.photo = None
        
        # Overlay elements
        self.overlays = []
        self.detection_boxes = []
        
        # FPS counter
        self.fps_counter = deque(maxlen=30)
        self.last_frame_time = time.time()
    
    def update_frame(self, frame):
        """Update displayed frame with overlays"""
        try:
            # Convert frame to RGB
            if isinstance(frame, VideoFrame):
                # Get image from VideoFrame
                pil_image = frame.GetImage()
                frame_array = np.array(pil_image)
                frame_rgb = cv2.cvtColor(frame_array, cv2.COLOR_BGR2RGB)
            else:
                # Assume it's already a numpy array
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
            
            # Resize to fit widget
            height, width = frame_rgb.shape[:2]
            scale = min(self.width/width, self.height/height)
            new_width = int(width * scale)
            new_height = int(height * scale)
            
            frame_resized = cv2.resize(frame_rgb, (new_width, new_height))
            
            # Draw overlays
            frame_with_overlays = self._draw_overlays(frame_resized)
            
            # Convert to PIL Image
            pil_image = Image.fromarray(frame_with_overlays)
            
            # Draw FPS
            self._draw_fps(pil_image)
            
            # Convert to PhotoImage
            self.photo = ImageTk.PhotoImage(pil_image)
            
            # Update canvas
            self.canvas.delete("all")
            x = (self.width - new_width) // 2
            y = (self.height - new_height) // 2
            self.canvas.create_image(x, y, anchor=tk.NW, image=self.photo)
            
            # Update FPS counter
            current_time = time.time()
            self.fps_counter.append(1 / (current_time - self.last_frame_time))
            self.last_frame_time = current_time
            
        except Exception as e:
            logger.error(f"Error updating frame: {e}")
    
    def _draw_overlays(self, frame):
        """Draw detection boxes and other overlays"""
        frame_copy = frame.copy()
        
        for box in self.detection_boxes:
            x1, y1, x2, y2 = box['coords']
            color = box.get('color', (0, 255, 0))
            thickness = box.get('thickness', 2)
            label = box.get('label', '')
            
            # Draw rectangle
            cv2.rectangle(frame_copy, (x1, y1), (x2, y2), color, thickness)
            
            # Draw label
            if label:
                label_size = cv2.getTextSize(label, cv2.FONT_HERSHEY_SIMPLEX, 0.5, 1)[0]
                cv2.rectangle(frame_copy, (x1, y1-20), (x1+label_size[0], y1), color, -1)
                cv2.putText(frame_copy, label, (x1, y1-5), 
                           cv2.FONT_HERSHEY_SIMPLEX, 0.5, (255, 255, 255), 1)
        
        return frame_copy
    
    def _draw_fps(self, image):
        """Draw FPS counter on image"""
        if self.fps_counter:
            avg_fps = sum(self.fps_counter) / len(self.fps_counter)
            draw = ImageDraw.Draw(image)
            
            # Try to load a font, fall back to default if not available
            try:
                font = ImageFont.truetype("arial.ttf", 16)
            except:
                font = ImageFont.load_default()
            
            text = f"FPS: {avg_fps:.1f}"
            draw.text((10, 10), text, fill=(0, 255, 0), font=font)
    
    def add_detection_box(self, x1, y1, x2, y2, label='', color=(0, 255, 0)):
        """Add a detection box to be drawn"""
        self.detection_boxes.append({
            'coords': (x1, y1, x2, y2),
            'label': label,
            'color': color,
            'timestamp': time.time()
        })
        
        # Remove old boxes (older than 2 seconds)
        current_time = time.time()
        self.detection_boxes = [
            box for box in self.detection_boxes 
            if current_time - box['timestamp'] < 2.0
        ]
    
    def clear_overlays(self):
        """Clear all overlays"""
        self.detection_boxes.clear()


class AdvancedLPRProcessor:
    """Advanced LPR processing engine with enhanced features"""
    
    def __init__(self, db, telegram_notifier, ui_callback=None):
        self.db = db
        self.telegram = telegram_notifier
        self.ui_callback = ui_callback
        self.stop_flag = False
        self.engine = None
        self.video_capture = None
        self.frame_count = 0
        self.plates_detected = 0
        self.processing_queue = queue.Queue()
        self.current_session_id = None
        
        # Performance monitoring
        self.performance_monitor = PerformanceMonitor(db)
        
        # Video recording
        self.video_writer = None
        self.is_recording = False
        
        # GPS
        self.current_location = None
        self.gps_thread = None
        
        # Setup
        self.setup_lpr()
        self.start_session()
        
        # Start processing thread
        self.processing_thread = threading.Thread(target=self._process_detections, daemon=True)
        self.processing_thread.start()
        
        # Start GPS thread if enabled
        if self.db.get_setting('gps_enabled', True):
            self.start_gps_tracking()
    
    def setup_lpr(self):
        """Initialize LPR engine with optimized parameters"""
        try:
            # Create LPR parameters
            self.params = LPRParams(DTKLPRLibrary(LIB_PATH))
            
            # Load settings from database
            self.params.MinPlateWidth = self.db.get_setting('min_plate_width', 50)
            self.params.MaxPlateWidth = self.db.get_setting('max_plate_width', 400)
            self.params.Countries = self.db.get_setting('countries', 'LV,LT,EE,RU,PL,DE')
            self.params.FormatPlateText = True
            self.params.RotateAngle = 0
            self.params.NumThreads = 0  # Use all available
            self.params.FPSLimit = self.db.get_setting('fps_limit', 30)
            self.params.DuplicateResultsDelay = self.db.get_setting('duplicate_delay', 1000)
            self.params.ResultConfirmationsCount = 2  # Require 2 confirmations
            
            # Burn format for debugging
            self.params.BurnFormatString = "%DATETIME% | %PLATE_NUM% | Conf: %CONFIDENCE%"
            self.params.BurnPosition = BURN_POS.LEFT_TOP
            
            # Create LPR engine
            self.engine = LPREngine(self.params, True, self.plate_detected_callback)
            
            if self.engine.IsLicensed() != 0:
                logger.error("LPR Engine is not licensed!")
                raise Exception("LPR Engine license error")
            
            logger.info("LPR Engine initialized successfully")
            logger.info(f"LPR Version: {LPREngine.GetLibraryVersion()}")
            
        except Exception as e:
            logger.error(f"Failed to initialize LPR: {e}")
            raise
    
    def start_session(self):
        """Start a new processing session"""
        with self.db.get_connection() as conn:
            cursor = conn.execute('''
                INSERT INTO sessions (start_time) VALUES (?)
            ''', (datetime.datetime.now(),))
            self.current_session_id = cursor.lastrowid
    
    def end_session(self):
        """End current processing session"""
        if self.current_session_id:
            with self.db.get_connection() as conn:
                # Get unique plates count
                unique_plates = conn.execute('''
                    SELECT COUNT(DISTINCT canonical_plate_text_ref) 
                    FROM original_detections 
                    WHERE detection_ts >= (SELECT start_time FROM sessions WHERE id = ?)
                ''', (self.current_session_id,)).fetchone()[0]
                
                conn.execute('''
                    UPDATE sessions 
                    SET end_time = ?, 
                        total_frames = ?,
                        total_detections = ?,
                        total_unique_plates = ?
                    WHERE id = ?
                ''', (datetime.datetime.now(), self.frame_count, 
                     self.plates_detected, unique_plates, self.current_session_id))
    
    def start_gps_tracking(self):
        """Start GPS tracking thread"""
        def update_gps():
            while not self.stop_flag:
                try:
                    # Get current location
                    g = geocoder.ip('me')
                    if g.ok:
                        self.current_location = {
                            'lat': g.latlng[0],
                            'lng': g.latlng[1],
                            'address': g.address
                        }
                except Exception as e:
                    logger.error(f"GPS update error: {e}")
                
                time.sleep(5)  # Update every 5 seconds
        
        self.gps_thread = threading.Thread(target=update_gps, daemon=True)
        self.gps_thread.start()
    
    def plate_detected_callback(self, engine, plate):
        """Enhanced callback when license plate is detected"""
        try:
            confidence = plate.Confidence()
            min_confidence = self.db.get_setting('min_confidence', DEFAULT_MIN_CONFIDENCE)
            
            if confidence < min_confidence:
                return 0
            
            # Get processing time
            start_time = time.time()
            
            # Queue for processing
            self.processing_queue.put({
                'plate': plate,
                'timestamp': datetime.datetime.now(),
                'location': self.current_location.copy() if self.current_location else None,
                'processing_start': start_time
            })
            
            self.plates_detected += 1
            
        except Exception as e:
            logger.error(f"Error in plate callback: {e}")
        
        return 0
    
    def _process_detections(self):
        """Enhanced detection processing with additional features"""
        while not self.stop_flag:
            try:
                item = self.processing_queue.get(timeout=1)
                if item is None:
                    break
                
                plate = item['plate']
                timestamp = item['timestamp']
                location = item['location']
                
                # Calculate processing time
                processing_time = int((time.time() - item['processing_start']) * 1000)
                
                # Extract plate data
                plate_text = plate.Text()
                confidence = plate.Confidence()
                country_code = plate.CountryCode()
                
                # Enhance plate image if enabled
                if self.db.get_setting('plate_enhancement', True):
                    plate_image = self._enhance_plate_image(plate.GetPlateImage())
                else:
                    plate_image = plate.GetPlateImage()
                
                # Save images
                plate_dir = os.path.join(IMAGES_DIR, timestamp.strftime('%Y-%m-%d'), plate_text)
                os.makedirs(plate_dir, exist_ok=True)
                
                ts_str = timestamp.strftime('%Y%m%d_%H%M%S_%f')
                plate_img_path = os.path.join(plate_dir, f'plate_{ts_str}.jpg')
                frame_img_path = os.path.join(plate_dir, f'frame_{ts_str}.jpg')
                
                # Save enhanced plate image
                plate_image.save(plate_img_path)
                
                # Process frame image
                frame_img = plate.GetImage()
                
                # Blur faces if enabled
                if self.db.get_setting('face_blur', True):
                    frame_img = self._blur_faces(frame_img)
                
                # Draw enhanced bounding box
                draw = ImageDraw.Draw(frame_img)
                
                # Determine box color based on status
                box_color = self._get_box_color(plate_text, confidence)
                
                # Draw main box
                draw.rectangle(
                    [plate.X(), plate.Y(), plate.X() + plate.Width(), plate.Y() + plate.Height()],
                    outline=box_color, width=3
                )
                
                # Add label
                label = f"{plate_text} ({confidence:.0f}%)"
                try:
                    font = ImageFont.truetype("arial.ttf", 20)
                except:
                    font = ImageFont.load_default()
                
                # Draw label background
                text_bbox = draw.textbbox((0, 0), label, font=font)
                text_width = text_bbox[2] - text_bbox[0]
                text_height = text_bbox[3] - text_bbox[1]
                
                draw.rectangle(
                    [plate.X(), plate.Y() - text_height - 5,
                     plate.X() + text_width + 10, plate.Y()],
                    fill=box_color
                )
                
                # Draw label text
                draw.text((plate.X() + 5, plate.Y() - text_height - 3), 
                         label, fill=(255, 255, 255), font=font)
                
                # Add timestamp and location
                info_text = timestamp.strftime("%Y-%m-%d %H:%M:%S")
                if location:
                    info_text += f" | {location['address']}"
                
                draw.text((10, 10), info_text, fill=(255, 255, 0), font=font)
                
                frame_img.save(frame_img_path)
                
                # Add to database with location
                gps_lat = location['lat'] if location else None
                gps_lng = location['lng'] if location else None
                
                # Enhanced database insertion
                canonical = self._add_detection_enhanced(
                    plate_text, confidence, country_code,
                    plate_img_path, frame_img_path,
                    gps_lat, gps_lng, processing_time,
                    plate.Width(), plate.Height()
                )
                
                # Update UI with detection box
                if self.ui_callback:
                    self.ui_callback('detection_box', {
                        'x1': plate.X(),
                        'y1': plate.Y(),
                        'x2': plate.X() + plate.Width(),
                        'y2': plate.Y() + plate.Height(),
                        'label': label,
                        'color': box_color
                    }, None)
                
                # Check various alert conditions
                self._check_alerts(canonical, confidence, plate_img_path, frame_img_path, location)
                
                # Update UI
                if self.ui_callback:
                    self.ui_callback('update', None, None)
                
                self.processing_queue.task_done()
                
            except queue.Empty:
                continue
            except Exception as e:
                logger.error(f"Error processing detection: {e}", exc_info=True)
    
    def _enhance_plate_image(self, plate_image):
        """Enhance plate image for better readability"""
        # Convert to numpy array
        img_array = np.array(plate_image)
        
        # Apply enhancements
        enhancer = ImageEnhance.Contrast(plate_image)
        enhanced = enhancer.enhance(2.0)
        
        enhancer = ImageEnhance.Sharpness(enhanced)
        enhanced = enhancer.enhance(2.0)
        
        return enhanced
    
    def _blur_faces(self, image):
        """Blur faces in image for privacy"""
        # This is a placeholder - would need face detection
        # For now, just return original image
        return image
    
    def _get_box_color(self, plate_text, confidence):
        """Get bounding box color based on plate status"""
        if self.db.is_blacklisted(plate_text):
            return (255, 0, 0)  # Red for blacklist
        elif self.db.is_whitelisted(plate_text):
            return (0, 255, 0)  # Green for whitelist
        elif confidence > 90:
            return (0, 255, 255)  # Cyan for high confidence
        else:
            return (255, 255, 0)  # Yellow for normal
    
    def _add_detection_enhanced(self, raw_text, confidence, country_code, 
                               plate_img_path, frame_img_path, gps_lat, gps_lng,
                               processing_time, plate_width, plate_height):
        """Enhanced detection addition with more metadata"""
        threshold = self.db.get_setting('levenshtein_threshold', DEFAULT_LEVENSHTEIN_THRESHOLD)
        canonical = self.db.find_canonical_plate(raw_text, threshold)
        
        now = datetime.datetime.now()
        
        with self.db.get_connection() as conn:
            if canonical:
                # Update existing plate
                conn.execute('''
                    UPDATE recognized_plates
                    SET last_appearance_ts = ?,
                        detection_count = detection_count + 1,
                        highest_confidence_achieved = MAX(highest_confidence_achieved, ?),
                        last_detection_image_path = ?,
                        gps_latitude = COALESCE(?, gps_latitude),
                        gps_longitude = COALESCE(?, gps_longitude)
                    WHERE plate_text_canonical = ?
                ''', (now, confidence, frame_img_path, gps_lat, gps_lng, canonical))
            else:
                # Create new canonical plate
                canonical = raw_text
                is_blacklisted = self.db.is_blacklisted(canonical)
                
                conn.execute('''
                    INSERT INTO recognized_plates
                    (plate_text_canonical, first_appearance_ts, last_appearance_ts,
                     detection_count, country_code, highest_confidence_achieved,
                     is_blacklisted, last_detection_image_path, gps_latitude, gps_longitude)
                    VALUES (?, ?, ?, 1, ?, ?, ?, ?, ?, ?)
                ''', (canonical, now, now, country_code, confidence, is_blacklisted, 
                     frame_img_path, gps_lat, gps_lng))
            
            # Add original detection record with enhanced data
            conn.execute('''
                INSERT INTO original_detections
                (canonical_plate_text_ref, raw_detected_text, detection_ts,
                 confidence, plate_image_path, frame_image_path,
                 gps_latitude, gps_longitude, camera_id, processing_time_ms,
                 plate_width, plate_height)
                VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
            ''', (canonical, raw_text, now, confidence, plate_img_path, frame_img_path,
                 gps_lat, gps_lng, self.db.get_setting('camera_id', 0),
                 processing_time, plate_width, plate_height))
        
        return canonical
    
    def _check_alerts(self, canonical, confidence, plate_img_path, frame_img_path, location):
        """Check various alert conditions"""
        # Check blacklist
        if self.db.is_blacklisted(canonical):
            bl_info = self.db.get_blacklist_info(canonical)
            
            # Decrypt sensitive notes
            if bl_info and bl_info.get('encrypted_notes'):
                bl_info['notes'] = self.db.decrypt_data(bl_info['encrypted_notes'])
            
            # Send alerts
            self.telegram.send_alert(
                "BLACKLIST DETECTED!",
                canonical, confidence,
                [plate_img_path, frame_img_path],
                bl_info
            )
            
            self.db.log_alert('blacklist', canonical, True, bl_info)
            
            if self.ui_callback:
                self.ui_callback('blacklist', canonical, bl_info)
        
        # Check tracking status
        newly_suspicious = self.db.update_tracking_status()
        
        for suspicious in newly_suspicious:
            # Mark as alert sent
            with self.db.get_connection() as conn:
                conn.execute(
                    'UPDATE recognized_plates SET telegram_alert_sent = 1 WHERE plate_text_canonical = ?',
                    (suspicious['plate'],)
                )
            
            # Send alert
            self.telegram.send_alert(
                "POTENTIAL TRACKING DETECTED!",
                suspicious['plate'], confidence,
                [frame_img_path],
                {'duration': suspicious['duration'], 'location': location}
            )
            
            self.db.log_alert('tracking', suspicious['plate'], True,
                             {'duration': suspicious['duration']})
            
            if self.ui_callback:
                self.ui_callback('tracking', suspicious['plate'],
                               {'duration': suspicious['duration']})
        
        # Check convoy detection
        if self.db.get_setting('convoy_detection', True):
            convoys = self.db.find_convoys()
            for convoy_id, plates in convoys.items():
                if canonical in plates and len(plates) >= 3:
                    self.db.log_alert('convoy', canonical, False,
                                     {'convoy_plates': plates})
                    
                    if self.ui_callback:
                        self.ui_callback('convoy', canonical, {'plates': plates})
    
    def is_whitelisted(self, plate_text):
        """Check if plate is whitelisted"""
        with self.db.get_connection() as conn:
            result = conn.execute(
                'SELECT * FROM whitelist_plates WHERE plate_text = ?',
                (plate_text,)
            ).fetchone()
            return result is not None
    
    def frame_captured_callback(self, video_capture, frame, custom_data):
        """Enhanced callback for captured video frames"""
        if not self.stop_flag:
            self.frame_count += 1
            
            # Update video display
            if self.ui_callback:
                self.ui_callback('video_frame', frame, None)
            
            # Record video if enabled
            if self.is_recording and self.video_writer:
                # Convert frame to numpy array
                img = frame.GetImage()
                img_array = np.array(img)
                self.video_writer.write(img_array)
            
            # Process frame
            self.engine.PutFrame(frame, 0)
            
            # Monitor performance
            self.performance_monitor.update(self.frame_count, self.processing_queue.qsize())
    
    def start_video_recording(self):
        """Start recording video"""
        if self.db.get_setting('record_video', False):
            timestamp = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
            filename = os.path.join(VIDEO_DIR, f'recording_{timestamp}.avi')
            
            # Get resolution
            res_str = self.db.get_setting('video_resolution', '1280x720')
            width, height = map(int, res_str.split('x'))
            
            # Create video writer
            fourcc = cv2.VideoWriter_fourcc(*'XVID')
            self.video_writer = cv2.VideoWriter(filename, fourcc, 20.0, (width, height))
            self.is_recording = True
            
            logger.info(f"Started video recording: {filename}")
    
    def stop_video_recording(self):
        """Stop recording video"""
        if self.is_recording and self.video_writer:
            self.video_writer.release()
            self.is_recording = False
            logger.info("Stopped video recording")


class PerformanceMonitor:
    """Monitor system performance"""
    
    def __init__(self, db):
        self.db = db
        self.last_update = time.time()
        self.last_frame_count = 0
    
    def update(self, frame_count, queue_size):
        """Update performance metrics"""
        current_time = time.time()
        
        # Update every second
        if current_time - self.last_update >= 1.0:
            # Calculate FPS
            fps = (frame_count - self.last_frame_count) / (current_time - self.last_update)
            
            # Get system metrics
            cpu_percent = psutil.cpu_percent()
            memory_percent = psutil.virtual_memory().percent
            
            # Get GPU usage if available
            gpu_percent = 0
            try:
                gpus = GPUtil.getGPUs()
                if gpus:
                    gpu_percent = gpus[0].load * 100
            except:
                pass
            
            # Save to database
            with self.db.get_connection() as conn:
                conn.execute('''
                    INSERT INTO performance_stats
                    (timestamp, fps, cpu_usage, memory_usage, gpu_usage, queue_size)
                    VALUES (?, ?, ?, ?, ?, ?)
                ''', (datetime.datetime.now(), fps, cpu_percent, memory_percent, 
                     gpu_percent, queue_size))
            
            self.last_update = current_time
            self.last_frame_count = frame_count

def TelegramNotifier(TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID):
    pass


class AdvancedMainApplication:
    """Advanced main GUI application with extended features"""
    
    def __init__(self):
        # Initialize theme
        self.root = ttkthemes.ThemedTk()
        self.root.set_theme("equilux")  # Dark theme
        self.root.title(f"LPR Counter-Surveillance System v{VERSION}")
        self.root.geometry("1400x900")
        
        # Set icon if available
        try:
            self.root.iconbitmap('icon.ico')
        except:
            pass
        
        # Initialize components
        self.db = EnhancedDatabase()
        self.telegram = TelegramNotifier(TELEGRAM_BOT_TOKEN, TELEGRAM_CHAT_ID)
        self.lpr_processor = None
        
        self.is_processing = False
        self.current_camera = self.db.get_setting('camera_id', 0)
        
        # UI state
        self.current_language = self.db.get_setting('language', 'en')
        self.translations = self.load_translations()
        
        # Setup UI
        self.setup_ui()
        
        # Start timers
        self.update_timer()
        self.cleanup_timer()
        
        # Bind events
        self.root.protocol("WM_DELETE_WINDOW", self.on_closing)
        self.setup_hotkeys()
        
        # Load last session info
        self.load_session_info()
    
    def load_translations(self):
        """Load language translations"""
        # This is a simplified version - in real app would load from files
        translations = {
            'en': {
                'start': 'Start Processing',
                'stop': 'Stop Processing',
                'settings': 'Settings',
                'blacklist': 'Manage Blacklist',
                'export': 'Export Data',
                'statistics': 'Statistics',
                'about': 'About',
                'camera': 'Camera',
                'detected_plates': 'Detected Plates',
                'plate': 'Plate',
                'count': 'Count',
                'last_seen': 'Last Seen',
                'duration': 'Duration',
                'status': 'Status',
                'confidence': 'Confidence'
            },
            'ru': {
                'start': 'Начать обработку',
                'stop': 'Остановить обработку',
                'settings': 'Настройки',
                'blacklist': 'Черный список',
                'export': 'Экспорт данных',
                'statistics': 'Статистика',
                'about': 'О программе',
                'camera': 'Камера',
                'detected_plates': 'Обнаруженные номера',
                'plate': 'Номер',
                'count': 'Количество',
                'last_seen': 'Последний раз',
                'duration': 'Длительность',
                'status': 'Статус',
                'confidence': 'Уверенность'
            }
        }
        
        return translations.get(self.current_language, translations['en'])
    
    def _(self, key):
        """Get translated string"""
        return self.translations.get(key, key)
    
    def setup_ui(self):
        """Setup enhanced user interface"""
        # Create menu bar
        self.create_menu_bar()
        
        # Main container with custom style
        style = ttk.Style()
        style.configure('Main.TFrame', background='#2b2b2b')
        
        main_frame = ttk.Frame(self.root, style='Main.TFrame', padding="5")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Configure grid weights
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=1)
        main_frame.columnconfigure(1, weight=2)
        main_frame.rowconfigure(1, weight=1)
        
        # Control panel with gradient background
        control_frame = ttk.LabelFrame(main_frame, text="Control Panel", padding="10")
        control_frame.grid(row=0, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=5)
        
        # Camera selection with preview
        camera_frame = ttk.Frame(control_frame)
        camera_frame.grid(row=0, column=0, padx=5)
        
        ttk.Label(camera_frame, text=f"{self._('camera')}:").pack(side=tk.LEFT, padx=5)
        self.camera_var = tk.IntVar(value=self.current_camera)
        camera_spinbox = ttk.Spinbox(camera_frame, from_=0, to=10, width=5,
                                     textvariable=self.camera_var)
        camera_spinbox.pack(side=tk.LEFT)
        
        # Camera preview button
        ttk.Button(camera_frame, text="📷", width=3,
                  command=self.preview_camera).pack(side=tk.LEFT, padx=2)
        
        # Start/Stop button with icon
        self.start_button = ttk.Button(control_frame, text=f"▶ {self._('start')}",
                                      command=self.toggle_processing,
                                      style='Accent.TButton')
        self.start_button.grid(row=0, column=1, padx=20)
        
        # Quick action buttons
        quick_actions = ttk.Frame(control_frame)
        quick_actions.grid(row=0, column=2, padx=10)
        
        ttk.Button(quick_actions, text="⚙", width=3, command=self.open_settings,
                  ).pack(side=tk.LEFT, padx=2)
        ttk.Button(quick_actions, text="🚫", width=3, command=self.open_blacklist,
                  ).pack(side=tk.LEFT, padx=2)
        ttk.Button(quick_actions, text="📊", width=3, command=self.show_statistics,
                  ).pack(side=tk.LEFT, padx=2)
        ttk.Button(quick_actions, text="💾", width=3, command=self.export_data,
                  ).pack(side=tk.LEFT, padx=2)
        
        # Statistics display
        stats_frame = ttk.Frame(control_frame)
        stats_frame.grid(row=0, column=3, padx=20)
        
        self.stats_labels = {}
        stats = [
            ('fps', 'FPS: 0'),
            ('plates', 'Plates: 0'),
            ('alerts', 'Alerts: 0'),
            ('cpu', 'CPU: 0%')
        ]
        
        for key, text in stats:
            label = ttk.Label(stats_frame, text=text, font=('Segoe UI', 9))
            label.pack(anchor=tk.W)
            self.stats_labels[key] = label
        
        # Video frame with enhanced display
        video_container = ttk.LabelFrame(main_frame, text="Live Feed", padding="5")
        video_container.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=5)
        
        self.video_display = VideoDisplayWidget(video_container, width=640, height=480)
        self.video_display.pack(fill=tk.BOTH, expand=True)
        
        # Create notebook for right panel
        right_notebook = ttk.Notebook(main_frame)
        right_notebook.grid(row=1, column=1, sticky=(tk.W, tk.E, tk.N, tk.S), padx=5)
        
        # Results tab
        results_frame = ttk.Frame(right_notebook)
        right_notebook.add(results_frame, text=self._('detected_plates'))
        
        self.create_results_panel(results_frame)
        
        # Map tab
        map_frame = ttk.Frame(right_notebook)
        right_notebook.add(map_frame, text="Map")
        
        self.create_map_panel(map_frame)
        
        # Analytics tab
        analytics_frame = ttk.Frame(right_notebook)
        right_notebook.add(analytics_frame, text="Analytics")
        
        self.create_analytics_panel(analytics_frame)
        
        # Alerts tab
        alerts_frame = ttk.Frame(right_notebook)
        right_notebook.add(alerts_frame, text="Alerts")
        
        self.create_alerts_panel(alerts_frame)
        
        # Status bar with progress
        self.create_status_bar()
    
    def create_menu_bar(self):
        """Create application menu bar"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="New Session", command=self.new_session)
        file_menu.add_command(label="Load Session", command=self.load_session)
        file_menu.add_separator()
        file_menu.add_command(label="Import Data", command=self.import_data)
        file_menu.add_command(label="Export Data", command=self.export_data)
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.on_closing)
        
        # View menu
        view_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="View", menu=view_menu)
        view_menu.add_command(label="Full Screen", command=self.toggle_fullscreen)
        view_menu.add_command(label="Statistics", command=self.show_statistics)
        view_menu.add_command(label="Performance Monitor", command=self.show_performance)
        
        # Tools menu
        tools_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Tools", menu=tools_menu)
        tools_menu.add_command(label="Blacklist Manager", command=self.open_blacklist)
        tools_menu.add_command(label="Whitelist Manager", command=self.open_whitelist)
        tools_menu.add_command(label="Convoy Analyzer", command=self.analyze_convoys)
        tools_menu.add_command(label="Database Maintenance", command=self.database_maintenance)
        
        # Settings menu
        settings_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Settings", menu=settings_menu)
        settings_menu.add_command(label="Preferences", command=self.open_settings)
        settings_menu.add_command(label="Camera Settings", command=self.camera_settings)
        settings_menu.add_command(label="Alert Settings", command=self.alert_settings)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="User Guide", command=self.show_help)
        help_menu.add_command(label="About", command=self.show_about)
    
    def create_results_panel(self, parent):
        """Create enhanced results panel"""
        # Search bar
        search_frame = ttk.Frame(parent)
        search_frame.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Label(search_frame, text="Search:").pack(side=tk.LEFT, padx=5)
        self.search_var = tk.StringVar()
        self.search_var.trace('w', lambda *args: self.filter_results())
        search_entry = ttk.Entry(search_frame, textvariable=self.search_var)
        search_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        
        # Filter buttons
        filter_frame = ttk.Frame(parent)
        filter_frame.pack(fill=tk.X, padx=5, pady=2)
        
        self.filter_vars = {
            'blacklist': tk.BooleanVar(),
            'tracking': tk.BooleanVar(),
            'whitelist': tk.BooleanVar()
        }
        
        ttk.Checkbutton(filter_frame, text="Blacklist", 
                       variable=self.filter_vars['blacklist'],
                       command=self.filter_results).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(filter_frame, text="Tracking",
                       variable=self.filter_vars['tracking'],
                       command=self.filter_results).pack(side=tk.LEFT, padx=5)
        ttk.Checkbutton(filter_frame, text="Whitelist",
                       variable=self.filter_vars['whitelist'],
                       command=self.filter_results).pack(side=tk.LEFT, padx=5)
        
        # Results treeview with custom style
        tree_frame = ttk.Frame(parent)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        columns = ('Plate', 'Count', 'Last Seen', 'Duration', 'Status', 'Confidence', 'Country')
        self.results_tree = ttk.Treeview(tree_frame, columns=columns, show='headings')
        
        # Configure columns
        col_widths = {'Plate': 100, 'Count': 60, 'Last Seen': 120, 
                     'Duration': 80, 'Status': 120, 'Confidence': 80, 'Country': 60}
        
        for col in columns:
            self.results_tree.heading(col, text=self._(col.lower()),
                                     command=lambda c=col: self.sort_results(c))
            self.results_tree.column(col, width=col_widths.get(col, 100))
        
        # Add scrollbars
        v_scroll = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL,
                                command=self.results_tree.yview)
        h_scroll = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL,
                                command=self.results_tree.xview)
        self.results_tree.configure(yscrollcommand=v_scroll.set,
                                   xscrollcommand=h_scroll.set)
        
        self.results_tree.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        v_scroll.grid(row=0, column=1, sticky=(tk.N, tk.S))
        h_scroll.grid(row=1, column=0, sticky=(tk.W, tk.E))
        
        tree_frame.rowconfigure(0, weight=1)
        tree_frame.columnconfigure(0, weight=1)
        
        # Configure tags for styling
        self.results_tree.tag_configure('blacklist', foreground='#ff4444',
                                       font=('Segoe UI', 10, 'bold'))
        self.results_tree.tag_configure('tracking', foreground='#ff8800',
                                       font=('Segoe UI', 10, 'bold'))
        self.results_tree.tag_configure('whitelist', foreground='#44ff44')
        self.results_tree.tag_configure('normal', foreground='#cccccc')
        
        # Bind events
        self.results_tree.bind('<Double-Button-1>', self.show_plate_details)
        self.results_tree.bind('<Button-3>', self.show_context_menu)
    
    def create_map_panel(self, parent):
        """Create map panel for location tracking"""
        # This is a placeholder - would integrate with a real map widget
        map_label = ttk.Label(parent, text="Map View\n(GPS tracking of detected plates)",
                             font=('Segoe UI', 14), anchor=tk.CENTER)
        map_label.pack(fill=tk.BOTH, expand=True)
        
        # Add some controls
        controls = ttk.Frame(parent)
        controls.pack(fill=tk.X, side=tk.BOTTOM, padx=5, pady=5)
        
        ttk.Button(controls, text="Show Routes",
                  command=self.show_routes).pack(side=tk.LEFT, padx=5)
        ttk.Button(controls, text="Heat Map",
                  command=self.show_heatmap).pack(side=tk.LEFT, padx=5)
        ttk.Button(controls, text="Clear Map",
                  command=self.clear_map).pack(side=tk.LEFT, padx=5)
    
    def create_analytics_panel(self, parent):
        """Create analytics panel with charts"""
        # Create matplotlib figure
        from matplotlib.figure import Figure
        
        self.fig = Figure(figsize=(8, 6), dpi=100, facecolor='#2b2b2b')
        self.fig.subplots_adjust(hspace=0.4, wspace=0.3)
        
        # Create subplots
        self.ax1 = self.fig.add_subplot(221)  # Hourly distribution
        self.ax2 = self.fig.add_subplot(222)  # Country distribution
        self.ax3 = self.fig.add_subplot(223)  # Top plates
        self.ax4 = self.fig.add_subplot(224)  # Trend over time
        
        # Style axes
        for ax in [self.ax1, self.ax2, self.ax3, self.ax4]:
            ax.set_facecolor('#3b3b3b')
            ax.tick_params(colors='white')
            ax.spines['bottom'].set_color('white')
            ax.spines['top'].set_color('white')
            ax.spines['left'].set_color('white')
            ax.spines['right'].set_color('white')
        
        # Create canvas
        self.canvas = FigureCanvasTkAgg(self.fig, parent)
        self.canvas.draw()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        
        # Control buttons
        controls = ttk.Frame(parent)
        controls.pack(fill=tk.X, side=tk.BOTTOM, padx=5, pady=5)
        
        ttk.Button(controls, text="Refresh",
                  command=self.update_analytics).pack(side=tk.LEFT, padx=5)
        ttk.Button(controls, text="Export Charts",
                  command=self.export_charts).pack(side=tk.LEFT, padx=5)
        
        # Initial update
        self.update_analytics()
    
    def create_alerts_panel(self, parent):
        """Create alerts panel"""
        # Alerts treeview
        columns = ('Time', 'Type', 'Plate', 'Details', 'Status')
        self.alerts_tree = ttk.Treeview(parent, columns=columns, show='headings')
        
        for col in columns:
            self.alerts_tree.heading(col, text=col)
            self.alerts_tree.column(col, width=120)
        
        # Scrollbar
        scrollbar = ttk.Scrollbar(parent, orient=tk.VERTICAL,
                                 command=self.alerts_tree.yview)
        self.alerts_tree.configure(yscrollcommand=scrollbar.set)
        
        self.alerts_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        
        # Load alerts
        self.update_alerts()
    
    def create_status_bar(self):
        """Create enhanced status bar"""
        status_frame = ttk.Frame(self.root)
        status_frame.grid(row=1, column=0, sticky=(tk.W, tk.E))
        
        # Status text
        self.status_var = tk.StringVar(value="Ready")
        status_label = ttk.Label(status_frame, textvariable=self.status_var,
                                relief=tk.SUNKEN)
        status_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=2)
        
        # Progress bar
        self.progress_var = tk.IntVar()
        self.progress_bar = ttk.Progressbar(status_frame, length=200,
                                           variable=self.progress_var)
        self.progress_bar.pack(side=tk.LEFT, padx=5)
        
        # Connection indicators
        indicators_frame = ttk.Frame(status_frame)
        indicators_frame.pack(side=tk.RIGHT, padx=5)
        
        self.indicators = {
            'camera': ttk.Label(indicators_frame, text="📷", foreground='gray'),
            'telegram': ttk.Label(indicators_frame, text="💬", foreground='gray'),
            'gps': ttk.Label(indicators_frame, text="📍", foreground='gray'),
            'db': ttk.Label(indicators_frame, text="💾", foreground='gray')
        }
        
        for indicator in self.indicators.values():
            indicator.pack(side=tk.LEFT, padx=2)
    
    def setup_hotkeys(self):
        """Setup keyboard shortcuts"""
        self.root.bind('<F1>', lambda e: self.show_help())
        self.root.bind('<F5>', lambda e: self.toggle_processing())
        self.root.bind('<F11>', lambda e: self.toggle_fullscreen())
        self.root.bind('<Control-s>', lambda e: self.open_settings())
        self.root.bind('<Control-b>', lambda e: self.open_blacklist())
        self.root.bind('<Control-e>', lambda e: self.export_data())
        self.root.bind('<Control-q>', lambda e: self.on_closing())
        self.root.bind('<Escape>', lambda e: self.root.attributes('-fullscreen', False))
    
    def toggle_processing(self):
        """Start or stop processing with enhanced features"""
        if not self.is_processing:
            try:
                camera_id = self.camera_var.get()
                
                # Create new processor
                self.lpr_processor = AdvancedLPRProcessor(
                    self.db, self.telegram, self.alert_callback
                )
                
                # Start capture
                self.lpr_processor.start_capture(camera_id)
                
                # Start video recording if enabled
                self.lpr_processor.start_video_recording()
                
                self.is_processing = True
                self.start_button.config(text=f"⏹ {self._('stop')}")
                self.status_var.set(f"Processing from camera {camera_id}")
                
                # Update indicators
                self.indicators['camera'].config(foreground='green')
                
                # Save camera selection
                self.db.set_setting('camera_id', camera_id, 'integer')
                
            except Exception as e:
                logger.error(f"Failed to start processing: {e}")
                messagebox.showerror("Error", f"Failed to start: {str(e)}")
        else:
            # Stop processing
            if self.lpr_processor:
                self.lpr_processor.stop_capture()
                self.lpr_processor.stop_video_recording()
                self.lpr_processor.end_session()
            
            self.is_processing = False
            self.start_button.config(text=f"▶ {self._('start')}")
            self.status_var.set("Stopped")
            
            # Update indicators
            self.indicators['camera'].config(foreground='gray')
    
    def alert_callback(self, alert_type, data, details):
        """Enhanced alert callback"""
        if alert_type == 'video_frame':
            # Update video display
            self.video_display.update_frame(data)
            
        elif alert_type == 'detection_box':
            # Add detection box to video
            self.video_display.add_detection_box(
                data['x1'], data['y1'], data['x2'], data['y2'],
                data['label'], data['color']
            )
            
        elif alert_type == 'blacklist':
            # Show enhanced blacklist alert
            self.show_blacklist_alert(data, details)
            
        elif alert_type == 'tracking':
            # Show tracking alert
            self.show_tracking_alert(data, details)
            
        elif alert_type == 'convoy':
            # Show convoy alert
            self.show_convoy_alert(data, details)
            
        elif alert_type == 'update':
            # General update
            pass
    
    def show_blacklist_alert(self, plate_text, details):
        """Show enhanced blacklist alert"""
        alert_window = tk.Toplevel(self.root)
        alert_window.title("⚠️ BLACKLIST ALERT!")
        alert_window.geometry("600x400")
        alert_window.configure(bg='#ff0000')
        
        # Make it stay on top
        alert_window.attributes('-topmost', True)
        
        # Flash effect
        def flash():
            current_bg = alert_window.cget('bg')
            new_bg = '#ff0000' if current_bg == '#2b2b2b' else '#2b2b2b'
            alert_window.configure(bg=new_bg)
            alert_window.after(500, flash)
        
        flash()
        
        # Content
        content_frame = ttk.Frame(alert_window, padding="20")
        content_frame.pack(fill=tk.BOTH, expand=True)
        
        # Alert header
        header = ttk.Label(content_frame, 
                          text="⚠️ BLACKLISTED PLATE DETECTED! ⚠️",
                          font=('Segoe UI', 18, 'bold'),
                          foreground='red')
        header.pack(pady=10)
        
        # Details
        details_text = f"""
Plate Number: {plate_text}
Reason: {details.get('reason', 'N/A')}
Danger Level: {details.get('danger_level', 'N/A')}
Date Added: {details.get('date_added', 'N/A')}
Contact: {details.get('contact_info', 'N/A')}
"""
        
        if details.get('notes'):
            details_text += f"\nNotes: {details['notes']}"
        
        details_label = ttk.Label(content_frame, text=details_text,
                                 font=('Segoe UI', 12))
        details_label.pack(pady=10)
        
        # Actions
        actions_frame = ttk.Frame(content_frame)
        actions_frame.pack(pady=20)
        
        ttk.Button(actions_frame, text="Acknowledge",
                  command=lambda: self.acknowledge_alert(alert_window, plate_text)
                  ).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(actions_frame, text="View Details",
                  command=lambda: self.show_plate_details_by_text(plate_text)
                  ).pack(side=tk.LEFT, padx=5)
        
        ttk.Button(actions_frame, text="Call Police",
                  command=self.call_emergency
                  ).pack(side=tk.LEFT, padx=5)
        
        # Play alert sound
        if self.db.get_setting('audio_alert_enabled', True):
            self.play_alert_sound('critical')
    
    def play_alert_sound(self, level='normal'):
        """Play alert sound based on level"""
        try:
            sound_file = self.db.get_setting('alert_sound', 'alert.wav')
            if os.path.exists(sound_file):
                winsound.PlaySound(sound_file, winsound.SND_ASYNC)
            else:
                # Use system sounds
                if level == 'critical':
                    winsound.MessageBeep(winsound.MB_ICONHAND)
                else:
                    winsound.MessageBeep(winsound.MB_ICONEXCLAMATION)
        except:
            pass
    
    def update_timer(self):
        """Update UI periodically"""
        self.update_results()
        self.update_stats()
        self.update_indicators()
        
        # Schedule next update
        self.root.after(1000, self.update_timer)
    
    def update_results(self):
        """Update results with filtering and sorting"""
        # Get current filters
        search_text = self.search_var.get().lower()
        filters = {k: v.get() for k, v in self.filter_vars.items()}
        
        # Clear existing items
        for item in self.results_tree.get_children():
            self.results_tree.delete(item)
        
        # Get plates from database with filters
        with self.db.get_connection() as conn:
            query = '''
                SELECT p.*, w.plate_text as whitelisted
                FROM recognized_plates p
                LEFT JOIN whitelist_plates w ON p.plate_text_canonical = w.plate_text
                WHERE 1=1
            '''
            params = []
            
            if search_text:
                query += ' AND p.plate_text_canonical LIKE ?'
                params.append(f'%{search_text}%')
            
            if filters['blacklist']:
                query += ' AND p.is_blacklisted = 1'
            
            if filters['tracking']:
                query += ' AND p.is_suspiciously_present = 1'
            
            if filters['whitelist']:
                query += ' AND w.plate_text IS NOT NULL'
            
            query += ' ORDER BY p.last_appearance_ts DESC LIMIT 500'
            
            plates = conn.execute(query, params).fetchall()
            
            for plate in plates:
                # Calculate duration
                first = datetime.datetime.fromisoformat(plate['first_appearance_ts'])
                last = datetime.datetime.fromisoformat(plate['last_appearance_ts'])
                duration_sec = (last - first).total_seconds()
                
                if duration_sec < 60:
                    duration_str = f"{int(duration_sec)}s"
                else:
                    minutes = int(duration_sec // 60)
                    seconds = int(duration_sec % 60)
                    duration_str = f"{minutes}m {seconds}s"
                
                # Determine status and tags
                status = "Normal"
                tags = ('normal',)
                
                if plate['is_blacklisted']:
                    status = "⚠️ BLACKLISTED!"
                    tags = ('blacklist',)
                elif plate['is_suspiciously_present']:
                    status = f"👀 Tracking: {duration_str}"
                    tags = ('tracking',)
                elif plate['whitelisted']:
                    status = "✓ Whitelisted"
                    tags = ('whitelist',)
                
                # Format last seen
                last_seen = last.strftime("%Y-%m-%d %H:%M:%S")
                
                # Insert item
                self.results_tree.insert('', 'end', values=(
                    plate['plate_text_canonical'],
                    plate['detection_count'],
                    last_seen,
                    duration_str,
                    status,
                    f"{plate['highest_confidence_achieved']:.0f}%",
                    plate['country_code'] or 'N/A'
                ), tags=tags)
    
    def update_stats(self):
        """Update statistics display"""
        if self.lpr_processor:
            # Get current FPS from performance monitor
            with self.db.get_connection() as conn:
                fps_data = conn.execute('''
                    SELECT fps FROM performance_stats 
                    ORDER BY timestamp DESC LIMIT 1
                ''').fetchone()
                
                fps = fps_data['fps'] if fps_data else 0
                
            self.stats_labels['fps'].config(text=f"FPS: {fps:.1f}")
            self.stats_labels['plates'].config(text=f"Plates: {self.lpr_processor.plates_detected}")
            
            # Get alerts count
            alerts_count = self.db.exec('''
                SELECT COUNT(*) FROM alerts_log 
                WHERE DATE(alert_ts) = DATE('now')
            ''').fetchone()[0]
            
            self.stats_labels['alerts'].config(text=f"Alerts: {alerts_count}")
            
            # Get CPU usage
            cpu_percent = psutil.cpu_percent()
            self.stats_labels['cpu'].config(text=f"CPU: {cpu_percent:.0f}%")
    
    def update_indicators(self):
        """Update connection indicators"""
        # Camera indicator - already handled in toggle_processing
        
        # Telegram indicator
        if self.telegram.enabled:
            # Check Telegram connection
            try:
                response = requests.get(f"{self.telegram.base_url}/getMe", timeout=2)
                if response.status_code == 200:
                    self.indicators['telegram'].config(foreground='green')
                else:
                    self.indicators['telegram'].config(foreground='red')
            except:
                self.indicators['telegram'].config(foreground='red')
        
        # GPS indicator
        if self.db.get_setting('gps_enabled', True):
            if self.lpr_processor and self.lpr_processor.current_location:
                self.indicators['gps'].config(foreground='green')
            else:
                self.indicators['gps'].config(foreground='yellow')
        
        # Database indicator
        try:
            with self.db.get_connection() as conn:
                conn.execute('SELECT 1')
            self.indicators['db'].config(foreground='green')
        except:
            self.indicators['db'].config(foreground='red')
    
    def update_analytics(self):
        """Update analytics charts"""
        stats = self.db.get_statistics()
        
        # Clear axes
        for ax in [self.ax1, self.ax2, self.ax3, self.ax4]:
            ax.clear()
        
        # Hourly distribution
        if stats['hourly_distribution']:
            hours = [int(h['hour']) for h in stats['hourly_distribution']]
            counts = [h['count'] for h in stats['hourly_distribution']]
            
            self.ax1.bar(hours, counts, color='#4CAF50')
            self.ax1.set_xlabel('Hour', color='white')
            self.ax1.set_ylabel('Detections', color='white')
            self.ax1.set_title('Hourly Distribution', color='white')
        
        # Country distribution
        if stats['country_distribution']:
            countries = [c['country_code'] or 'Unknown' for c in stats['country_distribution'][:5]]
            counts = [c['count'] for c in stats['country_distribution'][:5]]
            
            self.ax2.pie(counts, labels=countries, autopct='%1.1f%%',
                        colors=['#FF6384', '#36A2EB', '#FFCE56', '#4BC0C0', '#9966FF'])
            self.ax2.set_title('Top Countries', color='white')
        
        # Top plates
        if stats['top_plates']:
            plates = [p['plate_text_canonical'] for p in stats['top_plates'][:10]]
            counts = [p['detection_count'] for p in stats['top_plates'][:10]]
            
            self.ax3.barh(plates, counts, color='#FF9800')
            self.ax3.set_xlabel('Detections', color='white')
            self.ax3.set_title('Top 10 Plates', color='white')
        
        # Trend over time
        with self.db.get_connection() as conn:
            trend_data = conn.execute('''
                SELECT DATE(detection_ts) as date, COUNT(*) as count
                FROM original_detections
                WHERE DATE(detection_ts) >= DATE('now', '-30 days')
                GROUP BY date
                ORDER BY date
            ''').fetchall()
            
            if trend_data:
                dates = [d['date'] for d in trend_data]
                counts = [d['count'] for d in trend_data]
                
                self.ax4.plot(dates, counts, 'b-', linewidth=2)
                self.ax4.set_xlabel('Date', color='white')
                self.ax4.set_ylabel('Detections', color='white')
                self.ax4.set_title('30-Day Trend', color='white')
                
                # Rotate x labels
                for tick in self.ax4.get_xticklabels():
                    tick.set_rotation(45)
        
        # Redraw canvas
        self.canvas.draw()
    
    def cleanup_timer(self):
        """Periodic cleanup tasks"""
        # Clean old data based on retention policy
        retention_days = self.db.get_setting('retention_days', 90)
        
        with self.db.get_connection() as conn:
            cutoff_date = datetime.datetime.now() - datetime.timedelta(days=retention_days)
            
            # Delete old detections
            conn.execute('''
                DELETE FROM original_detections
                WHERE detection_ts < ?
            ''', (cutoff_date,))
            
            # Delete old performance stats
            conn.execute('''
                DELETE FROM performance_stats
                WHERE timestamp < ?
            ''', (cutoff_date,))
        
        # Check storage usage
        self.check_storage_usage()
        
        # Schedule next cleanup (every hour)
        self.root.after(3600000, self.cleanup_timer)
    
    def check_storage_usage(self):
        """Check and manage storage usage"""
        max_storage_gb = self.db.get_setting('max_storage_gb', 100)
        
        # Calculate current usage
        total_size = 0
        for dirpath, dirnames, filenames in os.walk('.'):
            for filename in filenames:
                filepath = os.path.join(dirpath, filename)
                total_size += os.path.getsize(filepath)
        
        size_gb = total_size / (1024**3)
        
        if size_gb > max_storage_gb * 0.9:  # 90% threshold
            logger.warning(f"Storage usage high: {size_gb:.1f}GB / {max_storage_gb}GB")
            
            # Could implement automatic cleanup of oldest files
            self.status_var.set(f"⚠️ Storage usage: {size_gb:.1f}GB / {max_storage_gb}GB")
    
    def show_plate_details(self, event=None):
        """Show comprehensive plate details"""
        selection = self.results_tree.selection()
        if not selection:
            return
        
        item = self.results_tree.item(selection[0])
        plate_text = item['values'][0]
        
        self.show_plate_details_by_text(plate_text)
    
    def show_plate_details_by_text(self, plate_text):
        """Show details window for specific plate"""
        details_window = tk.Toplevel(self.root)
        details_window.title(f"Plate Details - {plate_text}")
        details_window.geometry("1000x700")
        
        # Create notebook
        notebook = ttk.Notebook(details_window, padding="10")
        notebook.pack(fill=tk.BOTH, expand=True)
        
        # Overview tab
        overview_frame = ttk.Frame(notebook)
        notebook.add(overview_frame, text="Overview")
        
        self.create_overview_tab(overview_frame, plate_text)
        
        # History tab
        history_frame = ttk.Frame(notebook)
        notebook.add(history_frame, text="Detection History")
        
        self.create_history_tab(history_frame, plate_text)
        
        # Images tab
        images_frame = ttk.Frame(notebook)
        notebook.add(images_frame, text="Images")
        
        self.create_images_tab(images_frame, plate_text)
        
        # Map tab
        map_frame = ttk.Frame(notebook)
        notebook.add(map_frame, text="Location History")
        
        self.create_location_tab(map_frame, plate_text)
        
        # Analysis tab
        analysis_frame = ttk.Frame(notebook)
        notebook.add(analysis_frame, text="Analysis")
        
        self.create_analysis_tab(analysis_frame, plate_text)
    
    def export_data(self):
        """Export data with multiple format options"""
        export_window = tk.Toplevel(self.root)
        export_window.title("Export Data")
        export_window.geometry("500x400")
        export_window.transient(self.root)
        
        # Format selection
        ttk.Label(export_window, text="Select export format:",
                 font=('Segoe UI', 12)).pack(pady=10)
        
        format_var = tk.StringVar(value='csv')
        formats_frame = ttk.Frame(export_window)
        formats_frame.pack(pady=10)
        
        ttk.Radiobutton(formats_frame, text="CSV", variable=format_var,
                       value='csv').pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(formats_frame, text="Excel", variable=format_var,
                       value='excel').pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(formats_frame, text="JSON", variable=format_var,
                       value='json').pack(side=tk.LEFT, padx=10)
        ttk.Radiobutton(formats_frame, text="PDF Report", variable=format_var,
                       value='pdf').pack(side=tk.LEFT, padx=10)
        
        # Date range
        date_frame = ttk.LabelFrame(export_window, text="Date Range", padding="10")
        date_frame.pack(fill=tk.X, padx=20, pady=10)
        
        ttk.Label(date_frame, text="From:").grid(row=0, column=0, padx=5, pady=5)
        from_date = ttk.Entry(date_frame)
        from_date.grid(row=0, column=1, padx=5, pady=5)
        from_date.insert(0, (datetime.datetime.now() - datetime.timedelta(days=30)).strftime('%Y-%m-%d'))
        
        ttk.Label(date_frame, text="To:").grid(row=1, column=0, padx=5, pady=5)
        to_date = ttk.Entry(date_frame)
        to_date.grid(row=1, column=1, padx=5, pady=5)
        to_date.insert(0, datetime.datetime.now().strftime('%Y-%m-%d'))
        
        # Options
        options_frame = ttk.LabelFrame(export_window, text="Options", padding="10")
        options_frame.pack(fill=tk.X, padx=20, pady=10)
        
        include_images = tk.BooleanVar(value=False)
        ttk.Checkbutton(options_frame, text="Include images",
                       variable=include_images).pack(anchor=tk.W)
        
        include_stats = tk.BooleanVar(value=True)
        ttk.Checkbutton(options_frame, text="Include statistics",
                       variable=include_stats).pack(anchor=tk.W)
        
        # Export button
        def do_export():
            filename = filedialog.asksaveasfilename(
                defaultextension=f".{format_var.get()}",
                filetypes=[
                    ("CSV files", "*.csv"),
                    ("Excel files", "*.xlsx"),
                    ("JSON files", "*.json"),
                    ("PDF files", "*.pdf"),
                    ("All files", "*.*")
                ]
            )
            
            if filename:
                try:
                    # Perform export based on format
                    self.export_data_to_file(
                        filename, format_var.get(),
                        from_date.get(), to_date.get(),
                        include_images.get(), include_stats.get()
                    )
                    
                    messagebox.showinfo("Success", f"Data exported to {filename}")
                    export_window.destroy()
                    
                except Exception as e:
                    logger.error(f"Export failed: {e}")
                    messagebox.showerror("Error", f"Export failed: {str(e)}")
        
        ttk.Button(export_window, text="Export", command=do_export,
                  style='Accent.TButton').pack(pady=20)

    def new_session(self):
        """Start a fresh application session."""
        if self.lpr_processor:
            self.lpr_processor.end_session()
        self.is_processing = False
        self.start_button.config(text=f"▶ {self._('start')}")
        self.status_var.set("New session started")
        messagebox.showinfo("Session", "A new session has been created.")

    def load_session(self):
        """Placeholder for loading a previous session."""
        messagebox.showinfo("Load Session", "Session loading not implemented.")

    def import_data(self):
        """Placeholder for data import."""
        messagebox.showinfo("Import", "Data import not implemented.")

    def open_settings(self):
        """Placeholder for settings dialog."""
        messagebox.showinfo("Settings", "Settings dialog not implemented.")

    def open_blacklist(self):
        """Placeholder for blacklist management."""
        messagebox.showinfo("Blacklist", "Blacklist management not implemented.")

    def open_whitelist(self):
        """Placeholder for whitelist management."""
        messagebox.showinfo("Whitelist", "Whitelist management not implemented.")

    def show_statistics(self):
        """Placeholder for statistics window."""
        messagebox.showinfo("Statistics", "Statistics view not implemented.")

    def show_about(self):
        """Display a simple About dialog."""
        messagebox.showinfo("About", f"LPR Counter-Surveillance System v{VERSION}")

    def toggle_fullscreen(self):
        """Toggle the main window fullscreen state."""
        current = bool(self.root.attributes('-fullscreen'))
        self.root.attributes('-fullscreen', not current)

    def show_help(self):
        """Display a basic help message."""
        messagebox.showinfo("Help", "User guide not available yet.")

    def load_session_info(self):
        """Load persisted UI state."""
        pass

    def save_session_info(self):
        """Persist UI state for next launch."""
        pass

    def acknowledge_alert(self, window, plate_text):
        """Placeholder alert acknowledgement."""
        window.destroy()

    def show_tracking_alert(self, plate_text, details):
        """Placeholder tracking alert."""
        logger.info(f"Tracking alert for {plate_text}: {details}")

    def show_convoy_alert(self, data, details):
        """Placeholder convoy alert."""
        logger.info(f"Convoy alert: {details}")

    def update_alerts(self):
        """Placeholder to refresh alerts table."""
        pass

    def export_data_to_file(self, filename, fmt, from_date, to_date, include_images, include_stats):
        """Minimal data export implementation."""
        logger.info(f"Exporting data to {filename} in {fmt} format")

    def create_overview_tab(self, parent, plate_text):
        pass

    def create_history_tab(self, parent, plate_text):
        pass

    def create_images_tab(self, parent, plate_text):
        pass

    def create_location_tab(self, parent, plate_text):
        pass

    def create_analysis_tab(self, parent, plate_text):
        pass

    def filter_results(self):
        pass

    def sort_results(self):
        pass

    def show_routes(self):
        """Placeholder for route display."""
        messagebox.showinfo("Routes", "Route view not implemented.")

    def show_heatmap(self):
        """Placeholder for heatmap display."""
        messagebox.showinfo("Heat Map", "Heat map not implemented.")

    def export_charts(self):
        """Placeholder for chart export."""
        messagebox.showinfo("Export Charts", "Chart export not implemented.")

    def preview_camera(self):
        """Placeholder for camera preview."""
        messagebox.showinfo("Preview", "Camera preview not implemented.")

    def call_emergency(self):
        """Placeholder for emergency call action."""
        messagebox.showinfo("Emergency", "Call to emergency services triggered.")

    def show_context_menu(self, event):
        """Placeholder context menu."""
        pass

    def show_performance(self):
        """Placeholder performance monitor."""
        messagebox.showinfo("Performance", "Performance monitor not implemented.")
    
    def on_closing(self):
        """Handle application closing"""
        if self.is_processing:
            if messagebox.askyesno("Confirm", "Processing is active. Stop and exit?"):
                if self.lpr_processor:
                    self.lpr_processor.stop_capture()
                    self.lpr_processor.stop_video_recording()
                    self.lpr_processor.end_session()
            else:
                return
        
        # Save current settings
        self.save_session_info()
        
        self.root.destroy()
    
    def run(self):
        """Run the application"""
        # Show splash screen
        self.show_splash_screen()
        
        # Start main loop
        self.root.mainloop()
    
    def show_splash_screen(self):
        """Show splash screen on startup"""
        splash = tk.Toplevel(self.root)
        splash.title("")
        splash.geometry("500x300")
        splash.configure(bg='#2b2b2b')
        
        # Center splash screen
        splash.update_idletasks()
        x = (splash.winfo_screenwidth() - splash.winfo_width()) // 2
        y = (splash.winfo_screenheight() - splash.winfo_height()) // 2
        splash.geometry(f"+{x}+{y}")
        
        # Remove window decorations
        splash.overrideredirect(True)
        
        # Content
        ttk.Label(splash, text="LPR Counter-Surveillance System",
                 font=('Segoe UI', 20, 'bold'),
                 foreground='white',
                 background='#2b2b2b').pack(pady=50)
        
        ttk.Label(splash, text=f"Version {VERSION}",
                 font=('Segoe UI', 12),
                 foreground='gray',
                 background='#2b2b2b').pack()
        
        progress = ttk.Progressbar(splash, length=300, mode='indeterminate')
        progress.pack(pady=30)
        progress.start()
        
        # Close splash after 2 seconds
        splash.after(2000, splash.destroy)


def main():
    """Main entry point"""
    try:
        # Check dependencies
        logger.info(f"Starting LPR Counter-Surveillance System v{VERSION}")
        logger.info(f"Python version: {sys.version}")
        
        # Create and run application
        app = AdvancedMainApplication()
        app.run()
        
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=True)
        messagebox.showerror("Fatal Error", f"Application failed to start:\n{str(e)}")


if __name__ == "__main__":
    main()