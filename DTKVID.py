# -------------------------------------------
# DTK Video Capture library
# Copyright (c) DTK Software
# https://www.dtksoft.com
# -------------------------------------------
import platform
from ctypes import *
import ctypes
from enum import Enum
from PIL import Image
import numpy as np

_library = None


class PIXFMT(Enum):
    GRAYSCALE = 1
    RGB24 = 2
    BGR24 = 3
    YUV420 = 4


class ERR_CAPTURE(Enum):
    OPEN_VIDEO = 1
    READ_FRAME = 2
    EOF = 3


# events
FrameCapturedCallback_type = CFUNCTYPE(None, c_void_p, c_void_p, c_uint64)
CaptureErrorCallback_type = CFUNCTYPE(None, c_void_p, c_int, c_void_p)


class DTKVIDLibrary:
    def __init__(self, lib_dir: str = None):
        if platform.system() == "Windows":
            lib_name = "DTKVID.dll"
        elif platform.system() == "Linux":
            lib_name = "libDTKVID.so"
        else:
            raise Exception("Unsupported platform")
        if lib_dir is None:
            self.lib = cdll.LoadLibrary(lib_name)
        else:
            self.lib = cdll.LoadLibrary(lib_dir + "/" + lib_name)
        # ------------------------------------------------
        # VideoCapture
        # ------------------------------------------------
        # VideoCapture_Create
        self.lib.VideoCapture_Create.argtypes = [FrameCapturedCallback_type, CaptureErrorCallback_type, c_void_p]
        self.lib.VideoCapture_Create.restype = POINTER(c_void_p)

        # VideoCapture_Destroy
        self.lib.VideoCapture_Destroy.argtypes = [c_void_p]
        self.lib.VideoCapture_Destroy.restype = None

        # VideoCapture_StartCaptureFromFile
        self.lib.VideoCapture_StartCaptureFromFile.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.VideoCapture_StartCaptureFromFile.restype = c_int

        # VideoCapture_StartCaptureFromIPCamera
        self.lib.VideoCapture_StartCaptureFromIPCamera.argtypes = [c_void_p, c_char_p]
        self.lib.VideoCapture_StartCaptureFromIPCamera.restype = c_int

        # VideoCapture_StartCaptureFromDevice
        self.lib.VideoCapture_StartCaptureFromDevice.argtypes = [c_void_p, c_int, c_int, c_int]
        self.lib.VideoCapture_StartCaptureFromDevice.restype = c_int

        # VideoCapture_StopCapture
        self.lib.VideoCapture_StopCapture.argtypes = [c_void_p]
        self.lib.VideoCapture_StopCapture.restype = c_int

        # VideoCapture_GetVideoWidth
        self.lib.VideoCapture_GetVideoWidth.argtypes = [c_void_p]
        self.lib.VideoCapture_GetVideoWidth.restype = c_int

        # VideoCapture_GetVideoHeight
        self.lib.VideoCapture_GetVideoHeight.argtypes = [c_void_p]
        self.lib.VideoCapture_GetVideoHeight.restype = c_int

        # VideoCapture_GetVideoFPS
        self.lib.VideoCapture_GetVideoFPS.argtypes = [c_void_p]
        self.lib.VideoCapture_GetVideoFPS.restype = c_int

        # VideoCapture_GetVideoFOURCC
        self.lib.VideoCapture_GetVideoFOURCC.argtypes = [c_void_p]
        self.lib.VideoCapture_GetVideoFOURCC.restype = c_int

        # VideoCapture_GetLibraryVersion
        self.lib.VideoCapture_GetLibraryVersion.argtypes = [c_char_p, c_int]
        self.lib.VideoCapture_GetLibraryVersion.restype = c_int

        # ------------------------------------------------
        # VideoFrame
        # ------------------------------------------------

        # VideoFrame_Destroy
        self.lib.VideoFrame_Destroy.argtypes = [c_void_p]
        self.lib.VideoFrame_Destroy.restype = None

        # VideoFrame_GetWidth
        self.lib.VideoFrame_GetWidth.argtypes = [c_void_p]
        self.lib.VideoFrame_GetWidth.restype = c_int

        # VideoFrame_GetHeight
        self.lib.VideoFrame_GetHeight.argtypes = [c_void_p]
        self.lib.VideoFrame_GetHeight.restype = c_int

        # VideoFrame_Timestamp
        self.lib.VideoFrame_Timestamp.argtypes = [c_void_p]
        self.lib.VideoFrame_GetHeight.restype = c_uint64

        # VideoFrame_GetImageBuffer
        self.lib.VideoFrame_GetImageBuffer.argtypes = [c_void_p, c_int, POINTER(c_void_p), POINTER(c_int),
                                                       POINTER(c_int), POINTER(c_int)]
        self.lib.VideoFrame_GetImageBuffer.restype = None

        # VideoFrame_FreeImageBuffer
        self.lib.VideoFrame_FreeImageBuffer.argtypes = [c_void_p]
        self.lib.VideoFrame_FreeImageBuffer.restype = None


class VideoCapture:
    def __init__(self, frameCapturedCallback, captureError, customObject=None, library: DTKVIDLibrary = None):
        global _library
        if library is None:
            if _library is None:
                _library = DTKVIDLibrary()
            self.library = _library
        else:
            self.library = library

        self.callback_FrameCaptured = FrameCapturedCallback_type(self.__FrameCapturedCallback)
        self.callback_CaptureError = CaptureErrorCallback_type(self.__CaptureErrorCallback)

        self.hVideoCapture = self.library.lib.VideoCapture_Create(
            self.callback_FrameCaptured, self.callback_CaptureError, None)

        self.frameCapturedCallback = frameCapturedCallback
        self.captureError = captureError
        self.customObject = customObject

    def __del__(self):
        self.library.lib.VideoCapture_Destroy(self.hVideoCapture)

    def __FrameCapturedCallback(self, hVideoCapture, hFrame, customObject):
        frame = VideoFrame(hFrame, self.library)
        self.frameCapturedCallback(self, frame, self.customObject)

    def __CaptureErrorCallback(self, hVideoCapture, errorCode, customObject):
        self.captureError(self, errorCode, self.customObject)

    def StartCaptureFromFile(self, file_name: str, repeat_count: int = 0) -> int:
        return self.library.lib.VideoCapture_StartCaptureFromFile(
            self.hVideoCapture, file_name.encode(), repeat_count)

    def StartCaptureFromIPCamera(self, url: str) -> int:
        return self.library.lib.VideoCapture_StartCaptureFromIPCamera(self.hVideoCapture, url.encode('utf-8'))

    def StartCaptureFromDevice(self, deviceIndex: int, captureWidth: int, captureHeight: int) -> int:
        return self.library.lib.VideoCapture_StartCaptureFromDevice(self.hVideoCapture, deviceIndex, captureWidth,
                                                                    captureHeight)

    def GetVideoWidth(self) -> int:
        return self.library.lib.VideoCapture_GetVideoWidth(self.hVideoCapture)

    def GetVideoHeight(self) -> int:
        return self.library.lib.VideoCapture_GetVideoHeight(self.hVideoCapture)

    def GetVideoFPS(self) -> int:
        return self.library.lib.VideoCapture_GetVideoFPS(self.hVideoCapture)

    def GetVideoFOURCC(self) -> int:
        return self.library.lib.VideoCapture_GetVideoFOURCC(self.hVideoCapture)

    def StopCapture(self) -> int:
        return self.library.lib.VideoCapture_StopCapture(self.hVideoCapture)

    @staticmethod
    def GetLibraryVersion(library: DTKVIDLibrary = None) -> str:
        global _library
        if library is None:
            if _library is None:
                _library = DTKVIDLibrary()
            library = _library
        size = library.lib.VideoCapture_GetLibraryVersion(None, 0)
        version = ctypes.create_string_buffer(size)
        library.lib.VideoCapture_GetLibraryVersion(version, size)
        return version.value.decode("utf-8")


class VideoFrame:
    def __init__(self, hFrame: c_void_p, library: DTKVIDLibrary):
        self.library = library
        self.hFrame = hFrame

    def Release(self):
        self.library.lib.VideoFrame_Destroy(self.hFrame)

    def GetWidth(self) -> int:
        return self.library.lib.VideoFrame_GetWidth(self.hFrame)

    def GetHeight(self) -> int:
        return self.library.lib.VideoFrame_GetHeight(self.hFrame)

    def Timestamp(self) -> int:
        return self.library.lib.VideoFrame_Timestamp(self.hFrame)

    def GetImage(self) -> Image:
        buf = POINTER(c_ubyte)()
        w, h, s = c_int(0), c_int(0), c_int(0)
        self.library.lib.VideoFrame_GetImageBuffer(self.hFrame, PIXFMT.RGB24, byref(buf), byref(w), byref(h), byref(s))
        data = np.ctypeslib.as_array(buf, shape=(w.value * h.value * 3,))
        img = Image.frombuffer('RGB', (w.value, h.value), data, "raw", "RGB")
        self.library.lib.VideoFrame_FreeImageBuffer(buf)
        return img
