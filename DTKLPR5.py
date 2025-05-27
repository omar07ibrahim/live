# -------------------------------------------
# DTK License Plate Recognition library
# Copyright (c) DTK Software
# https://www.dtksoft.com
# -------------------------------------------

import platform
from ctypes import *
import ctypes
from enum import Enum
from PIL import Image
import numpy as np
from DTKVID import PIXFMT, VideoFrame

_library = None


class BURN_POS(Enum):
    LEFT_TOP = 0
    RIGHT_TOP = 1
    LEFT_BOTTOM = 2
    RIGHT_BOTTOM = 3


class PLATE_TYPE(Enum):
    DARK_ON_LIGHT_BKG = 1
    LIGHT_ON_DARK_BKG = 2


class MOVING_DIRECTION(Enum):
    MV_INCOMING = 1
    MV_OUTGOING = 2
    MV_NO_MOVEMENT = 3


# events
LicensePlateDetectedCallback_type = CFUNCTYPE(None, c_void_p, c_void_p)


class DTKLPRLibrary:
    def __init__(self, lib_dir=None):
        if platform.system() == "Windows":
            lib_name = "DTKLPR5.dll"
        elif platform.system() == "Linux":
            lib_name = "libDTKLPR5.so"
        else:
            raise Exception("Unsupported platform")
        if lib_dir is None:
            self.lib = cdll.LoadLibrary(lib_name)
        else:
            self.lib = cdll.LoadLibrary(lib_dir + "/" + lib_name)
        # ------------------------------------------------
        # LPREngine
        # ------------------------------------------------
        # LPREngine_Create
        self.lib.LPREngine_Create.argtypes = [c_void_p, c_bool, LicensePlateDetectedCallback_type]
        self.lib.LPREngine_Create.restype = c_void_p

        # LPREngine_Destroy
        self.lib.LPREngine_Destroy.argtypes = [c_void_p]
        self.lib.LPREngine_Destroy.restype = None

        # LPREngine_SetFrameProcessingCompletedCallback | TODO:
        self.lib.LPREngine_SetFrameProcessingCompletedCallback.argtypes = [c_void_p, c_void_p]
        self.lib.LPREngine_SetFrameProcessingCompletedCallback.restype = None

        # LPREngine_ReadFromFile
        self.lib.LPREngine_ReadFromFile.argtypes = [c_void_p, c_char_p]
        self.lib.LPREngine_ReadFromFile.restype = c_void_p

        # LPREngine_ReadFromMemFile
        self.lib.LPREngine_ReadFromMemFile.argtypes = [c_void_p, POINTER(c_ubyte), c_int]
        self.lib.LPREngine_ReadFromMemFile.restype = c_void_p

        # LPREngine_ReadFromURL
        self.lib.LPREngine_ReadFromURL.argtypes = [c_void_p, c_char_p]
        self.lib.LPREngine_ReadFromURL.restype = c_void_p

        # LPREngine_ReadFromImageBuffer
        self.lib.LPREngine_ReadFromImageBuffer.argtypes = [c_void_p, POINTER(c_ubyte), c_int, c_int, c_int, c_int]
        self.lib.LPREngine_ReadFromImageBuffer.restype = c_void_p

        # LPREngine_PutFrameImageBuffer
        self.lib.LPREngine_PutFrameImageBuffer.argtypes = [c_void_p, POINTER(c_ubyte), c_int, c_int, c_int,
                                                           c_int, c_uint64, c_long]
        self.lib.LPREngine_PutFrameImageBuffer.restype = c_int

        # LPREngine_PutFrame
        self.lib.LPREngine_PutFrame.argtypes = [c_void_p, c_void_p, c_uint64]
        self.lib.LPREngine_PutFrame.restype = c_int

        # LPREngine_GetProcessingFPS
        self.lib.LPREngine_GetProcessingFPS.argtypes = [c_void_p]
        self.lib.LPREngine_GetProcessingFPS.restype = c_int

        # LPREngine_IsQueueEmpty
        self.lib.LPREngine_IsQueueEmpty.argtypes = [c_void_p]
        self.lib.LPREngine_IsQueueEmpty.restype = c_bool

        # LPREngine_IsLicensed
        self.lib.LPREngine_IsLicensed.argtypes = [c_void_p]
        self.lib.LPREngine_IsLicensed.restype = c_int

        # LPREngine_GetSupportedCountries
        self.lib.LPREngine_GetSupportedCountries.argtypes = [c_void_p, c_char_p]
        self.lib.LPREngine_GetSupportedCountries.restype = c_int

        # LPREngine_GetLibraryVersion
        self.lib.LPREngine_GetLibraryVersion.argtypes = [c_char_p, c_int]
        self.lib.LPREngine_GetLibraryVersion.restype = c_int

        # ------------------------------------------------
        # LPRParams
        # ------------------------------------------------

        # LPRParams_Create
        self.lib.LPRParams_Create.argtypes = []
        self.lib.LPRParams_Create.restype = c_void_p

        # LPRParams_Destroy
        self.lib.LPRParams_Destroy.argtypes = [c_void_p]
        self.lib.LPRParams_Destroy.restype = None

        # LPRParams_get_MinPlateWidth
        self.lib.LPRParams_get_MinPlateWidth.argtypes = [c_void_p]
        self.lib.LPRParams_get_MinPlateWidth.restype = c_int

        # LPRParams_set_MinPlateWidth
        self.lib.LPRParams_set_MinPlateWidth.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_MinPlateWidth.restype = None

        # LPRParams_get_MaxPlateWidth
        self.lib.LPRParams_get_MaxPlateWidth.argtypes = [c_void_p]
        self.lib.LPRParams_get_MaxPlateWidth.restype = c_int

        # LPRParams_set_MaxPlateWidth
        self.lib.LPRParams_set_MaxPlateWidth.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_MaxPlateWidth.restype = None

        # LPRParams_get_RotateAngle
        self.lib.LPRParams_get_RotateAngle.argtypes = [c_void_p]
        self.lib.LPRParams_get_RotateAngle.restype = c_int

        # LPRParams_set_RotateAngle
        self.lib.LPRParams_set_RotateAngle.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_RotateAngle.restype = None

        # LPRParams_get_Countries
        self.lib.LPRParams_get_Countries.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LPRParams_get_Countries.restype = c_int

        # LPRParams_set_Countries
        self.lib.LPRParams_set_Countries.argtypes = [c_void_p, c_char_p]
        self.lib.LPRParams_set_Countries.restype = None

        # LPRParams_get_FormatPlateText
        self.lib.LPRParams_get_FormatPlateText.argtypes = [c_void_p]
        self.lib.LPRParams_get_FormatPlateText.restype = c_bool

        # LPRParams_set_FormatPlateText
        self.lib.LPRParams_set_FormatPlateText.argtypes = [c_void_p, c_bool]
        self.lib.LPRParams_set_FormatPlateText.restype = None

        # LPRParams_get_NumThreads
        self.lib.LPRParams_get_NumThreads.argtypes = [c_void_p]
        self.lib.LPRParams_get_NumThreads.restype = c_int

        # LPRParams_set_NumThreads
        self.lib.LPRParams_set_NumThreads.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_NumThreads.restype = None

        # LPRParams_get_FPSLimit
        self.lib.LPRParams_get_FPSLimit.argtypes = [c_void_p]
        self.lib.LPRParams_get_FPSLimit.restype = c_int

        # LPRParams_set_FPSLimit
        self.lib.LPRParams_set_FPSLimit.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_FPSLimit.restype = None

        # LPRParams_get_DuplicateResultsDelay
        self.lib.LPRParams_get_DuplicateResultsDelay.argtypes = [c_void_p]
        self.lib.LPRParams_get_DuplicateResultsDelay.restype = c_int

        # LPRParams_set_DuplicateResultsDelay
        self.lib.LPRParams_set_DuplicateResultsDelay.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_DuplicateResultsDelay.restype = None

        # LPRParams_get_ResultConfirmationsCount
        self.lib.LPRParams_get_ResultConfirmationsCount.argtypes = [c_void_p]
        self.lib.LPRParams_get_ResultConfirmationsCount.restype = c_int

        # LPRParams_set_ResultConfirmationsCount
        self.lib.LPRParams_set_ResultConfirmationsCount.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_ResultConfirmationsCount.restype = None

        # LPRParams_get_RecognitionOnMotion
        self.lib.LPRParams_get_RecognitionOnMotion.argtypes = [c_void_p]
        self.lib.LPRParams_get_RecognitionOnMotion.restype = c_bool

        # LPRParams_set_RecognitionOnMotion
        self.lib.LPRParams_set_RecognitionOnMotion.argtypes = [c_void_p, c_bool]
        self.lib.LPRParams_set_RecognitionOnMotion.restype = None

        # LPRParams_get_BurnFormatString
        self.lib.LPRParams_get_BurnFormatString.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LPRParams_get_BurnFormatString.restype = c_int

        # LPRParams_set_BurnFormatString
        self.lib.LPRParams_set_BurnFormatString.argtypes = [c_void_p, c_char_p]
        self.lib.LPRParams_set_BurnFormatString.restype = None

        # LPRParams_get_BurnPosition
        self.lib.LPRParams_get_BurnPosition.argtypes = [c_void_p]
        self.lib.LPRParams_get_BurnPosition.restype = c_int

        # LPRParams_set_BurnPosition
        self.lib.LPRParams_set_BurnPosition.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_set_BurnPosition.restype = None

        # LPRParams_GetXOption
        self.lib.LPRParams_GetXOption.argtypes = [c_void_p, c_char_p, c_char_p, c_int]
        self.lib.LPRParams_GetXOption.restype = c_int

        # LPRParams_SetXOption
        self.lib.LPRParams_SetXOption.argtypes = [c_void_p, c_char_p, c_char_p]
        self.lib.LPRParams_SetXOption.restype = None

        # LPRParams_GetZonesCount
        self.lib.LPRParams_GetZonesCount.argtypes = [c_void_p]
        self.lib.LPRParams_GetZonesCount.restype = c_int

        # LPRParams_AddZone
        self.lib.LPRParams_AddZone.argtypes = [c_void_p]
        self.lib.LPRParams_AddZone.restype = c_int

        # LPRParams_RemoveZone
        self.lib.LPRParams_RemoveZone.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_RemoveZone.restype = c_int

        # LPRParams_GetZonePointsCount
        self.lib.LPRParams_GetZonePointsCount.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_GetZonePointsCount.restype = c_int

        # LPRParams_GetZonePoint
        self.lib.LPRParams_GetZonePoint.argtypes = [c_void_p, c_int, c_int, POINTER(c_int), POINTER(c_int)]
        self.lib.LPRParams_GetZonePoint.restype = None

        # LPRParams_SetZonePoint
        self.lib.LPRParams_SetZonePoint.argtypes = [c_void_p, c_int, c_int, c_int, c_int]
        self.lib.LPRParams_SetZonePoint.restype = None

        # LPRParams_AddZonePoint
        self.lib.LPRParams_AddZonePoint.argtypes = [c_void_p, c_int, c_int, c_int]
        self.lib.LPRParams_AddZonePoint.restype = c_int

        # LPRParams_RemoveZonePoint
        self.lib.LPRParams_RemoveZonePoint.argtypes = [c_void_p, c_int, c_int]
        self.lib.LPRParams_RemoveZonePoint.restype = c_int

        # LPRParams_GetZonePointsCountF
        self.lib.LPRParams_GetZonePointsCountF.argtypes = [c_void_p, c_int]
        self.lib.LPRParams_GetZonePointsCountF.restype = c_int

        # LPRParams_GetZonePointF
        self.lib.LPRParams_GetZonePointF.argtypes = [c_void_p, c_int, c_int, POINTER(c_float),
                                                     POINTER(c_float)]
        self.lib.LPRParams_GetZonePointF.restype = None

        # LPRParams_SetZonePointF
        self.lib.LPRParams_SetZonePointF.argtypes = [c_void_p, c_int, c_int, c_float, c_float]
        self.lib.LPRParams_SetZonePointF.restype = None

        # LPRParams_AddZonePointF
        self.lib.LPRParams_AddZonePointF.argtypes = [c_void_p, c_int, c_float, c_float]
        self.lib.LPRParams_AddZonePointF.restype = c_int

        # LPRParams_RemoveZonePointF
        self.lib.LPRParams_RemoveZonePointF.argtypes = [c_void_p, c_int, c_int]
        self.lib.LPRParams_RemoveZonePointF.restype = c_int

        # ------------------------------------------------
        # LPRResult
        # ------------------------------------------------

        # LPRResult_Destroy
        self.lib.LPRResult_Destroy.argtypes = [c_void_p]
        self.lib.LPRResult_Destroy.restype = None

        # LPRResult_GetPlatesCount
        self.lib.LPRResult_GetPlatesCount.argtypes = [c_void_p]
        self.lib.LPRResult_GetPlatesCount.restype = c_int

        # LPRResult_GetPlate
        self.lib.LPRResult_GetPlate.argtypes = [c_void_p, c_int]
        self.lib.LPRResult_GetPlate.restype = c_void_p

        # LPRResult_GetProcessingTime
        self.lib.LPRResult_GetProcessingTime.argtypes = [c_void_p]
        self.lib.LPRResult_GetProcessingTime.restype = c_int

        # ------------------------------------------------
        # LicensePlate
        # ------------------------------------------------

        # LicensePlate_Destroy
        self.lib.LicensePlate_Destroy.argtypes = [c_void_p]
        self.lib.LicensePlate_Destroy.restype = None

        # LicensePlate_GetText
        self.lib.LicensePlate_GetText.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_GetText.restype = c_int

        # LicensePlate_GetConfidence
        self.lib.LicensePlate_GetConfidence.argtypes = [c_void_p]
        self.lib.LicensePlate_GetConfidence.restype = c_int

        # LicensePlate_GetZone
        self.lib.LicensePlate_GetZone.argtypes = [c_void_p]
        self.lib.LicensePlate_GetZone.restype = c_int

        # LicensePlate_GetDirection
        self.lib.LicensePlate_GetDirection.argtypes = [c_void_p]
        self.lib.LicensePlate_GetDirection.restype = c_int

        # LicensePlate_GetMovingDirection
        self.lib.LicensePlate_GetMovingDirection.argtypes = [c_void_p]
        self.lib.LicensePlate_GetMovingDirection.restype = c_int

        # LicensePlate_GetTimestamp
        self.lib.LicensePlate_GetTimestamp.argtypes = [c_void_p]
        self.lib.LicensePlate_GetTimestamp.restype = c_long

        # LicensePlate_GetFrameTimestamp
        self.lib.LicensePlate_GetFrameTimestamp.argtypes = [c_void_p]
        self.lib.LicensePlate_GetFrameTimestamp.restype = c_long

        # LicensePlate_GetDateTimeString
        self.lib.LicensePlate_GetDateTimeString.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_GetDateTimeString.restype = c_int

        # LicensePlate_GetId
        self.lib.LicensePlate_GetId.argtypes = [c_void_p]
        self.lib.LicensePlate_GetId.restype = c_long

        # LicensePlate_GetCustomData
        self.lib.LicensePlate_GetCustomData.argtypes = [c_void_p]
        self.lib.LicensePlate_GetCustomData.restype = c_long

        # LicensePlate_GetImageBuffer
        self.lib.LicensePlate_GetImageBuffer.argtypes = [c_void_p, POINTER(c_void_p), POINTER(c_int),
                                                         POINTER(c_int), POINTER(c_int)]
        self.lib.LicensePlate_GetImageBuffer.restype = None

        # LicensePlate_GetPlateImageBuffer
        self.lib.LicensePlate_GetPlateImageBuffer.argtypes = [c_void_p, POINTER(c_void_p), POINTER(c_int),
                                                              POINTER(c_int), POINTER(c_int)]
        self.lib.LicensePlate_GetPlateImageBuffer.restype = None

        # LicensePlate_FreeImageBuffer
        self.lib.LicensePlate_FreeImageBuffer.argtypes = [c_void_p]
        self.lib.LicensePlate_FreeImageBuffer.restype = None

        # LicensePlate_SaveImage
        self.lib.LicensePlate_SaveImage.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_SaveImage.restype = c_int

        # LicensePlate_SavePlateImage
        self.lib.LicensePlate_SavePlateImage.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_SavePlateImage.restype = c_int

        # LicensePlate_GetCountryCode
        self.lib.LicensePlate_GetCountryCode.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_GetCountryCode.restype = c_int

        # LicensePlate_GetState
        self.lib.LicensePlate_GetState.argtypes = [c_void_p, c_char_p, c_int]
        self.lib.LicensePlate_GetState.restype = c_int

        # LicensePlate_GetType
        self.lib.LicensePlate_GetType.argtypes = [c_void_p]
        self.lib.LicensePlate_GetType.restype = c_int

        # LicensePlate_GetNumRows
        self.lib.LicensePlate_GetNumRows.argtypes = [c_void_p]
        self.lib.LicensePlate_GetNumRows.restype = c_int

        # LicensePlate_GetX
        self.lib.LicensePlate_GetX.argtypes = [c_void_p]
        self.lib.LicensePlate_GetX.restype = c_int

        # LicensePlate_GetY
        self.lib.LicensePlate_GetY.argtypes = [c_void_p]
        self.lib.LicensePlate_GetY.restype = c_int

        # LicensePlate_GetWidth
        self.lib.LicensePlate_GetWidth.argtypes = [c_void_p]
        self.lib.LicensePlate_GetWidth.restype = c_int

        # LicensePlate_GetHeight
        self.lib.LicensePlate_GetHeight.argtypes = [c_void_p]
        self.lib.LicensePlate_GetHeight.restype = c_int

        # LicensePlate_GetSymbolsCount
        self.lib.LicensePlate_GetSymbolsCount.argtypes = [c_void_p]
        self.lib.LicensePlate_GetSymbolsCount.restype = c_int

        # LicensePlate_GetSymbol
        self.lib.LicensePlate_GetSymbol.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbol.restype = c_wchar

        # LicensePlate_GetSymbolX
        self.lib.LicensePlate_GetSymbolX.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolX.restype = c_int

        # LicensePlate_GetSymbolY
        self.lib.LicensePlate_GetSymbolY.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolY.restype = c_int

        # LicensePlate_GetSymbolWidth
        self.lib.LicensePlate_GetSymbolWidth.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolWidth.restype = c_int

        # LicensePlate_GetSymbolHeight
        self.lib.LicensePlate_GetSymbolHeight.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolHeight.restype = c_int

        # LicensePlate_GetSymbolConfidence
        self.lib.LicensePlate_GetSymbolConfidence.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolConfidence.restype = c_int

        # LicensePlate_GetSymbolRowNum
        self.lib.LicensePlate_GetSymbolRowNum.argtypes = [c_void_p, c_int]
        self.lib.LicensePlate_GetSymbolRowNum.restype = c_int

        # ------------------------------------------------
        # License
        # ------------------------------------------------

        # LPREngine_ActivateLicenseOnline
        self.lib.LPREngine_ActivateLicenseOnline.argtypes = [c_char_p, c_char_p]
        self.lib.LPREngine_ActivateLicenseOnline.restype = c_int

        # LPREngine_ActivateLicenseOnlineEx
        self.lib.LPREngine_ActivateLicenseOnlineEx.argtypes = [c_char_p, c_char_p, c_int, c_char_p]
        self.lib.LPREngine_ActivateLicenseOnlineEx.restype = c_int

        # LPREngine_GetActivatedLicenseInfo
        self.lib.LPREngine_GetActivatedLicenseInfo.argtypes = [c_char_p, c_int, c_char_p, c_int,
                                                               POINTER(c_int), POINTER(c_long)]
        self.lib.LPREngine_GetActivatedLicenseInfo.restype = None

        # LPREngine_GetActivatedLicenseInfoEx
        self.lib.LPREngine_GetActivatedLicenseInfoEx.argtypes = [c_char_p, c_int, c_char_p, c_int,
                                                                 POINTER(c_int), POINTER(c_long), c_char_p, c_int]
        self.lib.LPREngine_GetActivatedLicenseInfoEx.restype = None

        # LPREngine_GetSystemID
        self.lib.LPREngine_GetSystemID.argtypes = [c_char_p, c_int]
        self.lib.LPREngine_GetSystemID.restype = c_int

        # LPREngine_ActivateLicenseOffline
        self.lib.LPREngine_ActivateLicenseOffline.argtypes = [c_char_p]
        self.lib.LPREngine_ActivateLicenseOffline.restype = c_int

        # LPREngine_GetActivationLink
        self.lib.LPREngine_GetActivationLink.argtypes = [c_char_p, c_char_p, c_char_p, c_int]
        self.lib.LPREngine_GetActivationLink.restype = c_int

        # LPREngine_SetNetLicenseServer
        self.lib.LPREngine_SetNetLicenseServer.argtypes = [c_char_p, c_int]
        self.lib.LPREngine_SetNetLicenseServer.restype = None

        # LPREngine_ReloadUSBDongles
        self.lib.LPREngine_ReloadUSBDongles.argtypes = []
        self.lib.LPREngine_ReloadUSBDongles.restype = None


# ------------------------------------------------
# LPRParams class
# ------------------------------------------------
class LPRParams:
    def __init__(self, library: DTKLPRLibrary = None):
        global _library
        if library is None:
            if _library is None:
                _library = DTKLPRLibrary()
            self.library = _library
        else:
            self.library = library
        self.hParams = self.library.lib.LPRParams_Create()

    def __del__(self):
        self.library.lib.LPRParams_Destroy(self.hParams)

    @property
    def MinPlateWidth(self) -> int:
        return self.library.lib.LPRParams_get_MinPlateWidth(self.hParams)

    @MinPlateWidth.setter
    def MinPlateWidth(self, value: int):
        self.library.lib.LPRParams_set_MinPlateWidth(self.hParams, value)

    @property
    def MaxPlateWidth(self) -> int:
        return self.library.lib.LPRParams_get_MaxPlateWidth(self.hParams)

    @MaxPlateWidth.setter
    def MaxPlateWidth(self, value: int):
        self.library.lib.LPRParams_set_MaxPlateWidth(self.hParams, value)

    @property
    def FormatPlateText(self) -> bool:
        return self.library.lib.LPRParams_get_FormatPlateText(self.hParams)

    @FormatPlateText.setter
    def FormatPlateText(self, value: bool):
        self.library.lib.LPRParams_set_FormatPlateText(self.hParams, value)

    @property
    def RotateAngle(self) -> int:
        return self.library.lib.LPRParams_get_RotateAngle(self.hParams)

    @RotateAngle.setter
    def RotateAngle(self, value: int):
        self.library.lib.LPRParams_set_RotateAngle(self.hParams, value)

    @property
    def FPSLimit(self) -> int:
        return self.library.lib.LPRParams_get_FPSLimit(self.hParams)

    @FPSLimit.setter
    def FPSLimit(self, value: int):
        self.library.lib.LPRParams_set_FPSLimit(self.hParams, value)

    @property
    def DuplicateResultsDelay(self) -> int:
        return self.library.lib.LPRParams_get_DuplicateResultsDelay(self.hParams)

    @DuplicateResultsDelay.setter
    def DuplicateResultsDelay(self, value: int):
        self.library.lib.LPRParams_set_DuplicateResultsDelay(self.hParams, value)

    @property
    def RecognitionOnMotion(self) -> bool:
        return self.library.lib.LPRParams_get_RecognitionOnMotion(self.hParams)

    @RecognitionOnMotion.setter
    def RecognitionOnMotion(self, value: bool):
        self.library.lib.LPRParams_set_RecognitionOnMotion(self.hParams, value)

    @property
    def ResultConfirmationsCount(self) -> int:
        return self.library.lib.LPRParams_get_ResultConfirmationsCount(self.hParams)

    @ResultConfirmationsCount.setter
    def ResultConfirmationsCount(self, value: int):
        self.library.lib.LPRParams_set_ResultConfirmationsCount(self.hParams, value)

    @property
    def NumThreads(self) -> int:
        return self.library.lib.LPRParams_get_NumThreads(self.hParams)

    @NumThreads.setter
    def NumThreads(self, value: int):
        self.library.lib.LPRParams_set_NumThreads(self.hParams, value)

    @property
    def BurnFormatString(self) -> str:
        size = self.library.lib.LPRParams_get_BurnFormatString(self.hParams, None, 0)
        burn_format_string = ctypes.create_string_buffer(size)
        self.library.lib.LPRParams_get_BurnFormatString(self.hParams, burn_format_string, size)
        return burn_format_string.value.decode('utf-8')

    @BurnFormatString.setter
    def BurnFormatString(self, value: str):
        self.library.lib.LPRParams_set_BurnFormatString(self.hParams, value.encode())

    @property
    def BurnPosition(self) -> BURN_POS:
        return BURN_POS(self.library.lib.LPRParams_get_BurnPosition(self.hParams))

    @BurnPosition.setter
    def BurnPosition(self, value: BURN_POS):
        self.library.lib.LPRParams_set_BurnPosition(self.hParams, value.value)

    def GetZonesCount(self) -> int:
        return self.library.lib.LPRParams_GetZonesCount(self.hParams)

    def AddZone(self) -> int:
        return self.library.lib.LPRParams_AddZone(self.hParams)

    def RemoveZone(self, index: int) -> int:
        return self.library.lib.LPRParams_RemoveZone(self.hParams, index)

    def GetZonePointsCount(self, index: int) -> int:
        return self.library.lib.LPRParams_GetZonePointsCount(self.hParams, index)

    def GetZonePoint(self, zone_index: int, point_index: int) -> (int, int):
        x = c_int()
        y = c_int()
        self.library.lib.LPRParams_GetZonePoint(self.hParams, zone_index, point_index, byref(x), byref(y))
        return x.value, y.value

    def SetZonePoint(self, zone_index: int, point_index: int, x: int, y: int):
        self.library.lib.LPRParams_SetZonePoint(self.hParams, zone_index, point_index, x, y)

    def AddZonePoint(self, zone_index: int, x: int, y: int) -> int:
        return self.library.lib.LPRParams_AddZonePoint(self.hParams, zone_index, x, y)

    def RemoveZonePoint(self, zone_index: int, point_index: int) -> int:
        return self.library.lib.LPRParams_RemoveZonePoint(self.hParams, zone_index, point_index)

    def GetZonePointsCountF(self, index: int) -> int:
        return self.library.lib.LPRParams_GetZonePointsCountF(self.hParams, index)

    def GetZonePointF(self, zone_index: int, point_index: int) -> (float, float):
        x = c_float()
        y = c_float()
        self.library.lib.LPRParams_GetZonePointF(self.hParams, zone_index, point_index, byref(x), byref(y))
        return x.value, y.value

    def SetZonePointF(self, zone_index: int, point_index: int, x: float, y: float):
        self.library.lib.LPRParams_SetZonePointF(self.hParams, zone_index, point_index, x, y)

    def AddZonePointF(self, zone_index: int, x: float, y: float) -> int:
        return self.library.lib.LPRParams_AddZonePointF(self.hParams, zone_index, x, y)

    def RemoveZonePointF(self, zone_index: int, point_index: int) -> int:
        return self.library.lib.LPRParams_RemoveZonePointF(self.hParams, zone_index, point_index)

    @property
    def Countries(self) -> str:
        size = self.library.lib.LPRParams_get_Countries(self.hParams, None, 0)
        countries = ctypes.create_string_buffer(size)
        self.library.lib.LPRParams_get_Countries(self.hParams, countries, size)
        return countries.value

    @Countries.setter
    def Countries(self, value: str):
        self.library.lib.LPRParams_set_Countries(self.hParams, value.encode())

    def GetXOption(self, option: str) -> str:
        option_value = ctypes.create_string_buffer(255)
        self.library.lib.LPRParams_GetXOption(self.hParams, option, option_value, 255)
        return option_value.value

    def SetXOption(self, option: str, value: str):
        self.library.lib.LPRParams_SetXOption(self.hParams, option.encode(), value.encode())


# ------------------------------------------------
# LicensePlateSymbol class
# ------------------------------------------------
class LicensePlateSymbol:
    def __init__(self, symbol: str, confidence: int, x: int, y: int, width: int, height: int, row_num: int):
        self.symbol = symbol
        self.confidence = confidence
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.row_num = row_num

    def Symbol(self) -> str:
        return self.symbol

    def Confidence(self) -> int:
        return self.confidence

    def X(self) -> int:
        return self.x

    def Y(self) -> int:
        return self.y

    def Width(self) -> int:
        return self.width

    def Height(self) -> int:
        return self.height

    def RowNum(self) -> int:
        return self.row_num

# ------------------------------------------------
# LicensePlate class
# ------------------------------------------------
class LicensePlate:
    def __init__(self, hPlate: c_void_p, library: DTKLPRLibrary):
        self.library = library
        self.hPlate = hPlate
        self.symbols = self.__load_symbols()

    def __del__(self):
        self.library.lib.LicensePlate_Destroy(self.hPlate)

    def __load_symbols(self):
        res = []
        cnt = self.library.lib.LicensePlate_GetSymbolsCount(self.hPlate)
        for i in range(cnt):
            symbol = LicensePlateSymbol(
                self.library.lib.LicensePlate_GetSymbol(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolConfidence(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolX(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolY(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolWidth(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolHeight(self.hPlate, i),
                self.library.lib.LicensePlate_GetSymbolRowNum(self.hPlate, i)
            )
            res.append(symbol)
        return res

    def Text(self) -> str:
        text = ctypes.create_string_buffer(100)
        self.library.lib.LicensePlate_GetText(self.hPlate, text, 100)
        return text.value.decode('utf-8')

    def CountryCode(self) -> str:
        country_code = ctypes.create_string_buffer(10)
        self.library.lib.LicensePlate_GetCountryCode(self.hPlate, country_code, 10)
        return country_code.value.decode('utf-8')

    def State(self) -> str:
        state = ctypes.create_string_buffer(10)
        self.library.lib.LicensePlate_GetState(self.hPlate, state, 10)
        return state.value.decode('utf-8')

    def Confidence(self) -> int:
        return self.library.lib.LicensePlate_GetConfidence(self.hPlate)

    def Zone(self) -> int:
        return self.library.lib.LicensePlate_GetZone(self.hPlate)

    def Direction(self) -> int:
        return self.library.lib.LicensePlate_GetDirection(self.hPlate)

    def MovingDirection(self) -> MOVING_DIRECTION:
        return MOVING_DIRECTION(self.library.lib.LicensePlate_GetMovingDirection(self.hPlate))

    def Timestamp(self) -> int:
        return self.library.lib.LicensePlate_GetTimestamp(self.hPlate)

    def FrameTimestamp(self) -> int:
        return self.library.lib.LicensePlate_GetFrameTimestamp(self.hPlate)

    def DateTimeString(self) -> str:
        size = self.library.lib.LicensePlate_GetDateTimeString(self.hPlate, None, 0)
        date_time = ctypes.create_string_buffer(size)
        self.library.lib.LicensePlate_GetDateTimeString(self.hPlate, date_time, size)
        return date_time.value

    def Id(self) -> int:
        return self.library.lib.LicensePlate_GetId(self.hPlate)

    def CustomData(self) -> int:
        return self.library.lib.LicensePlate_GetCustomData(self.hPlate)

    def Type(self) -> PLATE_TYPE:
        return self.library.lib.LicensePlate_GetType(self.hPlate)

    def NumRows(self) -> int:
        return self.library.lib.LicensePlate_GetNumRows(self.hPlate)

    def X(self) -> int:
        return self.library.lib.LicensePlate_GetX(self.hPlate)

    def Y(self) -> int:
        return self.library.lib.LicensePlate_GetY(self.hPlate)

    def Width(self) -> int:
        return self.library.lib.LicensePlate_GetWidth(self.hPlate)

    def Height(self) -> int:
        return self.library.lib.LicensePlate_GetHeight(self.hPlate)

    def GetSymbolsCount(self) -> int:
        return self.library.lib.LicensePlate_GetSymbolsCount(self.hPlate)

    def GetSymbol(self, index: int) -> str:
        symbol = self.library.lib.LicensePlate_GetSymbol(self.hPlate, index)
        return symbol.value.decode('utf-8')

    def GetSymbolX(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolX(self.hPlate, index)

    def GetSymbolY(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolY(self.hPlate, index)

    def GetSymbolWidth(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolWidth(self.hPlate, index)

    def GetSymbolHeight(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolHeight(self.hPlate, index)

    def GetSymbolConfidence(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolConfidence(self.hPlate, index)

    def GetSymbolRowNum(self, index: int) -> int:
        return self.library.lib.LicensePlate_GetSymbolRowNum(self.hPlate, index)
    def GetImage(self) -> Image:
        buf = c_void_p()  # Используем c_void_p для хранения указателя
        w, h, s = c_int(0), c_int(0), c_int(0)
        
        # Здесь мы убираем передачу PIXFMT как аргумент, потому что он должен быть заранее установлен в библиотеке
        self.library.lib.LicensePlate_GetImageBuffer(self.hPlate, byref(buf), byref(w), byref(h), byref(s))
        
        # Преобразуем указатель в массив байтов
        data = np.ctypeslib.as_array((c_ubyte * (w.value * h.value * 3)).from_address(buf.value))
        
        img = Image.frombuffer('RGB', (w.value, h.value), data, "raw", "RGB")
        self.library.lib.LicensePlate_FreeImageBuffer(buf)
        return img

    def GetPlateImage(self) -> Image:
        buf = c_void_p()  # Используем c_void_p для хранения указателя
        w, h, s = c_int(0), c_int(0), c_int(0)
        
        # Убираем передачу PIXFMT в функцию
        self.library.lib.LicensePlate_GetPlateImageBuffer(self.hPlate, byref(buf), byref(w), byref(h), byref(s))
        
        # Преобразуем указатель в массив байтов
        data = np.ctypeslib.as_array((c_ubyte * (w.value * h.value * 3)).from_address(buf.value))
        
        img = Image.frombuffer('RGB', (w.value, h.value), data, "raw", "RGB")
        self.library.lib.LicensePlate_FreeImageBuffer(buf)
        return img

    def SaveImage(self, file_path: str, quality: int) -> int:
        return self.library.lib.LicensePlate_SaveImage(self.hPlate, file_path.encode(), quality)

    def SavePlateImage(self, file_path: str, quality: int) -> int:
        return self.library.lib.LicensePlate_SavePlateImage(self.hPlate, file_path.encode(), quality)

    def __str__(self):
        return f"text: {self.Text()}, country: {self.CountryCode()}, confidence: {self.Confidence()}"


# ------------------------------------------------
# LPREngine class
# ------------------------------------------------
class LPREngine:
    def __init__(self, params: LPRParams, video: bool = False, licensePlateDetectedCallback=None):
        self.library = params.library
        self.params = params
        self.licensePlateDetectedCallback = licensePlateDetectedCallback
        self.callback_LicensePlateDetected = LicensePlateDetectedCallback_type(self.__LicensePlateDetectedCallback)
        self.hEngine = self.library.lib.LPREngine_Create(self.params.hParams, video, self.callback_LicensePlateDetected)

    def __del__(self):
        self.library.lib.LPREngine_Destroy(self.hEngine)

    def __LicensePlateDetectedCallback(self, hVideoCapture, hPlate):
        plate = LicensePlate(hPlate, self.library)
        self.licensePlateDetectedCallback(self, plate)

    def ReadFromFile(self, file_path: str):
        hResult = self.library.lib.LPREngine_ReadFromFile(self.hEngine, file_path.encode())
        return self.__get_result(hResult)

    def ReadFromMemFile(self, mem_file: bytes):
        mem_file = (c_ubyte * len(mem_file)).from_buffer_copy(mem_file)
        hResult = self.library.lib.LPREngine_ReadFromMemFile(self.hEngine, mem_file, len(mem_file))
        return self.__get_result(hResult)

    def ReadFromURL(self, url: str):
        hResult = self.library.lib.LPREngine_ReadFromURL(self.hEngine, url.encode())
        return self.__get_result(hResult)

    def ReadFromImageBuffer(self, image_buffer: bytes, width: int, height: int, stride: int, format: int):
        image_buffer = (c_ubyte * len(image_buffer)).from_buffer_copy(image_buffer)
        hResult = self.library.lib.LPREngine_ReadFromImageBuffer(self.hEngine, image_buffer, width, height, stride,
                                                                 format)
        return self.__get_result(hResult)

    def PutFrameImageBuffer(self, image_buffer: bytes, width: int, height: int, stride: int, format: int,
                            timestamp: int, custom_data: int):
        image_buffer = (c_ubyte * len(image_buffer)).from_buffer_copy(image_buffer)
        return self.library.lib.LPREngine_PutFrameImageBuffer(self.hEngine, image_buffer, width, height, stride, format,
                                                              c_uint64(timestamp), custom_data)

    def PutFrame(self, frame: VideoFrame, timestamp: int):
        return self.library.lib.LPREngine_PutFrame(self.hEngine, frame.hFrame, c_uint64(timestamp))

    def GetProcessingFPS(self) -> int:
        return self.library.lib.LPREngine_GetProcessingFPS(self.hEngine)

    def IsQueueEmpty(self) -> bool:
        return self.library.lib.LPREngine_IsQueueEmpty(self.hEngine)

    def GetSupportedCountries(self) -> str:
        size = self.library.lib.LPREngine_GetSupportedCountries(self.hEngine, None, 0)
        countries = ctypes.create_string_buffer(size)
        self.library.lib.LPREngine_GetSupportedCountries(self.hEngine, countries, size)
        return countries.value

    def __get_result(self, hResult):
        platesCount = self.library.lib.LPRResult_GetPlatesCount(hResult)
        processingTime = self.library.lib.LPRResult_GetProcessingTime(hResult)
        plates = []
        for i in range(platesCount):
            hPlate = self.library.lib.LPRResult_GetPlate(hResult, i)
            plates.append(LicensePlate(hPlate, self.library))
        self.library.lib.LPRResult_Destroy(hResult)
        return plates, processingTime

    def IsLicensed(self) -> int:
        return self.library.lib.LPREngine_IsLicensed(self.hEngine)

    @staticmethod
    def __get_library(library):
        global _library
        if library is None:
            if _library is None:
                _library = DTKLPRLibrary()
            library = _library
        return library

    @staticmethod
    def GetLibraryVersion(library: DTKLPRLibrary = None) -> str:
        library = LPREngine.__get_library(library)
        size = library.lib.LPREngine_GetLibraryVersion(None, 0)
        version = ctypes.create_string_buffer(size)
        library.lib.LPREngine_GetLibraryVersion(version, size)
        return version.value.decode("utf-8")

    @staticmethod
    def ActivateLicenseOnline(license_key: str, comments: str, library: DTKLPRLibrary = None) -> int:
        library = LPREngine.__get_library(library)
        return library.lib.LPREngine_ActivateLicenseOnline(license_key.encode(), comments.encode())

    @staticmethod
    def ActivateLicenseOnlineEx(license_key: str, comments: str, channels: int, security_key: str,
                                library: DTKLPRLibrary = None) -> int:
        library = LPREngine.__get_library(library)
        return library.lib.LPREngine_ActivateLicenseOnlineEx(license_key.encode(), comments.encode(), channels, security_key.encode())

    @staticmethod
    def GetActivatedLicenseInfo(library: DTKLPRLibrary = None) -> (str, str, int, int):
        library = LPREngine.__get_library(library)
        license_key = ctypes.create_string_buffer(100)
        comments = ctypes.create_string_buffer(255)
        channels = c_int()
        expiration_date = c_long()
        library.lib.LPREngine_GetActivatedLicenseInfo(license_key, 100, comments, 255, byref(channels),
                                                      byref(expiration_date))
        return (license_key.value.decode('utf-8'),
                comments.value.decode('utf-8'),
                channels.value,
                expiration_date.value)

    @staticmethod
    def GetActivatedLicenseInfoEx(library: DTKLPRLibrary = None) -> (str, str, int, int, str):
        library = LPREngine.__get_library(library)
        license_key = ctypes.create_string_buffer(100)
        comments = ctypes.create_string_buffer(255)
        channels = c_int()
        expiration_date = c_long()
        dongleID = ctypes.create_string_buffer(255)
        library.lib.LPREngine_GetActivatedLicenseInfoEx(license_key, 100, comments, 255, byref(channels),
                                                        byref(expiration_date), dongleID, 100)
        return (license_key.value.decode('utf-8'),
                comments.value.decode('utf-8'),
                channels.value,
                expiration_date.value,
                dongleID.value.decode('utf-8'))

    @staticmethod
    def GetSystemID(library: DTKLPRLibrary = None) -> str:
        library = LPREngine.__get_library(library)
        systemID = ctypes.create_string_buffer(50)
        library.lib.LPREngine_GetSystemID(systemID, 50)
        return systemID.value.decode('utf-8')

    @staticmethod
    def ActivateLicenseOffline(license_key: str, library: DTKLPRLibrary = None) -> int:
        library = LPREngine.__get_library(library)
        return library.lib.LPREngine_ActivateLicenseOffline(license_key.encode())

    @staticmethod
    def GetActivationLink(license_key: str, email: str, comments: str, library: DTKLPRLibrary = None) -> str:
        library = LPREngine.__get_library(library)
        activation_link = ctypes.create_string_buffer(255)
        library.lib.LPREngine_GetActivationLink(license_key.encode(), email.encode(), comments.encode(), activation_link, 255)
        return activation_link.value

    @staticmethod
    def SetNetLicenseServer(server: str, port: int, library: DTKLPRLibrary = None):
        library = LPREngine.__get_library(library)
        library.lib.LPREngine_SetNetLicenseServer(server.encode(), port)

    @staticmethod
    def ReloadUSBDongles(library: DTKLPRLibrary = None):
        library = LPREngine.__get_library(library)
        library.lib.LPREngine_ReloadUSBDongles()
