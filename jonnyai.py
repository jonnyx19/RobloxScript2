import csv, ctypes, json, math, os, queue, random, string, sys, threading, time
import hashlib, platform, subprocess, urllib.request, urllib.error
from ctypes import wintypes
from typing import Optional, Tuple
from PyQt5 import QtWebEngineWidgets 
import cv2
import numpy as np
import onnxruntime as ort
import win32api, win32con, win32gui
from PyQt5 import QtWebEngineWidgets  # must be first

from PyQt5.QtCore import Qt
from PyQt5.QtWidgets import QApplication

QApplication.setAttribute(Qt.AA_ShareOpenGLContexts)

app = QApplication([])
from PyQt6 import QtCore, QtWidgets
from PyQt6.QtCore import QUrl, QObject, pyqtSlot, pyqtSignal, QTimer
from PyQt6.QtGui import QColor, QPainter, QPen
from PyQt6.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget
from PyQt6.QtWebEngineWidgets import QWebEngineView
from PyQt6.QtWebChannel import QWebChannel

# ──────────────────────────────────────────────────────────────────
#  KEY SYSTEM — communicates with pythonanywhere server
#  Endpoints: /flygod/activate  and  /flygod/loader_check
# ──────────────────────────────────────────────────────────────────
_SERVER_BASE = "https://jonnydev.pythonanywhere.com/"
_KEY_FILE    = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".jny_license")

def _get_hwid() -> str:
    """Generate a stable HWID from machine identifiers."""
    try:
        # Windows: use wmic csproduct get UUID
        out = subprocess.check_output(
            ["wmic", "csproduct", "get", "UUID"],
            stderr=subprocess.DEVNULL, timeout=6
        ).decode(errors="ignore")
        uid = out.strip().split()[-1]
    except Exception:
        uid = platform.node()
    raw = f"{uid}-{platform.machine()}-{platform.processor()}"
    return hashlib.sha256(raw.encode()).hexdigest()[:48]

def _http_post(endpoint: str, payload: dict, timeout: int = 10):
    """Simple JSON POST without requests library."""
    url  = _SERVER_BASE + endpoint
    data = json.dumps(payload).encode()
    req  = urllib.request.Request(
        url, data=data,
        headers={"Content-Type": "application/json", "User-Agent": "JNY/6.5"},
        method="POST"
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode())
    except urllib.error.HTTPError as e:
        body = {}
        try: body = json.loads(e.read().decode())
        except: pass
        return {"success": False, "message": body.get("message", f"HTTP {e.code}"), "_status": e.code}
    except Exception as ex:
        return {"success": False, "message": str(ex), "_status": 0}

def _save_key(key: str, hwid: str, expiry: str):
    try:
        data = json.dumps({"key": key, "hwid": hwid, "expiry": expiry})
        with open(_KEY_FILE, "w") as f:
            f.write(data)
    except Exception:
        pass

def _load_saved_key():
    try:
        with open(_KEY_FILE, "r") as f:
            return json.loads(f.read())
    except Exception:
        return None

def keysystem_validate(key: str, hwid: str) -> tuple:
    """
    Returns (ok: bool, message: str, expiry: str|None)
    Calls /flygod/activate which handles first-use binding and expiry check.
    """
    result = _http_post("/flygod/activate", {"key": key, "hwid": hwid})
    if result.get("success"):
        return True, "OK", result.get("expiry", "")
    return False, result.get("message", "Server error"), None

def keysystem_loader_check(hwid: str) -> tuple:
    """
    Returns (ok: bool, message: str)
    Periodic check — server can kill a session mid-use.
    """
    result = _http_post("/flygod/loader_check", {"hwid": hwid})
    if result.get("success"):
        return True, "OK"
    return False, result.get("message", "Access denied")

# ── Globals set after successful auth ──
_AUTHED_HWID   = ""
_AUTHED_EXPIRY = ""

# ── Try bettercam, fall back to mss gracefully ──────────────────
try:
    import bettercam
    _BETTERCAM_AVAILABLE = True
except ImportError:
    import mss
    _BETTERCAM_AVAILABLE = False
    print("[Capture] bettercam not found, using mss. Install: pip install bettercam")

MONITOR_WIDTH  = ctypes.windll.user32.GetSystemMetrics(0)
MONITOR_HEIGHT = ctypes.windll.user32.GetSystemMetrics(1)

MAX_FOV      = 200
FRAME_SIZE   = MAX_FOV * 2
FRAME_WIDTH  = FRAME_SIZE // 2
FRAME_HEIGHT = FRAME_SIZE // 2

_rx = int(MONITOR_WIDTH  / 2 - FRAME_WIDTH)
_ry = int(MONITOR_HEIGHT / 2 - FRAME_HEIGHT)
_rw = _rx + FRAME_SIZE
_rh = _ry + FRAME_SIZE

screenshotcentre = [FRAME_SIZE // 2, FRAME_SIZE // 2]
MSS_REGION = {"left": _rx, "top": _ry, "width": FRAME_SIZE, "height": FRAME_SIZE}
BC_REGION = (_rx, _ry, _rw, _rh)
INFER_SIZE = 480

loaded             = False
session            = None
previousads        = None
_target_fps_global = 360
fps_val            = 0
_active_provider   = "CPU"

_win_mouse_speed     = 10
_win_speed_last_read = 0.0

def _refresh_win_mouse_speed():
    global _win_mouse_speed, _win_speed_last_read
    now = time.perf_counter()
    if now - _win_speed_last_read < 2.0:
        return _win_mouse_speed
    try:
        spd = ctypes.c_int(0)
        ctypes.windll.user32.SystemParametersInfoW(0x0070, 0, ctypes.byref(spd), 0)
        v = max(1, min(20, spd.value))
    except Exception:
        v = 10
    _win_mouse_speed = v
    _win_speed_last_read = now
    return v

def get_sens_scale() -> float:
    return 10.0 / max(1, _refresh_win_mouse_speed())

keymapping = {
    "RightMouse":0x02,"LeftMouse":0x01,"MiddleMouse":0x04,
    "X1Mouse":0x05,"X2Mouse":0x06,"Tab":0x09,
    "Shift":0x10,"Control":0x11,"Alt":0x12,
    "CapsLock":0x14,"LMB":0x01,"RMB":0x02,
    "MMB":0x04,"Mouse4":0x05,"Mouse5":0x06,
    "Backspace":0x08,"Enter":0x0D,"Pause":0x13,
    "Caps":0x14,"Esc":0x1B,"Space":0x20,
    "PgUp":0x21,"PgDn":0x22,"End":0x23,
    "Home":0x24,"Left":0x25,"Up":0x26,
    "Right":0x27,"Down":0x28,"Insert":0x2D,"Delete":0x2E,
    "Num0":0x60,"Num1":0x61,"Num2":0x62,"Num3":0x63,
    "Num4":0x64,"Num5":0x65,"Num6":0x66,"Num7":0x67,
    "Num8":0x68,"Num9":0x69,
    "F1":0x70,"F2":0x71,"F3":0x72,"F4":0x73,
    "F5":0x74,"F6":0x75,"F7":0x76,"F8":0x77,
    "F9":0x78,"F10":0x79,"F11":0x7A,"F12":0x7B,
    "LShift":0xA0,"RShift":0xA1,"LCtrl":0xA2,"RCtrl":0xA3,
    "LAlt":0xA4,"RAlt":0xA5,
    **{chr(i): i for i in range(0x41, 0x5B)},
    **{str(i-0x30): i for i in range(0x30, 0x3A)},
}

KEY_ITEMS = ["RightMouse","LeftMouse","MiddleMouse","X1Mouse","X2Mouse",
             "Tab","Shift","Control","Alt","CapsLock",
             *[chr(i) for i in range(0x41, 0x5B)],
             *[str(i) for i in range(10)]]

def generaterandomstring(length: int = 12) -> str:
    return "".join(random.choices(string.ascii_letters + string.digits, k=length))

INPUT_MOUSE          = 0
MOUSEEVENTF_MOVE     = 0x0001
MOUSEEVENTF_LEFTDOWN = 0x0002
MOUSEEVENTF_LEFTUP   = 0x0004

class MouseInput(ctypes.Structure):
    _fields_ = [("dx",ctypes.c_long),("dy",ctypes.c_long),
                ("mouseData",ctypes.c_ulong),("dwFlags",ctypes.c_ulong),
                ("time",ctypes.c_ulong),("dwExtraInfo",ctypes.POINTER(ctypes.c_ulong))]

class Input_I(ctypes.Union):
    _fields_ = [("mi", MouseInput)]

class InputStruct(ctypes.Structure):
    _fields_ = [("type",ctypes.c_ulong),("ii",Input_I)]

_extra_info   = ctypes.c_ulong(0)
_extra_ptr    = ctypes.pointer(_extra_info)
_input_struct = InputStruct()
_input_struct.type = INPUT_MOUSE
_input_ptr    = ctypes.pointer(_input_struct)
_input_size   = ctypes.sizeof(_input_struct)

def mousemove(dx: int, dy: int):
    _input_struct.ii.mi.dx = int(dx)
    _input_struct.ii.mi.dy = int(dy)
    _input_struct.ii.mi.dwFlags = MOUSEEVENTF_MOVE
    _input_struct.ii.mi.dwExtraInfo = _extra_ptr
    ctypes.windll.user32.SendInput(1, _input_ptr, _input_size)

def _click(flag: int):
    _input_struct.ii.mi.dx = 0; _input_struct.ii.mi.dy = 0
    _input_struct.ii.mi.dwFlags = flag
    _input_struct.ii.mi.dwExtraInfo = _extra_ptr
    ctypes.windll.user32.SendInput(1, _input_ptr, _input_size)

def mouseclick():
    _click(MOUSEEVENTF_LEFTDOWN); _click(MOUSEEVENTF_LEFTUP)

def ads() -> bool:
    return win32api.GetKeyState(0x02) in (-127, -128)

class SettingsStore:
    _defaults = {
        "aimbotcheckbox":              False,
        "regularstrengthslider":       150,
        "adsstrengthslider":           120,
        "speedmultiplierslider":       25,
        "aimboneradiobutton":          "Head",
        "customoffsetslider":          2,
        "regularfovslider":            80,
        "adsfovslider":                60,
        "aimbothotkeycombobox":        "RightMouse",
        "aimbotadskeycombobox":        "RightMouse",
        "smoothnessslider":            40,
        "triggerbotcheckbox":          False,
        "triggerbothotkeycombobox":    "RightMouse",
        "antirecoilcheckbox":          False,
        "antirecoilstrengthslider":    5,
        "antirecoilhotkeycombobox":    "RightMouse",
        "antirecoilpatterncombo":      "default",
        "patterncheckbox":             False,
        "patternhotkeycombobox":       "RightMouse",
        "patternselect":               "default",
        "patternspeedslider":          10,
        "patternscaleslider":          10,
        "patternloopcheckbox":         True,
        "patterncustom":               "",
        "drawfovcirclecheckbox":       True,
        "drawcircleoutlinescheckbox":  False,
        "fovcirclecolorpicker":        [255,255,255,255],
        "drawcrosshaircheckbox":       True,
        "crosshairsizeslider":         6,
        "crosshaircolorpicker":        [255,255,255,255],
        "drawtargetboxescheckbox":     True,
        "drawboxoutlinescheckbox":     False,
        "targetboxestyperadiobutton":  "Regular Box",
        "targetboxescolorpicker":      [255,255,255,255],
        "drawtargettracerscheckbox":   False,
        "drawtraceroutlinescheckbox":  False,
        "targettracersfromradiobutton":"Screen Centre",
        "targettracerstoradiobutton":  "Aim Bone",
        "targettracerscolorpicker":    [255,255,255,255],
        "drawframesquarecheckbox":     False,
        "ignorefortniteplayercheckbox":False,
        "aiconfidenceslider":          35,
        "aiiouslider":                 45,
        "streamproofcheckbox":         False,
        "targetfpsslider":             360,
        "modelcombobox":               "best.onnx",
        "lockradiusslider":            90,
        "locktimeoutslider":           35,
        "predictionstrengthslider":    50,
        "stickinessslider":            50,
    }

    def __init__(self):
        self._data = dict(self._defaults)
        self._lock = threading.RLock()

    def get(self, key, default=None):
        with self._lock:
            return self._data.get(key, self._defaults.get(key, default))

    def set(self, key, value):
        with self._lock:
            self._data[key] = value

    def get_all(self) -> dict:
        with self._lock:
            return dict(self._data)

    def load_from_dict(self, d: dict):
        with self._lock:
            for k, v in d.items():
                self._data[k] = v

    def save(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'jonny_settings.json')
        try:
            with self._lock: data = dict(self._data)
            with open(path, 'w') as f: json.dump(data, f, indent=2)
        except Exception: pass

    def load(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'jonny_settings.json')
        try:
            with open(path, 'r') as f: d = json.load(f)
            self.load_from_dict(d)
        except Exception: pass

settings = SettingsStore()
settings.load()

class AimLogger:
    def __init__(self):
        self._file=None; self._writer=None
        self._lock=threading.Lock(); self.enabled=False

    def start(self, path: str):
        with self._lock:
            if self._file: self._file.close()
            self._file=open(path,"w",newline="")
            self._writer=csv.writer(self._file)
            self._writer.writerow(["ts","tx","ty","ax","ay","ex","ey","mx","my","conf"])
            self.enabled=True

    def stop(self):
        with self._lock:
            self.enabled=False
            if self._file: self._file.close()
            self._file=None; self._writer=None

    def log(self,tx,ty,ax,ay,ex,ey,mx,my,conf):
        if not self.enabled: return
        with self._lock:
            if self._writer:
                self._writer.writerow([f"{time.perf_counter():.6f}",
                    f"{tx:.2f}",f"{ty:.2f}",f"{ax:.2f}",f"{ay:.2f}",
                    f"{ex:.2f}",f"{ey:.2f}",f"{mx:.3f}",f"{my:.3f}",f"{conf:.3f}"])

_aim_logger = AimLogger()


class DetectionResult:
    __slots__=("box","cx","cy","conf","cls","timestamp","has_detection","second_box","second_conf")
    def __init__(self,box=None,cx=0.0,cy=0.0,conf=0.0,cls=0,second_box=None,second_conf=0.0):
        self.box=box; self.cx=cx; self.cy=cy; self.conf=conf; self.cls=cls
        self.timestamp=time.perf_counter(); self.has_detection=box is not None
        self.second_box=second_box; self.second_conf=second_conf


class TargetScorer:
    def __init__(self, conf_weight=0.25, dist_weight=0.75):
        self.conf_weight = conf_weight
        self.dist_weight = dist_weight

    def score(self, det, centre, max_dist) -> float:
        x1,y1,x2,y2,conf,cls = det
        cx = (x1 + x2) / 2
        cy = (y1 + y2) / 2
        dist = math.hypot(cx - centre[0], cy - centre[1])
        
        # Basis-Score
        base = self.conf_weight * conf + self.dist_weight * (1.0 - min(dist / max(max_dist, 1.0), 1.0))
        
        # Extra Bonus für aktuell gelocktes Ziel (stark reduziert Wegrutschen)
        return base


def calculate_iou(box1, box2) -> float:
    x1 = max(box1[0], box2[0])
    y1 = max(box1[1], box2[1])
    x2 = min(box1[2], box2[2])
    y2 = min(box1[3], box2[3])
    inter = max(0, x2 - x1 + 1) * max(0, y2 - y1 + 1)
    a1 = (box1[2] - box1[0] + 1) * (box1[3] - box1[1] + 1)
    a2 = (box2[2] - box2[0] + 1) * (box2[3] - box2[1] + 1)
    union = a1 + a2 - inter
    return inter / union if union > 0 else 0.0


def nms(detections: np.ndarray, iou_threshold: float) -> list:
    if len(detections) == 0:
        return []
    keep = []
    while len(detections) > 0:
        best = detections[0]
        keep.append(best)
        if len(detections) == 1:
            break
        ious = np.array([calculate_iou(best[:4], d[:4]) for d in detections[1:]])
        detections = detections[1:][ious < iou_threshold]
    return keep


def postprocess(outputs, conf_threshold, iou_threshold, max_det=8) -> list:
    raw = outputs[0]
    if raw.ndim == 3 and raw.shape[2] == 6:
        preds = np.squeeze(raw, 0)
        filtered = preds[preds[:,4] >= conf_threshold]
        if len(filtered) == 0: 
            return []
        filtered = filtered[np.argsort(-filtered[:,4])]
        kept = nms(filtered, iou_threshold)
        return [[float(d[0]),float(d[1]),float(d[2]),float(d[3]),float(d[4]),int(d[5])] 
                for d in np.array(kept)[:max_det]]

    # YOLOv8 / YOLOv11 Format
    if raw.ndim == 3 and raw.shape[1] < raw.shape[2]:
        preds = np.squeeze(raw, 0).T
        boxes = preds[:,:4]
        scores = preds[:,4:]
        cls_ids = np.argmax(scores, axis=1)
        confs = scores[np.arange(len(scores)), cls_ids]
        mask = confs >= conf_threshold
        if len(mask) == 0:
            return []
        boxes_f = boxes[mask]
        confs_f = confs[mask]
        cls_f = cls_ids[mask]
        x1 = boxes_f[:,0] - boxes_f[:,2]/2
        y1 = boxes_f[:,1] - boxes_f[:,3]/2
        x2 = boxes_f[:,0] + boxes_f[:,2]/2
        y2 = boxes_f[:,1] + boxes_f[:,3]/2
        dets = np.stack([x1,y1,x2,y2,confs_f,cls_f.astype(float)], axis=1)
        dets = dets[np.argsort(-dets[:,4])]
        kept = nms(dets, iou_threshold)
        return [[float(d[0]),float(d[1]),float(d[2]),float(d[3]),float(d[4]),int(d[5])] 
                for d in np.array(kept)[:max_det]]

    return []


def _scale_detections(dets, frame_w, frame_h, imgsz=480) -> list:
    result = []
    for det in dets:
        x1,y1,x2,y2,conf,cls = det
        if max(x1,y1,x2,y2) <= 1.0:   # normalized
            x1s = int(x1 * frame_w)
            y1s = int(y1 * frame_h)
            x2s = int(x2 * frame_w)
            y2s = int(y2 * frame_h)
        else:
            x1s = int(x1 * frame_w / imgsz)
            y1s = int(y1 * frame_h / imgsz)
            x2s = int(x2 * frame_w / imgsz)
            y2s = int(y2 * frame_h / imgsz)
        result.append([x1s, y1s, x2s, y2s, conf, int(cls)])
    return result


def is_within_fov(fovcenter, fovradius, box) -> bool:
    x1,y1,x2,y2 = box
    cx,cy = fovcenter
    for px,py in [(x1,y1),(x1,y2),(x2,y1),(x2,y2)]:
        if math.dist((px,py),(cx,cy)) <= fovradius * 1.2:
            return True
    if cx + fovradius*1.15 >= x1 and cx - fovradius*1.15 <= x2 and cy >= y1 and cy <= y2:
        return True
    if cy + fovradius*1.15 >= y1 and cy - fovradius*1.15 <= y2 and cx >= x1 and cx <= x2:
        return True
    return False


ENEMY_CLASS_IDS: list = [0]

def is_enemy_class(cls_id: int) -> bool:
    return int(cls_id) in ENEMY_CLASS_IDS


class KalmanAimFilter:
    def __init__(self):
        self.F = np.array([[1,0,1,0],[0,1,0,1],[0,0,1,0],[0,0,0,1]], dtype=np.float64)
        self.H = np.array([[1,0,0,0],[0,1,0,0]], dtype=np.float64)
        q = 13.5                                     # nah am Original, aber stabiler bei schnellen Moves
        self.Q = np.diag([q, q, q*2.4, q*2.4]).astype(np.float64)
        r = 2.9                                      # höher = filtert Noise besser → kein Schwanken mehr
        self.R = np.diag([r, r]).astype(np.float64)
        self.P = np.eye(4, dtype=np.float64) * 155.0
        self.x = np.zeros((4,1), dtype=np.float64)
        self._initialized = False
        self._vel_damping = 0.97                     # leichte Dämpfung genau für schnelle Bewegungen

    def reset(self):
        self.x[:] = 0
        self.P = np.eye(4, dtype=np.float64) * 155.0
        self._initialized = False

    def init(self, px: float, py: float):
        self.x[0,0] = px
        self.x[1,0] = py
        self.x[2,0] = 0.0
        self.x[3,0] = 0.0
        self.P = np.eye(4, dtype=np.float64) * 26.0
        self._initialized = True

    def predict(self, dt: float) -> tuple:
        if not self._initialized:
            return (float(self.x[0,0]), float(self.x[1,0]))
        
        dt = max(0.0, min(dt, 0.08))
        self.F[0,2] = dt
        self.F[1,3] = dt
        self.x = self.F @ self.x
        self.P = self.F @ self.P @ self.F.T + self.Q
        
        self.x[2:4] *= self._vel_damping
        
        return (float(self.x[0,0]), float(self.x[1,0]))

    def update(self, px: float, py: float) -> tuple:
        z = np.array([[px],[py]], dtype=np.float64)
        if not self._initialized:
            self.init(px, py)
            return (px, py)
        
        y = z - self.H @ self.x
        S = self.H @ self.P @ self.H.T + self.R
        K = self.P @ self.H.T @ np.linalg.inv(S)
        self.x = self.x + K @ y
        self.P = (np.eye(4) - K @ self.H) @ self.P
        return (float(self.x[0,0]), float(self.x[1,0]))

    @property
    def velocity(self) -> tuple:
        return (float(self.x[2,0]), float(self.x[3,0]))

    @property
    def position(self) -> tuple:
        return (float(self.x[0,0]), float(self.x[1,0]))

    @property
    def initialized(self) -> bool:
        return self._initialized


class PDController:
    STOP_THRESHOLD = 0.8

    def __init__(self):
        self.kp = 1.5
        self.kd = 0.05
        self._alpha = 0.6
        self._max_px = 25.0
        self._last_ex = 0.0
        self._last_ey = 0.0
        self._rem_x   = 0.0
        self._rem_y   = 0.0
        self._smx     = 0.0
        self._smy     = 0.0

    def reset(self):
        self._last_ex = self._last_ey = 0.0
        self._rem_x   = self._rem_y   = 0.0
        self._smx     = self._smy     = 0.0

    def configure(self, strength: float, smoothness: float, speed_px: float):
        t = strength / 272.0
        self.kp = 1.0 + t * 4.4                      # stärker und schneller aufs Ziel
        self.kd = 0.025 + t * 0.052
        s = max(0.0, min(100.0, smoothness)) / 100.0
        self._alpha = 0.86 - s * 0.39                # mehr Glätte = konstant und scharf, kein Schwanken
        self._max_px = speed_px / max(get_sens_scale(), 0.5)

    def tick(self, ex: float, ey: float, dt: float) -> tuple:
        dist = math.hypot(ex, ey)
        if dist < self.STOP_THRESHOLD:
            self.reset()
            return (0, 0)
        
        dex = (ex - self._last_ex) / max(dt, 1e-4)
        dey = (ey - self._last_ey) / max(dt, 1e-4)
        self._last_ex = ex
        self._last_ey = ey
        
        raw_x = (self.kp * ex + self.kd * dex) / 1000.0
        raw_y = (self.kp * ey + self.kd * dey) / 1000.0
        
        mag = math.hypot(raw_x, raw_y)
        if mag > self._max_px:
            raw_x = raw_x / mag * self._max_px
            raw_y = raw_y / mag * self._max_px
        
        if dist < 14.0:
            feather = dist / 14.0
            raw_x *= feather
            raw_y *= feather
        
        self._smx = self._smx * (1 - self._alpha) + raw_x * self._alpha
        self._smy = self._smy * (1 - self._alpha) + raw_y * self._alpha
        
        self._rem_x += self._smx
        self._rem_y += self._smy
        ix = int(self._rem_x)
        iy = int(self._rem_y)
        self._rem_x -= ix
        self._rem_y -= iy
        
        ix = max(min(ix, 10.2), -10.2)
        iy = max(min(iy, 10.2), -10.2)
        
        return (ix, iy)


class ScreenCapture(threading.Thread):
    def __init__(self, frame_q):
        super().__init__(daemon=True)
        self.frame_q = frame_q
        self.running = True
        self._cam = None

    def _init_bettercam(self):
        try:
            cam = bettercam.create(device_idx=0, output_color="BGR")
            cam.start(region=BC_REGION, target_fps=_target_fps_global, video_mode=True)
            self._cam = cam
            print("[Capture] bettercam initialized")
            return True
        except Exception as e:
            print(f"[Capture] bettercam init failed: {e}, falling back to mss")
            return False

    def run(self):
        if _BETTERCAM_AVAILABLE:
            use_bc = self._init_bettercam()
        else:
            use_bc = False
        if use_bc:
            self._run_bettercam()
        else:
            self._run_mss()

    def _run_bettercam(self):
        while self.running:
            frame = self._cam.get_latest_frame()
            if frame is None:
                time.sleep(0.002)
                continue
            try: self.frame_q.get_nowait()
            except queue.Empty: pass
            self.frame_q.put_nowait(frame)

    def _run_mss(self):
        import mss as _mss
        with _mss.mss() as sct:
            while self.running:
                t0 = time.perf_counter()
                raw = sct.grab(MSS_REGION)
                frame = np.frombuffer(raw.raw, dtype=np.uint8)
                frame = frame.reshape((raw.height,raw.width,4))[:,:,:3].copy()
                try: self.frame_q.get_nowait()
                except queue.Empty: pass
                self.frame_q.put_nowait(frame)
                elapsed = time.perf_counter()-t0
                tfps = max(60, min(360, _target_fps_global))
                sleep = (1.0/tfps)-elapsed
                if sleep>0: time.sleep(sleep)

    def stop(self):
        self.running = False
        if self._cam is not None:
            try: self._cam.stop()
            except Exception: pass


class DetectionResult:
    __slots__=("box","cx","cy","conf","cls","timestamp","has_detection","second_box","second_conf")
    def __init__(self,box=None,cx=0.0,cy=0.0,conf=0.0,cls=0,second_box=None,second_conf=0.0):
        self.box=box; self.cx=cx; self.cy=cy; self.conf=conf; self.cls=cls
        self.timestamp=time.perf_counter(); self.has_detection=box is not None
        self.second_box=second_box; self.second_conf=second_conf


class TargetScorer:
    def __init__(self, conf_weight=0.25, dist_weight=0.75):
        self.conf_weight=conf_weight; self.dist_weight=dist_weight

    def score(self, det, centre, max_dist) -> float:
        x1,y1,x2,y2,conf,cls=det
        dist=math.hypot((x1+x2)/2-centre[0],(y1+y2)/2-centre[1])
        return self.conf_weight*conf+self.dist_weight*(1.0-min(dist/max(max_dist,1.0),1.0))


class Detector(threading.Thread):
    def __init__(self, frame_q, result_q):
        super().__init__(daemon=True)
        self.frame_q=frame_q; self.result_q=result_q; self.running=True
        self._scorer=TargetScorer(0.25,0.75)
        self._locked_cx=None; self._locked_cy=None; self._lock_age=0.0

    def _best_target(self, dets, sc):
        enemy_dets=[d for d in dets if is_enemy_class(d[5])]
        if not enemy_dets: return None, None
        ignore_fp=settings.get("ignorefortniteplayercheckbox",False)
        if ignore_fp:
            filtered=([d for d in enemy_dets if d[0]>=MAX_FOV/4] if ads()
                      else [d for d in enemy_dets if d[0]>=MAX_FOV/2])
            if filtered: enemy_dets=filtered
        now=time.perf_counter()
        lock_radius=settings.get("lockradiusslider",90)
        lock_timeout=settings.get("locktimeoutslider",35)/100.0
        max_dist=math.hypot(FRAME_SIZE,FRAME_SIZE)
        if self._locked_cx is not None and now-self._lock_age<lock_timeout:
            lock_candidates=[d for d in enemy_dets
                             if math.hypot((d[0]+d[2])/2-self._locked_cx,
                                           (d[1]+d[3])/2-self._locked_cy)<lock_radius]
            if lock_candidates: enemy_dets=lock_candidates
        scored=sorted(enemy_dets,key=lambda d:self._scorer.score(d,sc,max_dist),reverse=True)
        best=scored[0] if scored else None
        second=scored[1] if len(scored)>1 else None
        if best is not None:
            self._locked_cx=(best[0]+best[2])/2; self._locked_cy=(best[1]+best[3])/2
            self._lock_age=now
        return best, second

    def run(self):
        global session
        inp_name_cache=None
        while self.running:
            if session is None or not loaded: time.sleep(0.05); continue
            try: frame=self.frame_q.get(timeout=0.05)
            except queue.Empty: continue
            try:
                conf_thresh=settings.get("aiconfidenceslider",35)/100
                iou_thresh=settings.get("aiiouslider",45)/100
                if inp_name_cache is None:
                    inp_name_cache=session.get_inputs()[0].name
                resized=cv2.resize(frame,(INFER_SIZE,INFER_SIZE),interpolation=cv2.INTER_LINEAR)
                img=resized[:,:,::-1].astype(np.float32)*(1.0/255.0)
                img=np.ascontiguousarray(np.transpose(img,(2,0,1)))[np.newaxis]
                outputs=session.run(None,{inp_name_cache:img})
                dets=postprocess(outputs,conf_thresh,iou_thresh)
                fw,fh=frame.shape[1],frame.shape[0]
                dets=_scale_detections(dets,fw,fh,INFER_SIZE)
                best,second=self._best_target(dets,screenshotcentre)
                if best is not None:
                    x1,y1,x2,y2,conf,cls=best
                    result=DetectionResult(
                        box=(int(x1),int(y1),int(x2),int(y2)),
                        cx=(x1+x2)/2,cy=(y1+y2)/2,conf=conf,cls=cls,
                        second_box=(int(second[0]),int(second[1]),int(second[2]),int(second[3])) if second else None,
                        second_conf=float(second[4]) if second else 0.0)
                else:
                    result=DetectionResult()
            except Exception:
                result=DetectionResult()
            try: self.result_q.get_nowait()
            except queue.Empty: pass
            self.result_q.put_nowait(result)

    def stop(self): self.running=False


class PersonValidator:
    def is_person(self, x1, y1, x2, y2, conf: float=1.0) -> bool:
        w=x2-x1; h=y2-y1
        if w<=0 or h<=0: return False
        if (h/w)<0.7: return False
        if w>160: return False
        if h<5: return False
        return True


DEFAULT_RECOIL_PATTERNS = {
    "default":         [[0,1],[0,2],[0,2],[0,3],[0,3],[0,3],[0,2],[0,2],[0,1],[0,1]],
    "ak":              [[0,2],[0,3],[-1,3],[1,3],[0,4],[0,4],[-1,3],[1,3],[0,3],[0,2]],
    "smg":             [[0,1],[0,1],[0,2],[0,2],[0,2],[0,1],[0,1],[0,1],[0,1],[0,1]],
    "lmg":             [[0,2],[0,2],[0,3],[0,3],[0,4],[0,4],[0,3],[0,3],[0,2],[0,2]],
    "sniper":          [[0,4],[0,1],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],
    "valorant_vandal": [[0,2],[0,3],[-1,3],[1,3],[0,4],[-1,3],[1,3],[0,3],[-1,2],[1,2]],
    "valorant_phantom":[[0,1],[0,2],[-1,2],[1,2],[0,3],[0,3],[-1,2],[1,2],[0,2],[0,1]],
    "csgo_ak47":       [[0,3],[0,4],[-1,4],[1,4],[0,5],[-1,4],[1,4],[0,4],[-1,3],[1,3]],
    "csgo_m4":         [[0,2],[0,3],[-1,3],[1,3],[0,3],[-1,3],[1,3],[0,3],[-1,2],[1,2]],
    "fortnite_ar":     [[0,1],[0,2],[0,2],[0,2],[0,3],[0,3],[0,2],[0,2],[0,1],[0,1]],
}

class RecoilEngine:
    _SHOT_INTERVAL = 0.1   # advance one pattern step every 100ms

    def __init__(self):
        self._pats      = {k: list(v) for k, v in DEFAULT_RECOIL_PATTERNS.items()}
        self._active    = "default"
        self._idx       = 0
        self._last_fire = 0.0
        self._firing    = False
        self._reset_t   = 0.0      # timestamp of last LMB-up
        self._reset_delay = 0.22   # seconds after release before index resets
        self._rem_x     = 0.0
        self._rem_y     = 0.0

    def set_pattern(self, name):
        if name in self._pats and name != self._active:
            self._active = name
            self._idx    = 0
            self._rem_x  = self._rem_y = 0.0

    def add_custom(self, name, points):
        if name and points: self._pats[name] = points

    def tick(self, strength: float) -> tuple:
        """
        strength: 1..15 from slider, converted to real px/step.
        Returns (ix, iy) integer mouse delta.
        Call every aimer loop tick (~1ms).
        LMB state is read internally for reliability.
        """
        lmb_held = win32api.GetKeyState(0x01) in (-127, -128)
        now       = time.perf_counter()

        if not lmb_held:
            if self._firing:
                self._firing  = False
                self._reset_t = now
            # Reset index after brief delay so next burst starts fresh
            if self._reset_t > 0 and now - self._reset_t > self._reset_delay:
                self._idx    = 0
                self._rem_x  = self._rem_y = 0.0
                self._reset_t = 0.0
            return (0, 0)

        if not self._firing:
            self._firing    = True
            self._idx       = 0
            self._last_fire = now
            self._rem_x     = self._rem_y = 0.0

        pat = self._pats.get(self._active, self._pats["default"])
        if not pat:
            return (0, 0)

        # Advance pattern index on real-time clock
        elapsed = now - self._last_fire
        new_idx = int(elapsed / self._SHOT_INTERVAL)
        if new_idx > self._idx:
            self._idx = min(new_idx, len(pat) - 1)

        dx, dy = pat[self._idx]

        # Convert pattern units → real pixels via strength and Windows sens
        # strength 1→0.5 px/step, strength 15→7.5 px/step
        scale    = (strength / 15.0) * 7.5 / max(get_sens_scale(), 0.5)
        raw_x    = dx * scale
        raw_y    = dy * scale

        # Sub-pixel accumulator — critical for small fractional moves
        self._rem_x += raw_x
        self._rem_y += raw_y
        ix = int(self._rem_x)
        iy = int(self._rem_y)
        self._rem_x -= ix
        self._rem_y -= iy

        return (ix, iy)

class PatternEngine:
    def __init__(self):
        self._pats={k:list(v) for k,v in DEFAULT_RECOIL_PATTERNS.items()}
        self._active="default"; self._idx=0
        self._firing=False; self._last_fire=0.0; self._reset_delay=0.30

    def set_pattern(self, name):
        if name in self._pats and name!=self._active:
            self._active=name; self._idx=0

    def add_custom(self, name, points):
        if name and points: self._pats[name]=points

    def list_patterns(self): return list(self._pats.keys())

    def tick(self, fire_held) -> tuple:
        now=time.perf_counter()
        scale=settings.get("patternscaleslider",10)/10.0
        speed=settings.get("patternspeedslider",10)/10.0
        loop=settings.get("patternloopcheckbox",True)
        if not fire_held:
            if self._firing:
                if now-self._last_fire>self._reset_delay: self._idx=0
                self._firing=False
            return (0,0)
        if not self._firing:
            self._firing=True; self._idx=0; self._last_fire=now
        pat=self._pats.get(self._active,[])
        if not pat: return (0,0)
        interval=0.10/max(speed,0.05)
        ei=int((now-self._last_fire)/interval)
        idx=(ei%len(pat)) if loop else min(ei,len(pat)-1)
        self._idx=idx; dx,dy=pat[idx]
        s=scale*get_sens_scale()
        return (int(round(dx*s)),int(round(dy*s)))

_pattern_engine = PatternEngine()
class SmoothAimer(threading.Thread):
    def __init__(self, result_q):
        super().__init__(daemon=True)
        self.result_q = result_q
        self.running = True
        self.enabled = True
        
        self._pd = PDController()
        self._recoil = RecoilEngine()
        self._validator = PersonValidator()
        self._scorer = TargetScorer()
        self._last_det_ts = 0.0
        self._last_valid_ts = 0.0
        self._last_tick_t = 0.0
        self._hk_cache = {}
        self._hk_time = 0.0
        self._valid_target = False
        self._snap_boost_active = False
        self._last_ix = 0.0
        self._last_iy = 0.0

        # Kalman
        self.dim = 6
        self.kalman_x = np.zeros((self.dim, 1))
        self.kalman_P = np.eye(self.dim) * 100.0
        self.kalman_initialized = False
        self.F = np.eye(self.dim)
        self.H = np.zeros((2, self.dim))
        self.H[0, 0] = 1.0
        self.H[1, 1] = 1.0
        self.Q_base = np.eye(self.dim) * 0.018
        self.R = np.eye(2) * 0.12
        self.last_vel = np.zeros((2, 1))
        self.last_acc = np.zeros((2, 1))
        self.history = []
        self.last_h = 0.0

    def _gk(self, key):
        return keymapping.get(key) if key else None

    def _refresh_hotkeys(self):
        now = time.perf_counter()
        if now - self._hk_time < 0.08:
            return
        self._hk_cache = {
            "aim": self._gk(settings.get("aimbothotkeycombobox")),
            "ads": self._gk(settings.get("aimbotadskeycombobox")),
            "ar": self._gk(settings.get("antirecoilhotkeycombobox")),
            "trig": self._gk(settings.get("triggerbothotkeycombobox")),
            "pat": self._gk(settings.get("patternhotkeycombobox")),
        }
        self._hk_time = now

    def _held(self, kc):
        return kc is not None and win32api.GetKeyState(kc) in (-127, -128)

    def _hard_reset(self):
        self.kalman_initialized = False
        self.history.clear()
        self.last_vel.fill(0.0)
        self.last_acc.fill(0.0)
        self.last_h = 0.0
        self._last_det_ts = self._last_valid_ts = 0.0
        self._valid_target = False
        self._snap_boost_active = False
        self._last_ix = self._last_iy = 0.0
        self._pd.reset()

    def _kalman_init(self, meas_x, meas_y, h):
        self.kalman_x[0] = meas_x
        self.kalman_x[1] = meas_y
        self.kalman_x[2:] = 0.0
        self.kalman_P = np.eye(self.dim) * 4.0
        self.kalman_initialized = True
        self.history = [(time.perf_counter(), meas_x, meas_y)]
        self.last_h = h

    def _kalman_update(self, meas_x, meas_y, h):
        if not self.kalman_initialized:
            self._kalman_init(meas_x, meas_y, h)
            return

        now = time.perf_counter()
        self.history.append((now, meas_x, meas_y))
        while self.history and now - self.history[0][0] > 0.48:
            self.history.pop(0)

        z = np.array([[meas_x], [meas_y]])
        y = z - self.H @ self.kalman_x
        S = self.H @ self.kalman_P @ self.H.T + self.R
        K = self.kalman_P @ self.H.T @ np.linalg.inv(S)
        self.kalman_x = self.kalman_x + K @ y
        self.kalman_P = (np.eye(self.dim) - K @ self.H) @ self.kalman_P

        recent_change = abs(self.kalman_x[2:4].mean())
        self.Q = self.Q_base * (1.0 + recent_change * 28.0)
        self.last_h = h

    def _kalman_predict(self, dt):
        if not self.kalman_initialized:
            return 0.0, 0.0

        self.F = np.eye(self.dim)
        self.F[0, 2] = dt
        self.F[0, 4] = 0.5 * dt * dt
        self.F[1, 3] = dt
        self.F[1, 5] = 0.5 * dt * dt
        self.F[2, 4] = dt
        self.F[3, 5] = dt

        self.kalman_x = self.F @ self.kalman_x
        self.kalman_P = self.F @ self.kalman_P @ self.F.T + self.Q

        px = float(self.kalman_x[0, 0])
        py = float(self.kalman_x[1, 0])

        vel = self.kalman_x[2:4]
        acc = self.kalman_x[4:6]

        distance_factor = max(1.0, 450.0 / (self.last_h + 1.0))

        if len(self.history) >= 5:
            dt_hist = self.history[-1][0] - self.history[-4][0]
            if dt_hist > 0:
                jerk_x = (vel[0, 0] - self.last_vel[0, 0]) / dt_hist
                jerk_y = (vel[1, 0] - self.last_vel[1, 0]) / dt_hist
                px += 0.38 * jerk_x * dt * dt * distance_factor
                py += 0.38 * jerk_y * dt * dt * distance_factor

        if len(self.history) >= 8:
            dxs = [self.history[i+1][1] - self.history[i][1] for i in range(len(self.history)-1)]
            if abs(np.mean(dxs)) > 3.5 and abs(np.std(dxs)) < 4.2:
                px += np.mean(dxs[-4:]) * 1.05 * distance_factor

        self.last_vel = vel.copy()
        self.last_acc = acc.copy()
        return px, py

    def run(self):
        INTERVAL = 0.001
        sc = screenshotcentre
        last_r = None
        self._last_tick_t = time.perf_counter()

        while self.running:
            t0 = time.perf_counter()
            while True:
                try:
                    last_r = self.result_q.get_nowait()
                except queue.Empty:
                    break

            if not loaded:
                time.sleep(0.01)
                continue

            self._refresh_hotkeys()
            hk = self._hk_cache

            aim_held = self._held(hk.get("aim"))
            ads_held = self._held(hk.get("ads"))
            ar_held = self._held(hk.get("ar"))
            trig_held = self._held(hk.get("trig"))
            pat_held = self._held(hk.get("pat"))

            aimbot_on = settings.get("aimbotcheckbox", False)
            conf_thresh = settings.get("aiconfidenceslider", 35) / 100.0
            stickiness = settings.get("stickinessslider", 50) / 100.0
            coast_time = 9.0 + stickiness * 8.0   # extrem langes Kleben

            pred_str = settings.get("predictionstrengthslider", 50) / 100.0
            self._pd.configure(
                settings.get("adsstrengthslider" if ads_held else "regularstrengthslider", 120 if ads_held else 150),
                settings.get("smoothnessslider", 40),
                settings.get("speedmultiplierslider", 25)
            )

            now = time.perf_counter()
            dt = now - self._last_tick_t
            self._last_tick_t = now

            is_fresh = (last_r is not None and last_r.timestamp != self._last_det_ts and now - last_r.timestamp < 0.20)

            if is_fresh:
                self._last_det_ts = last_r.timestamp
                if last_r.has_detection:
                    bx1, by1, bx2, by2 = last_r.box
                    if (self._validator.is_person(bx1, by1, bx2, by2, last_r.conf) and last_r.conf >= conf_thresh):
                        h = by2 - by1
                        bone = settings.get("aimboneradiobutton", "Head")
                        bdiv = {"Head": 2.5, "Neck": 3.0, "Torso": 5.0}.get(bone, settings.get("customoffsetslider", 2.5))
                        aim_x = (bx1 + bx2) / 2.0
                        aim_y = (by1 + by2) / 2.0 - h / bdiv

                        was_new_target = not self.kalman_initialized
                        if was_new_target:
                            self._snap_boost_active = True

                        self._kalman_update(aim_x, aim_y, h)
                        self._last_valid_ts = now
                        self._valid_target = True
                    else:
                        self._hard_reset()
                else:
                    self._hard_reset()

            if self._valid_target and now - self._last_valid_ts > coast_time:
                self._hard_reset()

            if (aimbot_on and self.enabled and (aim_held or ads_held) and
                    self._valid_target and self.kalman_initialized):
                distance_factor = max(1.0, 420.0 / (self.last_h + 1.0))
                pred_multiplier = 1.0 + pred_str * (420.0 if self._snap_boost_active else 320.0) * distance_factor

                px, py = self._kalman_predict(dt * pred_multiplier)
                in_fov = True
                if in_fov:
                    ex = px - sc[0]
                    ey = py - sc[1]
                    ix, iy = self._pd.tick(ex, ey, dt)

                    error_mag = (ex**2 + ey**2)**0.5
                    vel_mag = float(np.linalg.norm(self.kalman_x[2:4]))

                    # === STRIKTER, EHRGEIZIGER + STABILER LOCK ===
                    if error_mag > 140 or self.last_h < 70:
                        boost = 38.0          # sehr stark auf Ferne
                        alpha = 0.79
                    elif error_mag > 55:
                        boost = 33.0
                        alpha = 0.74
                    elif error_mag > 15:
                        boost = 19.0
                        alpha = 0.71
                    else:  # ultra nah = extrem klebrig + stabil
                        boost = 1.22          # sanft, aber konstant
                        alpha = 0.99998       # sehr starke Dämpfung

                    if vel_mag > 18.0:
                        boost *= 1.45

                    ix *= boost
                    iy *= boost

                    # Starke Anti-Schaukel Dämpfung
                    ix = ix * alpha + self._last_ix * (1 - alpha)
                    iy = iy * alpha + self._last_iy * (1 - alpha)
                    self._last_ix = ix
                    self._last_iy = iy

                    # Große Deadzone gegen Wegrutschen
                    if abs(ix) < 0.65:
                        ix = 0.0
                    if abs(iy) < 0.65:
                        iy = 0.0
                    ix = max(min(ix, 9.0), -9.0)
                    iy = max(min(iy, 9.0), -9.0)

                    if self._snap_boost_active:
                        self._snap_boost_active = False

                    if ix != 0 or iy != 0:
                        mousemove(ix, iy)
                        if _aim_logger.enabled:
                            _aim_logger.log(px, py, sc[0], sc[1], ex, ey, ix, iy,
                                            last_r.conf if last_r else 0.0)
                else:
                    self._pd.reset()
            elif not (aim_held or ads_held):
                self._pd.reset()
                if self._last_valid_ts > 0 and now - self._last_valid_ts > 1.5:
                    self._hard_reset()

            # Trigger, Recoil, Pattern unverändert
            if (settings.get("triggerbotcheckbox", False) and trig_held and
                    last_r is not None and last_r.has_detection and self._valid_target):
                bx1, by1, bx2, by2 = last_r.box
                if bx1 <= sc[0] <= bx2 and by1 <= sc[1] <= by2:
                    mouseclick()

            if settings.get("antirecoilcheckbox", False) and ar_held:
                fire_held = win32api.GetKeyState(0x01) in (-127, -128)
                ar_s = settings.get("antirecoilstrengthslider", 1) / 15.0
                self._recoil.set_pattern(settings.get("antirecoilpatterncombo", "default"))
                rdx, rdy = self._recoil.tick(fire_held, ar_s)
                if rdx != 0 or rdy != 0:
                    mousemove(rdx, rdy)

            if settings.get("patterncheckbox", False) and pat_held:
                fire_held = win32api.GetKeyState(0x01) in (-127, -128)
                pat_name = settings.get("patternselect", "default")
                if pat_name != _pattern_engine._active:
                    _pattern_engine.set_pattern(pat_name)
                pdx, pdy = _pattern_engine.tick(fire_held)
                if pdx != 0 or pdy != 0:
                    mousemove(pdx, pdy)
            elif not pat_held:
                _pattern_engine.tick(False)

            elapsed = time.perf_counter() - t0
            sleep = INTERVAL - elapsed
            if sleep > 0.0005:
                time.sleep(sleep - 0.0004)
            while time.perf_counter() - t0 < INTERVAL:
                pass

    def stop(self):
        self.running = False

class Visuals(QMainWindow):
    def __init__(self):
        super().__init__()
        self.detectionresults=[]
        self._win_title=generaterandomstring()
        self.setWindowTitle(self._win_title)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TranslucentBackground)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_ShowWithoutActivating)
        self.setAttribute(QtCore.Qt.WidgetAttribute.WA_TransparentForMouseEvents,True)
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            |QtCore.Qt.WindowType.WindowStaysOnTopHint
            |QtCore.Qt.WindowType.WindowDoesNotAcceptFocus
            |QtCore.Qt.WindowType.Tool)
        self.setGeometry(0,0,MONITOR_WIDTH,MONITOR_HEIGHT)

    def paintEvent(self,event):
        Xoff=int(MONITOR_WIDTH/2-FRAME_WIDTH); Yoff=int(MONITOR_HEIGHT/2-FRAME_HEIGHT)
        hmx=MONITOR_WIDTH//2; hmy=MONITOR_HEIGHT//2
        painter=QPainter(self); painter.setOpacity(1)

        def qc(key,default=(255,255,255)):
            v=settings.get(key)
            if v and isinstance(v,(list,tuple)) and len(v)>=3:
                try: return QColor(*[int(c) for c in v[:3]])
                except: pass
            return QColor(*default)

        def chk(key,default=False): return settings.get(key,default)

        if chk("drawframesquarecheckbox"):
            painter.setPen(QPen(QtCore.Qt.GlobalColor.white,1))
            painter.drawRect(hmx-FRAME_SIZE//2,hmy-FRAME_SIZE//2,FRAME_SIZE,FRAME_SIZE)

        if chk("drawfovcirclecheckbox"):
            fov_r=settings.get("adsfovslider" if ads() else "regularfovslider",80)
            col=qc("fovcirclecolorpicker",(255,255,255))
            painter.setRenderHint(QPainter.RenderHint.Antialiasing,True)
            if chk("drawcircleoutlinescheckbox"):
                painter.setPen(QPen(QtCore.Qt.GlobalColor.black,3))
                painter.drawEllipse(hmx-fov_r,hmy-fov_r,fov_r*2,fov_r*2)
            painter.setPen(QPen(col,1))
            painter.drawEllipse(hmx-fov_r,hmy-fov_r,fov_r*2,fov_r*2)

        if chk("drawcrosshaircheckbox"):
            sz=settings.get("crosshairsizeslider",6); col=qc("crosshaircolorpicker",(255,255,255))
            painter.setRenderHint(QPainter.RenderHint.Antialiasing,False)
            painter.setPen(QPen(col,1))
            painter.drawLine(hmx-sz,hmy,hmx+sz,hmy); painter.drawLine(hmx,hmy-sz,hmx,hmy+sz)

        bone=settings.get("aimboneradiobutton","Head")
        bdiv={"Head":2.5,"Neck":3.0,"Torso":5.0}.get(bone,settings.get("customoffsetslider",2))
        draw_boxes=chk("drawtargetboxescheckbox"); draw_tracers=chk("drawtargettracerscheckbox")

        for det in self.detectionresults:
            x1,y1,x2,y2=det["bbox"]
            if draw_boxes:
                col=qc("targetboxescolorpicker",(255,255,255))
                btype=settings.get("targetboxestyperadiobutton","Regular Box")
                painter.setRenderHint(QPainter.RenderHint.Antialiasing,False)
                def draw_box_shape(pen):
                    painter.setPen(pen)
                    if btype=="Regular Box":
                        painter.drawRect(x1+Xoff,y1+Yoff,x2-x1,y2-y1)
                    else:
                        bw=x2-x1; bh=y2-y1; cl=int(min(bw,bh)*0.25)
                        for ax,ay,sx,sy in [(x1+Xoff,y1+Yoff,1,1),(x2+Xoff,y1+Yoff,-1,1),
                                            (x1+Xoff,y2+Yoff,1,-1),(x2+Xoff,y2+Yoff,-1,-1)]:
                            painter.drawLine(ax,ay,ax+sx*cl,ay); painter.drawLine(ax,ay,ax,ay+sy*cl)
                if chk("drawboxoutlinescheckbox"): draw_box_shape(QPen(QtCore.Qt.GlobalColor.black,3))
                draw_box_shape(QPen(col,1))
            if draw_tracers:
                col=qc("targettracerscolorpicker",(255,255,255))
                t_from=settings.get("targettracersfromradiobutton","Screen Centre")
                t_to=settings.get("targettracerstoradiobutton","Aim Bone")
                spx=hmx; spy=hmy if t_from=="Screen Centre" else MONITOR_HEIGHT
                epx=int((x1+x2)/2)+Xoff
                epy=(int((y1+y2)/2-(y2-y1)/bdiv)+Yoff) if t_to=="Aim Bone" else (y2+Yoff)
                painter.setRenderHint(QPainter.RenderHint.Antialiasing,True)
                if chk("drawtraceroutlinescheckbox"):
                    painter.setPen(QPen(QtCore.Qt.GlobalColor.black,3))
                    painter.drawLine(spx,spy,epx,epy)
                painter.setPen(QPen(col,1)); painter.drawLine(spx,spy,epx,epy)
        painter.end()


class PreviewWindow(QMainWindow):
    def __init__(self, result_q):
        super().__init__()
        self._result_q  = result_q
        self._last_frame: 'np.ndarray | None' = None
        self._last_det   = None

        WIN_W, WIN_H = FRAME_SIZE, FRAME_SIZE   # match capture size
        self.setWindowTitle("JONNY AI — Preview")
        self.setFixedSize(WIN_W, WIN_H)
        self.setWindowFlags(
            QtCore.Qt.WindowType.WindowStaysOnTopHint
            | QtCore.Qt.WindowType.Tool
        )
        self.setStyleSheet("QMainWindow{background:#000;}")
        # Central widget for painting
        self._canvas = _PreviewCanvas(self)
        self.setCentralWidget(self._canvas)

        # Update at ~30 fps
        self._timer = QTimer()
        self._timer.timeout.connect(self._refresh)
        self._timer.start(33)

    def set_frame(self, frame):
        """Called from mainloop with latest raw frame (BGR np array)."""
        self._last_frame = frame

    def set_detection(self, det):
        self._last_det = det

    def _refresh(self):
        self._canvas.frame     = self._last_frame
        self._canvas.detection = self._last_det
        self._canvas.update()

    def closeEvent(self, e):
        self._timer.stop()
        e.accept()


class _PreviewCanvas(QWidget):
    """Inner widget that actually paints frame + detections."""
    def __init__(self, parent):
        super().__init__(parent)
        self.frame     = None
        self.detection = None

    def paintEvent(self, event):
        from PyQt6.QtGui import QImage, QPixmap
        p = QPainter(self)
        W, H = self.width(), self.height()

        # ── Draw raw camera frame ────────────────────────────────
        if self.frame is not None:
            try:
                frm = self.frame
                fh, fw = frm.shape[:2]
                # Convert BGR→RGB for Qt
                rgb = frm[:, :, ::-1].copy()
                img = QImage(rgb.data, fw, fh, fw * 3, QImage.Format.Format_RGB888)
                pix = QPixmap.fromImage(img).scaled(
                    W, H,
                    QtCore.Qt.AspectRatioMode.KeepAspectRatioByExpanding,
                    QtCore.Qt.TransformationMode.SmoothTransformation
                )
                p.drawPixmap(0, 0, pix)
            except Exception:
                p.fillRect(0, 0, W, H, QColor(10, 10, 14))
        else:
            p.fillRect(0, 0, W, H, QColor(10, 10, 14))
            p.setPen(QPen(QColor(80, 80, 90), 1))
            p.drawText(W // 2 - 60, H // 2, "Waiting for frame…")

        cx, cy = W // 2, H // 2

        # ── Crosshair ───────────────────────────────────────────
        if settings.get("drawcrosshaircheckbox", True):
            sz  = settings.get("crosshairsizeslider", 6)
            col = self._qcol("crosshaircolorpicker")
            p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
            p.setPen(QPen(col, 1))
            p.drawLine(cx - sz, cy, cx + sz, cy)
            p.drawLine(cx, cy - sz, cx, cy + sz)

        # ── FOV circle ──────────────────────────────────────────
        if settings.get("drawfovcirclecheckbox", True):
            fov_r_raw = settings.get("adsfovslider" if ads() else "regularfovslider", 80)
            # Scale from FRAME_SIZE coordinate space to canvas pixel space
            scale_factor = W / FRAME_SIZE
            fov_r = int(fov_r_raw * scale_factor)
            col   = self._qcol("fovcirclecolorpicker")
            p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            if settings.get("drawcircleoutlinescheckbox", False):
                p.setPen(QPen(QColor(0, 0, 0), 3))
                p.drawEllipse(cx - fov_r, cy - fov_r, fov_r * 2, fov_r * 2)
            p.setPen(QPen(col, 1))
            p.drawEllipse(cx - fov_r, cy - fov_r, fov_r * 2, fov_r * 2)

        # ── Detection boxes & aimpoint ──────────────────────────
        det = self.detection
        if (det is not None and det.has_detection
                and time.perf_counter() - det.timestamp < 0.15):
            # Detection coords are in FRAME_SIZE space — scale to canvas
            sf = W / FRAME_SIZE
            x1 = int(det.box[0] * sf); y1 = int(det.box[1] * sf)
            x2 = int(det.box[2] * sf); y2 = int(det.box[3] * sf)
            bone = settings.get("aimboneradiobutton", "Head")
            bdiv = {"Head": 2.5, "Neck": 3.0, "Torso": 5.0}.get(
                bone, settings.get("customoffsetslider", 2.5))
            aim_x = int((x1 + x2) / 2)
            aim_y = int((y1 + y2) / 2 - (y2 - y1) / bdiv)

            if settings.get("drawtargetboxescheckbox", True):
                col   = self._qcol("targetboxescolorpicker")
                btype = settings.get("targetboxestyperadiobutton", "Regular Box")
                p.setRenderHint(QPainter.RenderHint.Antialiasing, False)
                if settings.get("drawboxoutlinescheckbox", False):
                    p.setPen(QPen(QColor(0, 0, 0), 3))
                    self._draw_box(p, x1, y1, x2, y2, btype)
                p.setPen(QPen(col, 1))
                self._draw_box(p, x1, y1, x2, y2, btype)

            if settings.get("drawtargettracerscheckbox", False):
                col  = self._qcol("targettracerscolorpicker")
                p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
                if settings.get("drawtraceroutlinescheckbox", False):
                    p.setPen(QPen(QColor(0, 0, 0), 3))
                    p.drawLine(cx, cy, aim_x, aim_y)
                p.setPen(QPen(col, 1))
                p.drawLine(cx, cy, aim_x, aim_y)

            # Draw bright aim-point dot
            p.setRenderHint(QPainter.RenderHint.Antialiasing, True)
            p.setPen(QPen(QColor(255, 80, 80), 2))
            p.setBrush(QColor(255, 80, 80, 180))
            p.drawEllipse(aim_x - 4, aim_y - 4, 8, 8)
            p.setBrush(QtCore.Qt.BrushStyle.NoBrush)

            # Confidence label
            p.setPen(QPen(QColor(255, 255, 255, 180), 1))
            p.drawText(x1 + 2, y1 - 4, f"{det.conf * 100:.0f}%")

        p.end()

    def _draw_box(self, p, x1, y1, x2, y2, btype):
        if btype == "Regular Box":
            p.drawRect(x1, y1, x2 - x1, y2 - y1)
        else:
            bw = x2 - x1; bh = y2 - y1; cl = int(min(bw, bh) * 0.25)
            for ax, ay, sx, sy in [
                (x1, y1, 1, 1), (x2, y1, -1, 1),
                (x1, y2, 1, -1), (x2, y2, -1, -1)
            ]:
                p.drawLine(ax, ay, ax + sx * cl, ay)
                p.drawLine(ax, ay, ax, ay + sy * cl)

    @staticmethod
    def _qcol(key, default=(255, 255, 255)):
        v = settings.get(key)
        if v and isinstance(v, (list, tuple)) and len(v) >= 3:
            try: return QColor(*[int(c) for c in v[:3]])
            except: pass
        return QColor(*default)


class Bridge(QObject):
    statsUpdated      = pyqtSignal(str)
    modelListUpdated  = pyqtSignal(str)
    configListUpdated = pyqtSignal(str)
    toastMessage      = pyqtSignal(str,str)

    def __init__(self,overlay:Visuals,aimer:SmoothAimer,frame_q,result_q):
        super().__init__()
        self.overlay=overlay; self.aimer=aimer
        self.frame_q=frame_q; self.result_q=result_q
        self._main_window   = None
        self._preview_win   = None

    @pyqtSlot()
    def togglePreview(self):
        """Open or close the capture preview window."""
        if self._preview_win is None or not self._preview_win.isVisible():
            if self._preview_win is None:
                self._preview_win = PreviewWindow(self.result_q)
            self._preview_win.show()
            self.toastMessage.emit("Preview window opened","info")
        else:
            self._preview_win.hide()
            self.toastMessage.emit("Preview window closed","info")

    @pyqtSlot(str,result=str)
    def getSetting(self,key):
        return json.dumps(settings.get(key))

    @pyqtSlot(str,str)
    def setSetting(self,key,value):
        try:
            val=json.loads(value)
            if key=='__discord_open__':
                import webbrowser
                webbrowser.open(str(val))
                return
            settings.set(key,val)
            if key=="targetfpsslider":
                global _target_fps_global
                _target_fps_global=int(val)
            elif key=="patternselect":
                _pattern_engine.set_pattern(str(val))
            elif key=="patterncustom":
                try:
                    pts=[[int(x) for x in p.split(",")] for p in str(val).split(";") if "," in p]
                    if pts: _pattern_engine.add_custom("custom",pts)
                except: pass
        except Exception as e:
            print(f"[Bridge] setSetting error: {e}")

    @pyqtSlot(result=str)
    def getAllSettings(self):
        return json.dumps(settings.get_all())

    @pyqtSlot(result=str)
    def getModelList(self):
        cwd=os.getcwd()
        models=sorted([f for f in os.listdir(cwd)
                        if f.lower().endswith(".onnx") and os.path.isfile(os.path.join(cwd,f))])
        return json.dumps(models if models else ["best.onnx"])

    @pyqtSlot(str)
    def loadModel(self,model_filename):
        global loaded,session
        model_path=os.path.join(os.getcwd(),model_filename)
        if not os.path.isfile(model_path):
            self.toastMessage.emit(f"Model not found: {model_filename}","error"); return
        self.toastMessage.emit(f"Loading {model_filename}...","info")
        loaded=False
        def _do_load():
            """
            Two-phase loading strategy to avoid freezing with TensorRT:

            Phase 1 (fast, ~1-3s): Load with CUDA or CPU → set loaded=True
                                   so the program starts immediately.
            Phase 2 (background):  If TRT is available, compile the TRT engine
                                   (can take 30-120s on first run) in a
                                   separate thread and hot-swap the session
                                   when done — zero disruption to the running
                                   aimbot.

            This means:
            - Program starts fast regardless of TRT compilation time.
            - After TRT engine is built, it auto-upgrades to TRT+CUDA.
            - On subsequent runs the TRT cache is reused (seconds).
            """
            global loaded,session,_active_provider
            import io as _io

            def _silent_make(providers):
                """Create InferenceSession with stderr suppressed."""
                old=sys.stderr; sys.stderr=_io.StringIO()
                try:
                    s=ort.InferenceSession(model_path,
                                           sess_options=opts,
                                           providers=providers)
                finally:
                    sys.stderr=old
                return s

            try:
                # ── Suppress DLL spam during preload ──
                old_err=sys.stderr; sys.stderr=_io.StringIO()
                try:
                    try: ort.preload_dlls(cuda=True,cudnn=True)
                    except Exception: pass
                finally:
                    sys.stderr=old_err

                opts=ort.SessionOptions()
                opts.graph_optimization_level=ort.GraphOptimizationLevel.ORT_ENABLE_ALL
                opts.execution_mode=ort.ExecutionMode.ORT_SEQUENTIAL
                opts.inter_op_num_threads=1
                opts.intra_op_num_threads=1
                opts.log_severity_level=4   # silent — errors show in toast

                avail=ort.get_available_providers()
                print(f"[ORT] Available providers: {avail}")

                trt_available = "TensorrtExecutionProvider" in avail
                cuda_available = "CUDAExecutionProvider" in avail

                phase1_sess = None
                phase1_name = "CPU"
                load_err    = ""

                # ── PHASE 1: Quick start via CUDA ──────────────────────────
                # If TRT cache already exists for this model → load TRT directly
                # (cached TRT loads in ~2s, same as CUDA)
                trt_cache_file = os.path.join("./trt_cache",
                    os.path.basename(model_path).replace(".onnx","") + "_fp16.engine")
                trt_cached = os.path.isfile(trt_cache_file)

                if trt_available and trt_cached:
                    # Cache hit — load TRT immediately, it's fast
                    print("[ORT] TRT engine cache found — loading directly")
                    self.toastMessage.emit(f"Loading {model_filename} via TRT cache…","info")
                    try:
                        os.makedirs("./trt_cache",exist_ok=True)
                        trt_opts={
                            "trt_engine_cache_enable":True,
                            "trt_engine_cache_path":"./trt_cache",
                            "trt_fp16_enable":True,
                            "trt_max_workspace_size":2147483648,
                        }
                        s=_silent_make([
                            ("TensorrtExecutionProvider",trt_opts),
                            ("CUDAExecutionProvider",{}),
                            "CPUExecutionProvider"
                        ])
                        active=s.get_providers()
                        if "TensorrtExecutionProvider" in active:
                            phase1_sess=s; phase1_name="TensorRT+CUDA"
                            print("[ORT] Phase1: TRT+CUDA (cached)")
                        elif "CUDAExecutionProvider" in active:
                            phase1_sess=s; phase1_name="CUDA"
                    except Exception as e:
                        load_err=f"TRT cache load failed: {e}"
                        print(f"[ORT] {load_err}")

                # If no TRT cache or TRT cache load failed → use CUDA for Phase 1
                if phase1_sess is None and cuda_available:
                    self.toastMessage.emit(f"Loading {model_filename} via CUDA…","info")
                    try:
                        cuda_opts={"device_id":0,"arena_extend_strategy":"kNextPowerOfTwo",
                                   "gpu_mem_limit":4*1024*1024*1024}
                        s=_silent_make([("CUDAExecutionProvider",cuda_opts),
                                        "CPUExecutionProvider"])
                        active=s.get_providers()
                        if "CUDAExecutionProvider" in active:
                            phase1_sess=s; phase1_name="CUDA (NVIDIA)"
                            print("[ORT] Phase1: CUDA")
                        else:
                            load_err+="|CUDA inactive"
                    except Exception as e:
                        load_err+=f"|CUDA: {e}"
                        print(f"[ORT] CUDA Phase1 failed: {e}")

                # DirectML fallback (AMD/Intel)
                if phase1_sess is None and "DmlExecutionProvider" in avail:
                    self.toastMessage.emit(f"Loading {model_filename} via DirectML…","info")
                    try:
                        s=_silent_make(["DmlExecutionProvider","CPUExecutionProvider"])
                        active=s.get_providers()
                        if "DmlExecutionProvider" in active:
                            phase1_sess=s; phase1_name="DirectML (AMD/Intel)"
                            print("[ORT] Phase1: DirectML")
                    except Exception as e:
                        load_err+=f"|DML: {e}"

                # ROCm fallback
                if phase1_sess is None and "ROCMExecutionProvider" in avail:
                    try:
                        s=_silent_make(["ROCMExecutionProvider","CPUExecutionProvider"])
                        if "ROCMExecutionProvider" in s.get_providers():
                            phase1_sess=s; phase1_name="ROCm (AMD)"
                    except Exception as e:
                        load_err+=f"|ROCm: {e}"

                # CPU last resort
                if phase1_sess is None:
                    self.toastMessage.emit(f"Loading {model_filename} via CPU…","info")
                    phase1_sess=_silent_make(["CPUExecutionProvider"])
                    phase1_name="CPU"
                    print("[ORT] Phase1: CPU (no GPU available)")

                # ── Activate Phase 1 session — program starts NOW ──
                _active_provider=phase1_name
                session=phase1_sess
                loaded=True
                sz_mb=os.path.getsize(model_path)/1024/1024
                self.toastMessage.emit(
                    f"Loaded: {model_filename} ({sz_mb:.1f}MB) [{phase1_name}]","success")

                if phase1_name=="CPU":
                    hint="No GPU provider active."
                    if load_err: hint+=f" ({load_err[:100]})"
                    hint+=" NVIDIA: pip install onnxruntime-gpu | AMD: pip install onnxruntime-directml"
                    self.toastMessage.emit(hint,"info")

                # ── PHASE 2: TRT background compilation ───────────────────
                # Only run if TRT is available AND we didn't already use it
                if trt_available and "TensorRT" not in phase1_name:
                    def _compile_trt():
                        global session,_active_provider
                        print("[ORT] Phase2: Starting TRT engine compilation (background)…")
                        print("[ORT] This takes 30-120s on first run. The aimbot runs normally meanwhile.")
                        self.toastMessage.emit("TRT compiling in background (first run only)…","info")
                        try:
                            # Use a separate SessionOptions for TRT
                            trt_sess_opts=ort.SessionOptions()
                            trt_sess_opts.graph_optimization_level=ort.GraphOptimizationLevel.ORT_ENABLE_ALL
                            trt_sess_opts.execution_mode=ort.ExecutionMode.ORT_SEQUENTIAL
                            trt_sess_opts.inter_op_num_threads=1
                            trt_sess_opts.intra_op_num_threads=1
                            trt_sess_opts.log_severity_level=4
                            os.makedirs("./trt_cache",exist_ok=True)
                            trt_opts={
                                "trt_engine_cache_enable":True,
                                "trt_engine_cache_path":"./trt_cache",
                                "trt_fp16_enable":True,
                                "trt_max_workspace_size":2147483648,
                            }
                            old=sys.stderr; sys.stderr=_io.StringIO()
                            try:
                                trt_sess=ort.InferenceSession(
                                    model_path,
                                    sess_options=trt_sess_opts,
                                    providers=[
                                        ("TensorrtExecutionProvider",trt_opts),
                                        ("CUDAExecutionProvider",{}),
                                        "CPUExecutionProvider"
                                    ]
                                )
                            finally:
                                sys.stderr=old
                            active=trt_sess.get_providers()
                            if "TensorrtExecutionProvider" in active:
                                # Hot-swap: replace session atomically
                                session=trt_sess
                                _active_provider="TensorRT+CUDA"
                                print("[ORT] Phase2: TRT engine ready — hot-swapped to TensorRT+CUDA")
                                self.toastMessage.emit("Upgraded to TensorRT+CUDA ✓","success")
                            else:
                                print(f"[ORT] Phase2: TRT compiled but not in active providers: {active}")
                        except Exception as e:
                            print(f"[ORT] Phase2 TRT compilation failed: {e}")
                            self.toastMessage.emit(f"TRT compile failed: {str(e)[:80]}","error")

                    threading.Thread(target=_compile_trt,daemon=True).start()

            except Exception as e:
                loaded=True
                self.toastMessage.emit(f"Load error: {e}","error")
                print(f"[ORT] Fatal load error: {e}")
        threading.Thread(target=_do_load,daemon=True).start()

    @pyqtSlot(result=str)
    def getConfigList(self):
        p=os.path.join(os.getcwd(),"extra/configs"); os.makedirs(p,exist_ok=True)
        configs=[f for f in os.listdir(p)
                 if os.path.isfile(os.path.join(p,f)) and f!="!loadersettings.json"]
        return json.dumps(configs)

    @pyqtSlot(str)
    def loadConfig(self,name):
        path=os.path.join(os.getcwd(),"extra/configs",name)
        if not os.path.isfile(path):
            self.toastMessage.emit("Config not found.","error"); return
        try:
            with open(path) as f: cfg=json.load(f)
            settings.load_from_dict(cfg)
            self.toastMessage.emit(f"Config loaded: {name}","success")
        except Exception as e:
            self.toastMessage.emit(f"Load error: {e}","error")

    @pyqtSlot(str)
    def saveConfig(self,name):
        if not name: self.toastMessage.emit("No config selected.","error"); return
        p=os.path.join(os.getcwd(),"extra/configs"); os.makedirs(p,exist_ok=True)
        with open(os.path.join(p,name),"w") as f: json.dump(settings.get_all(),f,indent=4)
        self.toastMessage.emit(f"Saved: {name}","success")

    @pyqtSlot(str)
    def createConfig(self,name):
        if not name: self.toastMessage.emit("Enter a config name.","error"); return
        if not name.endswith(".json"): name+=".json"
        p=os.path.join(os.getcwd(),"extra/configs"); os.makedirs(p,exist_ok=True)
        with open(os.path.join(p,name),"w") as f: json.dump(settings.get_all(),f,indent=4)
        self.configListUpdated.emit(self.getConfigList())
        self.toastMessage.emit(f"Created: {name}","success")

    @pyqtSlot(str,str)
    def startLogging(self,path,_=None):
        if not path: path="aim_log.csv"
        try: _aim_logger.start(path); self.toastMessage.emit(f"Logging → {path}","success")
        except Exception as e: self.toastMessage.emit(f"Log error: {e}","error")

    @pyqtSlot()
    def stopLogging(self):
        _aim_logger.stop(); self.toastMessage.emit("Logging stopped.","info")

    @pyqtSlot()
    def hideConsole(self):
        ctypes.windll.user32.ShowWindow(ctypes.windll.kernel32.GetConsoleWindow(),0)

    @pyqtSlot(int,int)
    def moveWindow(self,dx,dy):
        w = getattr(self, '_main_window', None)
        if w is not None:
            p = w.pos(); w.move(p.x()+dx, p.y()+dy)

    @pyqtSlot()
    def minimizeWindow(self):
        w = getattr(self, '_main_window', None)
        if w is not None: w.showMinimized()

    @pyqtSlot()
    def closeWindow(self):
        w = getattr(self, '_main_window', None)
        if w is not None: w.hide()

    def set_main_window(self, win):
        self._main_window = win

    @pyqtSlot(result=str)
    def getStats(self):
        global fps_val
        try:
            r=self.result_q.queue[-1]
            has_target=r.has_detection and time.perf_counter()-r.timestamp<0.12
            conf=r.conf if r.has_detection else 0.0
        except (IndexError,AttributeError):
            has_target=False; conf=0.0
        cap_mode="bettercam" if _BETTERCAM_AVAILABLE else "mss"
        return json.dumps({
            "fps":int(fps_val),"loaded":loaded,"has_target":has_target,
            "confidence":round(conf*100,1),"model":settings.get("modelcombobox","—"),
            "provider":_active_provider,"capture":cap_mode,
        })


GUI_W=720; GUI_H=460

# ──────────────────────────────────────────────────────────────────
#  KEY WINDOW — shown before the main GUI, blocks until auth passes
# ──────────────────────────────────────────────────────────────────
class KeyWindow(QMainWindow):
    """Standalone login/key-entry window. Closes itself on success."""

    auth_success = pyqtSignal()

    def __init__(self):
        super().__init__()
        self.setWindowTitle("JONNY AI — Activation")
        self.setFixedSize(380, 240)
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            | QtCore.Qt.WindowType.WindowStaysOnTopHint
            | QtCore.Qt.WindowType.Tool
        )
        self.setStyleSheet("QMainWindow{background:#111114;}")

        self._hwid = _get_hwid()
        self._drag_pos = None

        central = QWidget(); self.setCentralWidget(central)
        lay = QVBoxLayout(central)
        lay.setContentsMargins(0, 0, 0, 0)

        self._web = QWebEngineView()
        self._web.setStyleSheet("background:transparent;")
        lay.addWidget(self._web)

        self._channel = QWebChannel()
        self._bridge  = _KeyBridge(self)
        self._channel.registerObject("kb", self._bridge)
        self._web.page().setWebChannel(self._channel)
        self._web.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.NoContextMenu)
        self._web.setHtml(self._build_html(), QUrl("about:blank"))

        screen = QApplication.primaryScreen().geometry()
        self.move(screen.width()//2 - 190, screen.height()//2 - 120)

    def _build_html(self) -> str:
        return f"""<!DOCTYPE html>
<html><head><meta charset="UTF-8">
<script src="qrc:///qtwebchannel/qwebchannel.js"></script>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;600;700;800;900&display=swap" rel="stylesheet">
<style>
*{{margin:0;padding:0;box-sizing:border-box;}}
body{{
  width:380px;height:240px;overflow:hidden;
  background:#0e0e11;
  font-family:'Inter',system-ui,sans-serif;color:#f0f0f5;
  display:flex;flex-direction:column;
  user-select:none;
}}
/* ── TITLEBAR ── */
.tb{{
  height:34px;background:#0e0e11;display:flex;align-items:center;
  padding:0 12px;border-bottom:1px solid rgba(255,255,255,0.06);
  cursor:grab;flex-shrink:0;
}}
.tb:active{{cursor:grabbing;}}
.logo{{
  font-size:14px;font-weight:900;color:#fff;letter-spacing:-0.04em;
  text-shadow:0 0 14px rgba(255,255,255,0.45);
}}
.tb-x{{
  margin-left:auto;width:20px;height:20px;border-radius:4px;
  border:none;background:transparent;cursor:pointer;
  font-size:9px;color:#505060;display:flex;align-items:center;
  justify-content:center;transition:.12s;
}}
.tb-x:hover{{background:rgba(255,68,85,0.15);color:#ff4455;}}
/* ── BODY ── */
.body{{
  flex:1;display:flex;flex-direction:column;align-items:center;
  justify-content:center;padding:20px 32px;gap:14px;
}}
/* ── INPUT ── */
.key-inp{{
  width:100%;padding:12px 14px;
  background:#1a1a20;border:1px solid rgba(255,255,255,0.08);
  border-radius:8px;color:#fff;font-size:13px;font-weight:600;
  outline:none;font-family:'Courier New',mono;letter-spacing:0.06em;
  transition:border-color .15s;text-align:center;
}}
.key-inp:focus{{border-color:rgba(255,255,255,0.22);}}
.key-inp.err{{
  border-color:rgba(255,68,85,0.55);
  animation:shake .28s ease;
}}
.key-inp.ok{{border-color:rgba(61,255,128,0.45);}}
@keyframes shake{{
  0%,100%{{transform:translateX(0)}}
  20%{{transform:translateX(-5px)}}
  60%{{transform:translateX(5px)}}
}}
/* ── BUTTON ── */
.btn{{
  width:100%;padding:12px;border-radius:8px;border:none;
  background:#fff;color:#0e0e11;font-size:13px;font-weight:800;
  cursor:pointer;transition:all .14s;letter-spacing:-0.01em;
}}
.btn:hover{{background:#e8e8e8;transform:translateY(-1px);}}
.btn:active{{transform:scale(.97);}}
.btn:disabled{{background:#22222c;color:#505060;cursor:not-allowed;transform:none;}}
/* ── STATUS ── */
.status{{
  font-size:10.5px;font-weight:600;min-height:14px;
  text-align:center;color:#505060;
  transition:color .15s,opacity .15s;
}}
.status.err{{color:#ff4455;}}
.status.ok{{color:#3dff80;}}
/* ── SUCCESS OVERLAY (login animation) ── */
.success-overlay{{
  position:fixed;inset:0;
  display:flex;align-items:center;justify-content:center;
  background:#0e0e11;
  opacity:0;pointer-events:none;
  transition:opacity .25s ease;
  flex-direction:column;gap:12px;z-index:99;
}}
.success-overlay.show{{opacity:1;pointer-events:all;}}
.check-wrap{{
  width:56px;height:56px;border-radius:50%;
  border:2px solid rgba(61,255,128,0.25);
  display:flex;align-items:center;justify-content:center;
  animation:pulse-ring 1.2s ease infinite;
}}
@keyframes pulse-ring{{
  0%{{box-shadow:0 0 0 0 rgba(61,255,128,0.3);}}
  70%{{box-shadow:0 0 0 12px rgba(61,255,128,0);}}
  100%{{box-shadow:0 0 0 0 rgba(61,255,128,0);}}
}}
.check-icon{{
  font-size:22px;color:#3dff80;
  animation:pop-in .35s cubic-bezier(.34,1.56,.64,1) .1s both;
}}
@keyframes pop-in{{
  from{{transform:scale(0);opacity:0;}}
  to{{transform:scale(1);opacity:1;}}
}}
.success-lbl{{
  font-size:11px;font-weight:700;color:#3dff80;
  letter-spacing:0.04em;opacity:0;
  animation:fade-up .3s ease .4s both;
}}
@keyframes fade-up{{
  from{{opacity:0;transform:translateY(4px);}}
  to{{opacity:1;transform:none;}}
}}
</style>
</head>
<body>
<div class="tb" id="drag">
  <span class="logo">JNY</span>
  <button class="tb-x" onclick="if(kb)kb.close()">✕</button>
</div>
<div class="body">
  <input class="key-inp" id="kinp" placeholder="Enter license key"
    maxlength="40" spellcheck="false" autocomplete="off"
    onkeydown="if(event.key==='Enter')submit()">
  <button class="btn" id="sbtn" onclick="submit()">ACTIVATE</button>
  <div class="status" id="stat"></div>
</div>
<!-- Success animation overlay -->
<div class="success-overlay" id="sov">
  <div class="check-wrap">
    <span class="check-icon">✓</span>
  </div>
  <div class="success-lbl">ACTIVATED</div>
</div>
<script>
let kb=null;
let _drag=false,_dx=0,_dy=0;
document.getElementById('drag').addEventListener('mousedown',e=>{{
  if(e.target.tagName==='BUTTON')return;
  _drag=true;_dx=e.screenX;_dy=e.screenY;e.preventDefault();
}});
document.addEventListener('mousemove',e=>{{
  if(!_drag||!kb)return;
  const dx=e.screenX-_dx,dy=e.screenY-_dy;
  if(dx||dy){{kb.moveWin(dx,dy);_dx=e.screenX;_dy=e.screenY;}}
}});
document.addEventListener('mouseup',()=>{{_drag=false;}});

new QWebChannel(qt.webChannelTransport,ch=>{{
  kb=ch.objects.kb;
}});

function setStat(msg,cls){{
  const el=document.getElementById('stat');
  el.textContent=msg;el.className='status '+(cls||'');
}}
function setInp(cls){{
  document.getElementById('kinp').className='key-inp '+(cls||'');
}}
function showSuccess(){{
  document.getElementById('sov').classList.add('show');
  setTimeout(()=>{{if(kb)kb.proceed();}},1400);
}}
function submit(){{
  const key=document.getElementById('kinp').value.trim();
  if(!key){{setInp('err');setStat('Enter your license key','err');return;}}
  const btn=document.getElementById('sbtn');
  btn.disabled=true;btn.textContent='Checking…';
  setStat('','');setInp('');
  kb.activate(key,r=>{{
    const d=JSON.parse(r);
    btn.disabled=false;btn.textContent='ACTIVATE';
    if(d.ok){{
      setInp('ok');
      showSuccess();
    }}else{{
      setInp('err');
      setStat(d.message||'Invalid key','err');
    }}
  }});
}}
</script>
</body></html>"""
    def mousePressEvent(self, e):
        if e.button() == QtCore.Qt.MouseButton.LeftButton:
            self._drag_pos = e.globalPosition().toPoint()

    def mouseMoveEvent(self, e):
        if self._drag_pos:
            delta = e.globalPosition().toPoint() - self._drag_pos
            self.move(self.pos() + delta)
            self._drag_pos = e.globalPosition().toPoint()

    def mouseReleaseEvent(self, e):
        self._drag_pos = None


class _KeyBridge(QObject):
    """Bridge between KeyWindow JS and Python key-system logic."""

    def __init__(self, win: KeyWindow):
        super().__init__()
        self._win = win

    @pyqtSlot(int, int)
    def moveWin(self, dx, dy):
        p = self._win.pos()
        self._win.move(p.x() + dx, p.y() + dy)

    @pyqtSlot()
    def close(self):
        QApplication.quit()

    @pyqtSlot(result=str)
    def tryAutoLogin(self):
        """Try to re-validate saved key silently."""
        global _AUTHED_HWID, _AUTHED_EXPIRY
        saved = _load_saved_key()
        if not saved:
            return json.dumps({"ok": False})
        hwid = _get_hwid()
        if saved.get("hwid") != hwid:
            return json.dumps({"ok": False})
        # Re-check against server (handles expiry + ban)
        ok, msg, expiry = keysystem_validate(saved["key"], hwid)
        if ok:
            _AUTHED_HWID   = hwid
            _AUTHED_EXPIRY = expiry or saved.get("expiry", "")
            _save_key(saved["key"], hwid, _AUTHED_EXPIRY)
            # Auto-proceed after short delay
            QTimer.singleShot(1200, self._proceed_now)
            return json.dumps({"ok": True, "expiry": _AUTHED_EXPIRY})
        return json.dumps({"ok": False, "message": msg})

    @pyqtSlot(str, result=str)
    def activate(self, key: str):
        global _AUTHED_HWID, _AUTHED_EXPIRY
        hwid = _get_hwid()
        ok, msg, expiry = keysystem_validate(key.strip(), hwid)
        if ok:
            _AUTHED_HWID   = hwid
            _AUTHED_EXPIRY = expiry or ""
            _save_key(key.strip(), hwid, _AUTHED_EXPIRY)
            return json.dumps({"ok": True, "expiry": _AUTHED_EXPIRY})
        return json.dumps({"ok": False, "message": msg})

    @pyqtSlot()
    def proceed(self):
        self._proceed_now()

    def _proceed_now(self):
        self._win.hide()
        self._win.auth_success.emit()



class MainWindow(QMainWindow):
    def __init__(self,bridge:Bridge):
        super().__init__()
        self.setWindowTitle("JONNY AI")
        self.setFixedSize(GUI_W,GUI_H)
        self.setWindowFlags(
            QtCore.Qt.WindowType.FramelessWindowHint
            |QtCore.Qt.WindowType.WindowStaysOnTopHint
            |QtCore.Qt.WindowType.Tool)
        self.setStyleSheet("QMainWindow{background:#111114;}")
        central=QWidget(); self.setCentralWidget(central)
        layout=QVBoxLayout(central)
        layout.setContentsMargins(0,0,0,0); layout.setSpacing(0)
        self.webview=QWebEngineView()
        self.webview.setStyleSheet("background:transparent;")
        layout.addWidget(self.webview)
        self.channel=QWebChannel()
        self.channel.registerObject("bridge",bridge)
        self.webview.page().setWebChannel(self.channel)
        self.webview.setContextMenuPolicy(QtCore.Qt.ContextMenuPolicy.NoContextMenu)
        self.webview.setHtml(build_html(),QUrl("about:blank"))
        self._stats_timer=QTimer()
        self._stats_timer.timeout.connect(self._push_stats)
        self._stats_timer.start(500)
        self._bridge=bridge
        self._repaint_timer=QTimer()
        self._repaint_timer.timeout.connect(lambda:bridge.overlay.update())
        self._repaint_timer.start(16)
        screen=QApplication.primaryScreen().geometry()
        self.move(screen.width()//2-GUI_W//2,screen.height()//2-GUI_H//2)

    def _push_stats(self):
        self._bridge.statsUpdated.emit(self._bridge.getStats())

    def keyPressEvent(self,e):
        if e.key()==QtCore.Qt.Key.Key_Insert:
            self.setVisible(not self.isVisible())


def build_html() -> str:
    key_items_json=json.dumps(KEY_ITEMS)
    all_patterns  =json.dumps(list(DEFAULT_RECOIL_PATTERNS.keys()))

    return f"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8"><title>JONNY AI</title>
<script src="qrc:///qtwebchannel/qwebchannel.js"></script>
<link href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800;900&family=JetBrains+Mono:wght@400;500;600&display=swap" rel="stylesheet">
<style>
*{{margin:0;padding:0;box-sizing:border-box;}}
:root{{
  --bg:#111114;
  --bg2:#18181c;
  --bg3:#1e1e24;
  --bg4:#25252d;
  --bg5:#2c2c36;
  --border:rgba(255,255,255,0.07);
  --border-hi:rgba(255,255,255,0.13);
  --txt:#f0f0f5;
  --txt2:#a0a0b0;
  --txt3:#606070;
  --grn:#3dff80;
  --grn-lo:rgba(61,255,128,0.12);
  --red:#ff4455;
  --red-lo:rgba(255,68,85,0.12);
  --acc:#8b77ff;
  --acc-lo:rgba(139,119,255,0.14);
  --font:"Inter",system-ui,sans-serif;
  --mono:"JetBrains Mono","Consolas",monospace;
  --r:10px;--r-sm:7px;--r-xs:5px;
  --t-fast:.12s cubic-bezier(.4,0,.2,1);
  --t:.18s cubic-bezier(.4,0,.2,1);
  --t-slow:.28s cubic-bezier(.4,0,.2,1);
  --sb-w:138px;--tb-h:38px;
}}
html,body{{
  width:720px;height:460px;overflow:hidden;
  background:var(--bg);color:var(--txt);
  font-family:var(--font);font-size:13px;font-weight:500;
  -webkit-font-smoothing:antialiased;
}}

/* ── STARS CANVAS ── */
#stars-bg{{
  position:fixed;inset:0;pointer-events:none;z-index:0;
}}

/* ── APP SHELL ── */
.app{{
  position:relative;z-index:1;
  display:flex;flex-direction:column;
  width:720px;height:460px;
  background:transparent;
}}

/* ── TITLEBAR ── */
.tb{{
  height:var(--tb-h);
  background:var(--bg);
  display:flex;align-items:center;
  padding:0 14px;gap:10px;flex-shrink:0;
  user-select:none;
  border-bottom:1px solid var(--border);
  position:relative;z-index:2;
}}
.tb-logo{{
  font-size:19px;font-weight:900;color:#fff;
  letter-spacing:-0.05em;line-height:1;
  text-shadow:0 0 18px rgba(255,255,255,0.5);
  flex-shrink:0;
}}
.tb-drag{{flex:1;height:100%;cursor:grab;}}
.tb-drag:active{{cursor:grabbing;}}
.tb-pills{{display:flex;gap:5px;}}
.tp{{
  display:flex;align-items:center;gap:4px;
  padding:3px 9px;
  border:none;border-radius:20px;
  font-size:9px;font-family:var(--mono);color:var(--txt3);
  letter-spacing:0.05em;transition:all var(--t);
}}
.tp .d{{width:5px;height:5px;border-radius:50%;background:var(--txt3);transition:all var(--t);flex-shrink:0;}}
.tp.on{{color:var(--txt2);}}
.tp.on .d{{background:var(--grn);box-shadow:0 0 6px rgba(61,255,128,.5);}}
.tp.tgt.on .d{{background:#fff;box-shadow:0 0 6px rgba(255,255,255,.4);}}
.tp.gpu-pill.on .d{{background:var(--acc);box-shadow:0 0 6px rgba(139,119,255,.6);}}
.wc{{display:flex;gap:3px;}}
.wc-btn{{
  width:22px;height:22px;border-radius:5px;border:none;
  background:transparent;cursor:pointer;
  display:flex;align-items:center;justify-content:center;
  font-size:10px;color:var(--txt3);transition:all var(--t);
}}
.wc-btn:hover{{background:rgba(255,255,255,0.07);color:var(--txt);}}
.wc-btn.x:hover{{background:var(--red-lo);color:var(--red);}}

/* ── BODY ── */
.body{{display:flex;flex:1;overflow:hidden;position:relative;z-index:1;}}

/* ── SIDEBAR ── */
.sb{{
  width:var(--sb-w);
  background:var(--bg);

  display:flex;flex-direction:column;flex-shrink:0;
}}
.sb-nav{{flex:1;padding:5px 4px;display:flex;flex-direction:column;gap:1px;justify-content:space-evenly;}}
.nb{{
  display:flex;align-items:center;flex:1;max-height:40px;
  padding:0 11px;border-radius:6px;
  cursor:pointer;border:none;background:transparent;
  color:var(--txt3);font-family:var(--font);font-size:12px;font-weight:600;
  width:100%;text-align:left;
  transition:color var(--t),background var(--t);
  white-space:nowrap;position:relative;min-height:0;
  letter-spacing:-0.01em;
}}
.nb:hover{{background:rgba(255,255,255,0.05);color:var(--txt);}}
.nb.on{{color:#fff;font-weight:700;}}
.nb.on::before{{
  content:'';position:absolute;left:0;top:22%;bottom:22%;
  width:2px;border-radius:1px;background:#fff;
  box-shadow:0 0 7px rgba(255,255,255,0.7);
}}
.sb-foot{{
  padding:6px 6px 8px;flex-shrink:0;
}}
.discord-btn{{
  display:flex;align-items:center;gap:8px;
  padding:8px 10px;border-radius:var(--r-sm);
  background:rgba(255,255,255,0.07);border:1px solid rgba(255,255,255,0.12);
  cursor:pointer;user-select:none;
  transition:background var(--t),border-color var(--t),transform .1s;
  width:100%;
}}
.discord-btn:hover{{
  background:rgba(255,255,255,0.13);border-color:rgba(255,255,255,0.22);
}}
.discord-btn:active{{transform:scale(.97);}}
.discord-ic{{width:18px;height:18px;color:#ffffff;flex-shrink:0;}}
.discord-lbl{{
  font-size:12px;font-weight:700;color:#ffffff;
  letter-spacing:-0.01em;
}}

/* ── CONTENT ── */
.content{{flex:1;display:flex;flex-direction:column;overflow:hidden;}}
.c-head{{display:none;}}
.c-title{{font-size:13px;font-weight:700;color:#fff;display:flex;align-items:center;gap:7px;}}
.c-ic{{font-size:10px;color:var(--txt2);}}
.c-right{{margin-left:auto;}}
.fps-pill{{font-family:var(--mono);font-size:9px;color:var(--txt2);font-weight:500;}}

/* ── SCROLL ── */
.scroll{{
  flex:1;overflow-y:auto;padding:7px 9px;
  scrollbar-width:thin;scrollbar-color:rgba(255,255,255,0.1) transparent;
  scroll-behavior:smooth;
}}
.scroll::-webkit-scrollbar{{width:3px;}}
.scroll::-webkit-scrollbar-thumb{{background:rgba(255,255,255,0.1);border-radius:2px;}}

/* ── PANELS with smooth tab-switch animation ── */
.panel{{display:none;}}
.panel.on{{
  display:block;
  animation:panelIn var(--t-slow) cubic-bezier(.22,1,.36,1) both;
}}
@keyframes panelIn{{
  from{{opacity:0;transform:translateY(6px);}}
  to{{opacity:1;transform:none;}}
}}

/* ── CARDS ── */
.card{{
  background:var(--bg2);border-radius:var(--r);
  margin-bottom:5px;overflow:hidden;
  border:1px solid var(--border);
  transition:border-color var(--t);
}}
.card:hover{{border-color:var(--border-hi);}}
.ch{{
  padding:8px 12px;font-size:9.5px;font-weight:700;
  letter-spacing:0.09em;text-transform:uppercase;
  color:var(--txt2);display:flex;align-items:center;
  cursor:pointer;user-select:none;transition:color var(--t);
}}
.ch:hover{{color:var(--txt);}}
.ch .cv{{margin-left:auto;font-size:7px;color:var(--txt3);transition:transform .18s;}}
.ch.cls .cv{{transform:rotate(-90deg);}}
.cb{{padding:9px 12px;display:flex;flex-direction:column;gap:6px;}}
.cb.hide{{display:none;}}
.g2{{display:grid;grid-template-columns:1fr 1fr;gap:5px;}}
.lbl{{font-size:10.5px;color:var(--txt2);font-weight:600;margin-bottom:4px;}}

/* ── TOGGLE SWITCH (replaces checkboxes) ──
   Fix: onclick on the .sw-track only (not the whole row),
   event.stopPropagation() prevents checkbox from double-firing.
   Visual state is set immediately via JS — no blur needed. ── */
.sw-row{{
  display:flex;align-items:center;justify-content:space-between;
  padding:8px 11px;background:var(--bg3);border-radius:var(--r-sm);
  cursor:pointer;user-select:none;
  transition:background var(--t);
}}
.sw-row:hover{{background:var(--bg4);}}
.sw-label{{
  font-size:13px;font-weight:600;color:#fff;
  letter-spacing:-0.01em;pointer-events:none;
}}
.sw-track{{
  position:relative;width:36px;height:20px;flex-shrink:0;
}}
.sw-track input[type=checkbox]{{
  position:absolute;opacity:0;width:0;height:0;pointer-events:none;
}}
.sw-knob{{
  position:absolute;inset:0;border-radius:10px;
  background:var(--bg5);
  border:none;
  transition:background var(--t);
  cursor:pointer;
}}
.sw-knob::after{{
  content:'';position:absolute;
  left:3px;top:3px;
  width:12px;height:12px;border-radius:50%;
  background:var(--txt3);
  transition:transform .2s cubic-bezier(.34,1.56,.64,1),background var(--t);
}}
.sw-knob.sw-on{{
  background:#ffffff;
}}
.sw-knob.sw-on::after{{
  transform:translateX(16px);background:#111114;
}}

/* ── SLIDERS ── */
.sl{{background:var(--bg3);border-radius:var(--r-sm);padding:8px 11px;}}
.sl-h{{display:flex;justify-content:space-between;align-items:center;margin-bottom:7px;}}
.sl-n{{font-size:12px;color:var(--txt);font-weight:600;letter-spacing:-0.01em;}}
.sl-v{{font-family:var(--mono);font-size:10px;color:#fff;font-weight:600;min-width:24px;text-align:right;}}
.range-wrap{{position:relative;width:100%;display:flex;align-items:center;height:18px;}}
.range-track{{position:absolute;left:0;right:0;height:3px;top:7px;background:rgba(255,255,255,0.1);border-radius:99px;pointer-events:none;}}
.range-fill{{position:absolute;left:0;height:3px;top:7px;background:#fff;border-radius:99px;pointer-events:none;}}
input[type=range]{{
  -webkit-appearance:none;appearance:none;
  width:100%;height:18px;margin:0;padding:0;
  background:transparent;outline:none;cursor:pointer;
  position:relative;z-index:2;
}}
input[type=range]::-webkit-slider-runnable-track{{height:3px;border-radius:99px;background:transparent;}}
input[type=range]::-webkit-slider-thumb{{
  -webkit-appearance:none;width:13px;height:13px;border-radius:50%;
  background:#fff;border:2px solid var(--bg);
  box-shadow:0 0 0 1px rgba(255,255,255,.25);
  cursor:pointer;margin-top:-5px;
  transition:transform .1s;
}}
input[type=range]:active::-webkit-slider-thumb{{transform:scale(1.15);}}

/* ── SELECT ── */
select{{
  background:var(--bg3);color:var(--txt);border:1px solid var(--border);
  border-radius:var(--r-sm);padding:6px 26px 6px 10px;
  font-family:var(--mono);font-size:10.5px;outline:none;cursor:pointer;width:100%;
  -webkit-appearance:none;
  background-image:url("data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 10 6'%3E%3Cpath d='M0 0l5 6 5-6z' fill='%23666'/%3E%3C/svg%3E");
  background-repeat:no-repeat;background-position:right 9px center;background-size:6px;
  font-weight:500;transition:border-color var(--t);
}}
select:hover{{border-color:var(--border-hi);}}
option{{background:#1a1a20;}}

/* ── HOTKEY ── */
.hk{{
  display:flex;align-items:center;justify-content:space-between;
  background:var(--bg3);border-radius:var(--r-sm);
  padding:6px 11px;cursor:pointer;user-select:none;min-height:32px;
  transition:background var(--t);border:1px solid var(--border);
}}
.hk:hover{{background:var(--bg4);}}
.hk.listening{{outline:2px solid rgba(255,255,255,.25);animation:_hkp .8s ease infinite;}}
@keyframes _hkp{{0%,100%{{outline-color:rgba(255,255,255,.1);}}50%{{outline-color:rgba(255,255,255,.3);}}}}
.hk-prompt{{font-size:9px;color:var(--txt2);font-family:var(--mono);animation:_blink .7s step-end infinite;}}
@keyframes _blink{{0%,100%{{opacity:1;}}50%{{opacity:.2;}}}}
.hk-badge{{padding:2px 8px;background:rgba(255,255,255,0.1);border-radius:3px;font-family:var(--mono);font-size:10.5px;color:#fff;font-weight:600;}}

/* ── PILLS ── */
.pills{{display:flex;gap:3px;flex-wrap:wrap;}}
.pill{{
  padding:5px 12px;background:var(--bg3);border-radius:20px;cursor:pointer;
  font-size:12px;font-weight:600;color:var(--txt2);user-select:none;
  transition:all var(--t);border:1px solid var(--border);
}}
.pill:hover{{color:var(--txt);background:var(--bg4);}}
.pill.on{{background:#fff;color:#000;border-color:transparent;font-weight:700;}}

/* ── BUTTONS ── */
.btn{{
  padding:7px 13px;border-radius:var(--r-sm);border:1px solid var(--border);
  background:var(--bg3);color:var(--txt);cursor:pointer;
  font-family:var(--font);font-size:12px;font-weight:600;
  transition:all var(--t);letter-spacing:-0.01em;
}}
.btn:hover{{background:var(--bg4);color:#fff;border-color:var(--border-hi);}}
.btn:active{{transform:scale(.97);}}
.btn.sm{{padding:3px 9px;font-size:10px;}}
.btn.primary{{background:#fff;color:#000;border-color:transparent;font-weight:700;}}
.btn.primary:hover{{background:#e8e8e8;}}
.btn.danger{{background:var(--red-lo);color:var(--red);border-color:rgba(255,68,85,.2);}}
.btn.danger:hover{{background:rgba(255,68,85,.2);}}
.btn.ok{{background:var(--grn-lo);color:var(--grn);border-color:rgba(61,255,128,.2);}}
.btn.ok:hover{{background:rgba(61,255,128,.2);}}

/* ── TEXT INPUT ── */
input[type=text]{{
  background:var(--bg3);color:#fff;border:1px solid var(--border);
  border-radius:var(--r-sm);padding:6px 10px;
  font-family:var(--font);font-size:12px;outline:none;width:100%;
  transition:border-color var(--t);
}}
input[type=text]:focus{{border-color:var(--border-hi);}}
input[type=text]::placeholder{{color:var(--txt3);}}

/* ── COLOR PICKER ── */
.color-row{{display:flex;align-items:center;gap:10px;padding:8px 11px;background:var(--bg3);border-radius:var(--r-sm);border:1px solid var(--border);}}
.cp-swatch{{width:26px;height:26px;border-radius:7px;cursor:pointer;flex-shrink:0;transition:transform var(--t);}}
.cp-swatch:hover{{transform:scale(1.1);}}
.color-info{{flex:1;}}
.color-label{{font-size:10.5px;color:var(--txt2);font-weight:600;}}
.color-hex{{font-family:var(--mono);font-size:9.5px;color:var(--txt3);margin-top:1px;}}
.cp-popup{{position:absolute;z-index:9999;background:var(--bg2);border-radius:var(--r);padding:10px;box-shadow:0 14px 44px rgba(0,0,0,.9);display:none;flex-direction:column;gap:8px;width:162px;border:1px solid var(--border-hi);}}
.cp-popup.open{{display:flex;}}
.cp-canvas{{border-radius:50%;cursor:crosshair;display:block;}}
.cp-bright{{width:100%;height:11px;border-radius:6px;cursor:pointer;-webkit-appearance:none;outline:none;border:none;}}
.cp-bright::-webkit-slider-thumb{{-webkit-appearance:none;width:13px;height:13px;border-radius:50%;background:#fff;cursor:pointer;}}
.cp-row{{display:flex;align-items:center;gap:5px;}}
.cp-hex-in{{flex:1;background:var(--bg3);color:#fff;border:1px solid var(--border);border-radius:var(--r-xs);padding:3px 7px;font-family:var(--mono);font-size:9.5px;outline:none;}}
.cp-ok{{padding:2px 8px;border-radius:var(--r-xs);border:1px solid var(--border);background:rgba(255,255,255,0.1);color:#fff;font-size:9.5px;cursor:pointer;}}
.pat-canvas-wrap{{background:var(--bg3);border-radius:var(--r-sm);overflow:hidden;display:flex;align-items:center;justify-content:center;padding:7px;border:1px solid var(--border);}}

/* ── TOASTS ── */
#toasts{{position:fixed;bottom:10px;right:12px;z-index:9999;display:flex;flex-direction:column;gap:4px;pointer-events:none;}}
.toast{{
  padding:7px 13px;border-radius:var(--r-sm);
  background:rgba(18,18,22,.98);font-size:10.5px;
  color:var(--txt2);font-family:var(--mono);
  animation:_ti .12s ease,_to .12s ease 2.8s forwards;
  box-shadow:0 4px 22px rgba(0,0,0,.9);border:1px solid var(--border);
}}
.toast.error{{color:var(--red);}}
.toast.ok{{color:var(--grn);}}
@keyframes _ti{{from{{opacity:0;transform:translateX(8px)}}to{{opacity:1;transform:none}}}}
@keyframes _to{{to{{opacity:0;transform:translateX(8px)}}}}
</style>
</head>
<body>
<canvas id="stars-bg"></canvas>
<div id="toasts"></div>
<div class="app">

<div class="tb">
  <span class="tb-logo">JNY</span>
  <div class="tb-drag" id="drag-region"></div>
  <div class="tb-pills">
    <div class="tp" id="tp-model"><div class="d"></div><span id="tp-mt">OFFLINE</span></div>
    <div class="tp tgt" id="tp-target"><div class="d"></div><span id="tp-tt">NO TARGET</span></div>
    <div class="tp gpu-pill" id="tp-gpu"><div class="d"></div><span id="tp-gt">CPU</span></div>
  </div>
  <div class="wc">
    <button class="wc-btn" onclick="if(bridge)bridge.minimizeWindow()">–</button>
    <button class="wc-btn x" onclick="if(bridge)bridge.closeWindow()">✕</button>
  </div>
</div>

<div class="body">
  <div class="sb">
    <nav class="sb-nav">
      <button class="nb on" onclick="nav('aimbot',this)">Aimbot</button>
      <button class="nb" onclick="nav('visuals',this)">Visuals</button>
      <button class="nb" onclick="nav('ai',this)">AI / Model</button>
      <button class="nb" onclick="nav('pattern',this)">Pattern</button>
      <button class="nb" onclick="nav('triggerbot',this)">Triggerbot</button>
      <button class="nb" onclick="nav('antirecoil',this)">Anti-Recoil</button>
      <button class="nb" onclick="nav('configs',this)">Configs</button>
      <button class="nb" onclick="nav('misc',this)">Settings</button>
    </nav>
    <div class="sb-foot">
      <div class="discord-btn" onclick="openDiscord()" title="Join our Discord">
        <svg class="discord-ic" viewBox="0 0 24 24" fill="currentColor" xmlns="http://www.w3.org/2000/svg">
          <path d="M20.317 4.37a19.791 19.791 0 0 0-4.885-1.515.074.074 0 0 0-.079.037c-.21.375-.444.864-.608 1.25a18.27 18.27 0 0 0-5.487 0 12.64 12.64 0 0 0-.617-1.25.077.077 0 0 0-.079-.037A19.736 19.736 0 0 0 3.677 4.37a.07.07 0 0 0-.032.027C.533 9.046-.32 13.58.099 18.057c.002.022.013.043.031.056a19.9 19.9 0 0 0 5.993 3.03.078.078 0 0 0 .084-.028 14.09 14.09 0 0 0 1.226-1.994.076.076 0 0 0-.041-.106 13.107 13.107 0 0 1-1.872-.892.077.077 0 0 1-.008-.128 10.2 10.2 0 0 0 .372-.292.074.074 0 0 1 .077-.01c3.928 1.793 8.18 1.793 12.062 0a.074.074 0 0 1 .078.01c.12.098.246.198.373.292a.077.077 0 0 1-.006.127 12.299 12.299 0 0 1-1.873.892.077.077 0 0 0-.041.107c.36.698.772 1.362 1.225 1.993a.076.076 0 0 0 .084.028 19.839 19.839 0 0 0 6.002-3.03.077.077 0 0 0 .032-.054c.5-5.177-.838-9.674-3.549-13.66a.061.061 0 0 0-.031-.03zM8.02 15.33c-1.183 0-2.157-1.085-2.157-2.419 0-1.333.956-2.419 2.157-2.419 1.21 0 2.176 1.096 2.157 2.42 0 1.333-.956 2.418-2.157 2.418zm7.975 0c-1.183 0-2.157-1.085-2.157-2.419 0-1.333.955-2.419 2.157-2.419 1.21 0 2.176 1.096 2.157 2.42 0 1.333-.946 2.418-2.157 2.418z"/>
        </svg>
        <span class="discord-lbl">Discord</span>
      </div>
    </div>
  </div>

  <div class="content">
    <div class="c-head">
      <div class="c-title"><div class="c-ic" id="p-ic">◎</div><span id="p-title">Aimbot</span></div>
      <div class="c-right"><div class="fps-pill" id="head-fps">0 FPS</div></div>
    </div>
    <div class="scroll">

<!-- ══ AIMBOT ══ -->
<div class="panel on" id="panel-aimbot">
  <div class="card"><div class="ch" onclick="tog(this)">Enable<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('aimbotcheckbox',event)">
      <span class="sw-label">Enable Aimbot</span>
      <div class="sw-track">
        <input type="checkbox" id="sw-aimbotcheckbox">
        <div class="sw-knob"></div>
      </div>
    </div>
  </div></div>

  <div class="card"><div class="ch" onclick="tog(this)">Strength &amp; Speed<span class="cv">▼</span></div><div class="cb">
    <div class="g2">
      <div class="sl"><div class="sl-h"><span class="sl-n">Reg Strength</span><span class="sl-v" id="v-regularstrengthslider">150</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="300" value="150" oninput="onSl('regularstrengthslider',this)"></div></div>
      <div class="sl"><div class="sl-h"><span class="sl-n">ADS Strength</span><span class="sl-v" id="v-adsstrengthslider">120</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="300" value="120" oninput="onSl('adsstrengthslider',this)"></div></div>
    </div>
    <div class="sl">
      <div class="sl-h"><span class="sl-n">Speed (px/tick)</span><span class="sl-v" id="v-speedmultiplierslider">25</span></div>
      <div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="50" value="25" oninput="onSl('speedmultiplierslider',this)"></div>
    </div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Smoothness</span><span class="sl-v" id="v-smoothnessslider">40</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="0" max="100" value="40" oninput="onSl('smoothnessslider',this)"></div></div>
    <div class="g2">
      <div class="sl"><div class="sl-h"><span class="sl-n">Reg FOV</span><span class="sl-v" id="v-regularfovslider">80</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="10" max="200" value="80" oninput="onSl('regularfovslider',this)"></div></div>
      <div class="sl"><div class="sl-h"><span class="sl-n">ADS FOV</span><span class="sl-v" id="v-adsfovslider">60</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="10" max="200" value="60" oninput="onSl('adsfovslider',this)"></div></div>
    </div>
  </div></div>

  <div class="card"><div class="ch" onclick="tog(this)">Bone &amp; Hotkeys<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Aim Bone</div>
      <div class="pills" id="pills-aimboneradiobutton">
        <div class="pill on" onclick="onPill('aimboneradiobutton','Head',this.parentElement)">Head</div>
        <div class="pill" onclick="onPill('aimboneradiobutton','Neck',this.parentElement)">Neck</div>
        <div class="pill" onclick="onPill('aimboneradiobutton','Torso',this.parentElement)">Torso</div>
        <div class="pill" onclick="onPill('aimboneradiobutton','Custom',this.parentElement)">Custom</div>
      </div>
    </div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Custom Offset</span><span class="sl-v" id="v-customoffsetslider">2</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="20" value="2" oninput="onSl('customoffsetslider',this)"></div></div>
    <div class="g2">
      <div><div class="lbl">Aim Key</div><div class="hk" id="hk-aimbothotkeycombobox" onclick="startListen('aimbothotkeycombobox',this)"><span class="hk-badge" id="hkv-aimbothotkeycombobox">RMB</span></div></div>
      <div><div class="lbl">ADS Key</div><div class="hk" id="hk-aimbotadskeycombobox" onclick="startListen('aimbotadskeycombobox',this)"><span class="hk-badge" id="hkv-aimbotadskeycombobox">None</span></div></div>
    </div>
  </div></div>
</div>

<!-- ══ VISUALS ══ -->
<div class="panel" id="panel-visuals">
  <div class="card"><div class="ch" onclick="tog(this)">FOV Circle<span class="cv">▼</span></div><div class="cb">
    <div class="g2">
      <div class="sw-row" onclick="swClick('drawfovcirclecheckbox',event)"><span class="sw-label">Draw FOV</span><div class="sw-track"><input type="checkbox" id="sw-drawfovcirclecheckbox"><div class="sw-knob"></div></div></div>
      <div class="sw-row" onclick="swClick('drawcircleoutlinescheckbox',event)"><span class="sw-label">Outlines</span><div class="sw-track"><input type="checkbox" id="sw-drawcircleoutlinescheckbox"><div class="sw-knob"></div></div></div>
    </div>
    <div class="color-row"><div class="cp-swatch" id="sw-fovcirclecolorpicker" style="background:#fff" onclick="cpOpen('fovcirclecolorpicker',this)"></div><div class="color-info"><div class="color-label">FOV Circle</div><div class="color-hex" id="hex-fovcirclecolorpicker">#ffffff</div></div></div>
    <div class="cp-popup" id="cpp-fovcirclecolorpicker"></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Crosshair<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('drawcrosshaircheckbox',event)"><span class="sw-label">Draw Crosshair</span><div class="sw-track"><input type="checkbox" id="sw-drawcrosshaircheckbox"><div class="sw-knob"></div></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Size</span><span class="sl-v" id="v-crosshairsizeslider">6</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="30" value="6" oninput="onSl('crosshairsizeslider',this)"></div></div>
    <div class="color-row"><div class="cp-swatch" id="sw-crosshaircolorpicker" style="background:#fff" onclick="cpOpen('crosshaircolorpicker',this)"></div><div class="color-info"><div class="color-label">Crosshair</div><div class="color-hex" id="hex-crosshaircolorpicker">#ffffff</div></div></div>
    <div class="cp-popup" id="cpp-crosshaircolorpicker"></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Target Boxes<span class="cv">▼</span></div><div class="cb">
    <div class="g2">
      <div class="sw-row" onclick="swClick('drawtargetboxescheckbox',event)"><span class="sw-label">Draw Boxes</span><div class="sw-track"><input type="checkbox" id="sw-drawtargetboxescheckbox"><div class="sw-knob"></div></div></div>
      <div class="sw-row" onclick="swClick('drawboxoutlinescheckbox',event)"><span class="sw-label">Outlines</span><div class="sw-track"><input type="checkbox" id="sw-drawboxoutlinescheckbox"><div class="sw-knob"></div></div></div>
    </div>
    <div><div class="lbl">Box Style</div><div class="pills" id="pills-targetboxestyperadiobutton"><div class="pill on" onclick="onPill('targetboxestyperadiobutton','Regular Box',this.parentElement)">Regular</div><div class="pill" onclick="onPill('targetboxestyperadiobutton','Corner Box',this.parentElement)">Corner</div></div></div>
    <div class="color-row"><div class="cp-swatch" id="sw-targetboxescolorpicker" style="background:#fff" onclick="cpOpen('targetboxescolorpicker',this)"></div><div class="color-info"><div class="color-label">Boxes</div><div class="color-hex" id="hex-targetboxescolorpicker">#ffffff</div></div></div>
    <div class="cp-popup" id="cpp-targetboxescolorpicker"></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Tracers<span class="cv">▼</span></div><div class="cb">
    <div class="g2">
      <div class="sw-row" onclick="swClick('drawtargettracerscheckbox',event)"><span class="sw-label">Tracers</span><div class="sw-track"><input type="checkbox" id="sw-drawtargettracerscheckbox"><div class="sw-knob"></div></div></div>
      <div class="sw-row" onclick="swClick('drawtraceroutlinescheckbox',event)"><span class="sw-label">Outlines</span><div class="sw-track"><input type="checkbox" id="sw-drawtraceroutlinescheckbox"><div class="sw-knob"></div></div></div>
    </div>
    <div class="g2">
      <div><div class="lbl">From</div><div class="pills" id="pills-targettracersfromradiobutton" style="flex-direction:column;gap:3px;"><div class="pill on" onclick="onPill('targettracersfromradiobutton','Screen Centre',this.parentElement)">Centre</div><div class="pill" onclick="onPill('targettracersfromradiobutton','Screen Bottom',this.parentElement)">Bottom</div></div></div>
      <div><div class="lbl">To</div><div class="pills" id="pills-targettracerstoradiobutton" style="flex-direction:column;gap:3px;"><div class="pill on" onclick="onPill('targettracerstoradiobutton','Aim Bone',this.parentElement)">Aim Bone</div><div class="pill" onclick="onPill('targettracerstoradiobutton','Target Bottom',this.parentElement)">Bot</div></div></div>
    </div>
    <div class="color-row"><div class="cp-swatch" id="sw-targettracerscolorpicker" style="background:#fff" onclick="cpOpen('targettracerscolorpicker',this)"></div><div class="color-info"><div class="color-label">Tracers</div><div class="color-hex" id="hex-targettracerscolorpicker">#ffffff</div></div></div>
    <div class="cp-popup" id="cpp-targettracerscolorpicker"></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Frame<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('drawframesquarecheckbox',event)"><span class="sw-label">Draw Frame Square</span><div class="sw-track"><input type="checkbox" id="sw-drawframesquarecheckbox"><div class="sw-knob"></div></div></div>
  </div></div>
</div>

<!-- ══ AI ══ -->
<div class="panel" id="panel-ai">
  <div class="card"><div class="ch" onclick="tog(this)">ONNX Model<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Model File</div><div style="display:flex;gap:5px;"><select id="s-modelcombobox" onchange="onSel('modelcombobox',this)" style="flex:1"></select><button class="btn sm" onclick="refreshModels()">↺</button></div></div>
    <button class="btn primary" style="width:100%;" onclick="loadSelectedModel()">Load Model</button>
    <div style="font-size:10.5px;color:var(--txt2);font-family:var(--mono);padding:3px 0;" id="model-status">No model loaded</div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Detection<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('ignorefortniteplayercheckbox',event)"><span class="sw-label">Ignore Own Player</span><div class="sw-track"><input type="checkbox" id="sw-ignorefortniteplayercheckbox"><div class="sw-knob"></div></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Confidence</span><span class="sl-v" id="v-aiconfidenceslider">35</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="90" value="35" oninput="onSl('aiconfidenceslider',this)"></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">IOU Threshold</span><span class="sl-v" id="v-aiiouslider">45</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="90" value="45" oninput="onSl('aiiouslider',this)"></div></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Target Lock &amp; Prediction<span class="cv">▼</span></div><div class="cb">
    <div class="sl"><div class="sl-h"><span class="sl-n">Lock Radius</span><span class="sl-v" id="v-lockradiusslider">90</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="10" max="300" value="90" oninput="onSl('lockradiusslider',this)"></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Lock Timeout</span><span class="sl-v" id="v-locktimeoutslider">35</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="10" max="80" value="35" oninput="onSl('locktimeoutslider',this)"></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Prediction</span><span class="sl-v" id="v-predictionstrengthslider">50</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="0" max="100" value="50" oninput="onSl('predictionstrengthslider',this)"></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Stickiness</span><span class="sl-v" id="v-stickinessslider">50</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="0" max="100" value="50" oninput="onSl('stickinessslider',this)"></div></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Aim Logging<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Log Path</div><input type="text" id="logpath" placeholder="aim_log.csv" value="aim_log.csv"></div>
    <div style="display:flex;gap:5px;"><button class="btn ok" style="flex:1;" onclick="startLog()">Start</button><button class="btn danger" style="flex:1;" onclick="stopLog()">Stop</button></div>
  </div></div>
</div>

<!-- ══ PATTERN ══ -->
<div class="panel" id="panel-pattern">
  <div class="card"><div class="ch" onclick="tog(this)">Pattern Control<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('patterncheckbox',event)"><span class="sw-label">Enable Pattern</span><div class="sw-track"><input type="checkbox" id="sw-patterncheckbox"><div class="sw-knob"></div></div></div>
    <div><div class="lbl">Hotkey</div><div class="hk" id="hk-patternhotkeycombobox" onclick="startListen('patternhotkeycombobox',this)"><span class="hk-badge" id="hkv-patternhotkeycombobox">RMB</span></div></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Pattern Select<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Preset</div><select id="s-patternselect" onchange="onPatSel(this)"></select></div>
    <div class="g2">
      <div class="sl"><div class="sl-h"><span class="sl-n">Speed</span><span class="sl-v" id="v-patternspeedslider">10</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="30" value="10" oninput="onSl('patternspeedslider',this);drawPatPreview()"></div></div>
      <div class="sl"><div class="sl-h"><span class="sl-n">Scale</span><span class="sl-v" id="v-patternscaleslider">10</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="30" value="10" oninput="onSl('patternscaleslider',this);drawPatPreview()"></div></div>
    </div>
    <div class="sw-row" onclick="swClick('patternloopcheckbox',event)"><span class="sw-label">Loop Pattern</span><div class="sw-track"><input type="checkbox" id="sw-patternloopcheckbox"><div class="sw-knob"></div></div></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Preview<span class="cv">▼</span></div><div class="cb">
    <div class="pat-canvas-wrap"><canvas id="pat-preview" width="240" height="110"></canvas></div>
    <div style="font-size:10.5px;color:var(--txt2);font-family:var(--mono);padding:3px 0;" id="pat-info">Select a pattern</div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Custom Pattern<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Points (dx,dy;dx,dy;…)</div><input type="text" id="inp-patterncustom" placeholder="0,2;-1,3;1,3;0,4" oninput="onSetting('patterncustom',this.value)"></div>
    <button class="btn" style="width:100%;" onclick="applyCustomPat()">Apply Custom</button>
  </div></div>
</div>

<!-- ══ TRIGGERBOT ══ -->
<div class="panel" id="panel-triggerbot">
  <div class="card"><div class="ch" onclick="tog(this)">Triggerbot<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('triggerbotcheckbox',event)"><span class="sw-label">Enable Triggerbot</span><div class="sw-track"><input type="checkbox" id="sw-triggerbotcheckbox"><div class="sw-knob"></div></div></div>
    <div><div class="lbl">Hotkey</div><div class="hk" id="hk-triggerbothotkeycombobox" onclick="startListen('triggerbothotkeycombobox',this)"><span class="hk-badge" id="hkv-triggerbothotkeycombobox">None</span></div></div>
  </div></div>
</div>

<!-- ══ ANTI-RECOIL ══ -->
<div class="panel" id="panel-antirecoil">
  <div class="card"><div class="ch" onclick="tog(this)">Anti-Recoil<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('antirecoilcheckbox',event)"><span class="sw-label">Enable Anti-Recoil</span><div class="sw-track"><input type="checkbox" id="sw-antirecoilcheckbox"><div class="sw-knob"></div></div></div>
    <div class="sl"><div class="sl-h"><span class="sl-n">Strength</span><span class="sl-v" id="v-antirecoilstrengthslider">5</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="1" max="15" value="5" oninput="onSl('antirecoilstrengthslider',this)"></div></div>
    <div><div class="lbl">Pattern</div><select id="s-antirecoilpatterncombo" onchange="onSel('antirecoilpatterncombo',this)"></select></div>
    <div><div class="lbl">Hotkey</div><div class="hk" id="hk-antirecoilhotkeycombobox" onclick="startListen('antirecoilhotkeycombobox',this)"><span class="hk-badge" id="hkv-antirecoilhotkeycombobox">None</span></div></div>
  </div></div>
</div>

<!-- ══ CONFIGS ══ -->
<div class="panel" id="panel-configs">
  <div class="card"><div class="ch" onclick="tog(this)">Load / Save<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Config File</div><select id="s-configlist"></select></div>
    <div style="display:flex;gap:5px;"><button class="btn" style="flex:1;" onclick="loadCfg()">Load</button><button class="btn" style="flex:1;" onclick="saveCfg()">Save</button></div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">New Config<span class="cv">▼</span></div><div class="cb">
    <div><div class="lbl">Name</div><input type="text" id="newcfg" placeholder="my_config"></div>
    <button class="btn primary" style="width:100%;" onclick="createCfg()">Create</button>
  </div></div>
</div>

<!-- ══ SETTINGS ══ -->
<div class="panel" id="panel-misc">
  <div class="card"><div class="ch" onclick="tog(this)">Performance<span class="cv">▼</span></div><div class="cb">
    <div class="sl"><div class="sl-h"><span class="sl-n">Capture FPS</span><span class="sl-v" id="v-targetfpsslider">360</span></div><div class="range-wrap"><div class="range-track"></div><div class="range-fill"></div><input type="range" min="60" max="360" step="30" value="360" oninput="onSl('targetfpsslider',this)"></div></div>
    <div style="font-size:10.5px;color:var(--txt2);font-family:var(--mono);padding:3px 0;" id="cap-mode-hint">Capture: checking…</div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Preview Window<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" id="preview-row" onclick="togglePreviewWindow(event)">
      <span class="sw-label">Capture Preview</span>
      <div class="sw-track">
        <input type="checkbox" id="sw-previewwindow">
        <div class="sw-knob" id="preview-knob"></div>
      </div>
    </div>
    <div style="font-size:10.5px;color:var(--txt2);font-family:var(--mono);padding:3px 0;">Shows live capture with ESP, boxes and tracers drawn on top.</div>
  </div></div>
  <div class="card"><div class="ch" onclick="tog(this)">Misc<span class="cv">▼</span></div><div class="cb">
    <div class="sw-row" onclick="swClick('streamproofcheckbox',event)"><span class="sw-label">Streamproof GUI</span><div class="sw-track"><input type="checkbox" id="sw-streamproofcheckbox"><div class="sw-knob"></div></div></div>
    <button class="btn" style="width:100%;" onclick="if(bridge)bridge.hideConsole()">Hide Console</button>
  </div></div>
</div>

    </div>
  </div>
</div>
</div>

<script>
// ── STARS / SNOWFLAKES BACKGROUND ──────────────────────────────
(function(){{
  const canvas=document.getElementById('stars-bg');
  canvas.width=720;canvas.height=460;
  const ctx=canvas.getContext('2d');
  const particles=[];
  const N=90;
  for(let i=0;i<N;i++){{
    const isFlake=Math.random()<0.35;
    particles.push({{
      x:Math.random()*720,
      y:Math.random()*460,
      r:isFlake?(Math.random()*2.5+1):(Math.random()*1.2+0.3),
      alpha:Math.random()*0.45+0.1,
      speed:Math.random()*0.25+0.04,
      drift:Math.random()*0.12-0.06,
      pulse:Math.random()*Math.PI*2,
      pulseSpeed:Math.random()*0.018+0.004,
      flake:isFlake,
      arms:Math.floor(Math.random()*2)*2+4
    }});
  }}
  function drawFlake(x,y,r,a){{
    ctx.save();ctx.translate(x,y);ctx.globalAlpha=a;
    ctx.strokeStyle='#ffffff';ctx.lineWidth=r*0.38;
    for(let i=0;i<6;i++){{
      ctx.save();ctx.rotate(i*Math.PI/3);
      ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(0,-r*2.8);ctx.stroke();
      ctx.save();ctx.translate(0,-r*1.4);
      ctx.rotate(Math.PI/4);ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(r*0.6,0);ctx.stroke();
      ctx.rotate(-Math.PI/2);ctx.beginPath();ctx.moveTo(0,0);ctx.lineTo(r*0.6,0);ctx.stroke();
      ctx.restore();ctx.restore();
    }}
    ctx.restore();
  }}
  function frame(){{
    ctx.clearRect(0,0,720,460);
    for(const p of particles){{
      p.pulse+=p.pulseSpeed;
      const a=p.alpha*(0.65+0.35*Math.sin(p.pulse));
      if(p.flake){{
        drawFlake(p.x,p.y,p.r,a);
      }}else{{
        ctx.globalAlpha=a;
        if(p.r>0.9){{
          const g=ctx.createRadialGradient(p.x,p.y,0,p.x,p.y,p.r*3.5);
          g.addColorStop(0,'rgba(255,255,255,'+a*0.35+')');
          g.addColorStop(1,'rgba(255,255,255,0)');
          ctx.fillStyle=g;
          ctx.beginPath();ctx.arc(p.x,p.y,p.r*3.5,0,Math.PI*2);ctx.fill();
        }}
        ctx.fillStyle='#ffffff';
        ctx.beginPath();ctx.arc(p.x,p.y,p.r,0,Math.PI*2);ctx.fill();
        ctx.globalAlpha=1;
      }}
      p.y+=p.speed;p.x+=p.drift;
      if(p.y>465){{p.y=-6;p.x=Math.random()*720;}}
      if(p.x<-6)p.x=726;
      if(p.x>726)p.x=-6;
    }}
    requestAnimationFrame(frame);
  }}
  frame();
}})();

// ── APP CORE ──────────────────────────────────────────────────
const KEY_ITEMS={key_items_json};
const ALL_PATTERNS={all_patterns};
const PANELS={{
  aimbot:{{ic:'◎',title:'Aimbot'}},
  visuals:{{ic:'◈',title:'Visuals'}},
  ai:{{ic:'◉',title:'AI / Model'}},
  pattern:{{ic:'⊕',title:'Pattern'}},
  triggerbot:{{ic:'⊛',title:'Triggerbot'}},
  antirecoil:{{ic:'↕',title:'Anti-Recoil'}},
  configs:{{ic:'☰',title:'Configs'}},
  misc:{{ic:'⚙',title:'Settings'}}
}};
let bridge=null;

// ── DRAG ──────────────────────────────────────────────────────
let _drag=false,_dx=0,_dy=0;
document.getElementById('drag-region').addEventListener('mousedown',e=>{{
  if(e.button!==0)return;_drag=true;_dx=e.screenX;_dy=e.screenY;e.preventDefault();
}});
document.addEventListener('mousemove',e=>{{
  if(!_drag||!bridge)return;
  const dx=e.screenX-_dx,dy=e.screenY-_dy;
  if(dx||dy){{bridge.moveWindow(dx,dy);_dx=e.screenX;_dy=e.screenY;}}
}});
document.addEventListener('mouseup',()=>{{_drag=false;}});

// ── HOTKEY CAPTURE ────────────────────────────────────────────
let _listening=null;
const VK_MAP={{1:'LMB',2:'RMB',4:'MMB',5:'Mouse4',6:'Mouse5',8:'Backspace',9:'Tab',13:'Enter',16:'Shift',17:'Ctrl',18:'Alt',19:'Pause',20:'Caps',27:'Esc',32:'Space',33:'PgUp',34:'PgDn',35:'End',36:'Home',37:'Left',38:'Up',39:'Right',40:'Down',45:'Insert',46:'Delete',96:'Num0',97:'Num1',98:'Num2',99:'Num3',100:'Num4',101:'Num5',102:'Num6',103:'Num7',104:'Num8',105:'Num9',112:'F1',113:'F2',114:'F3',115:'F4',116:'F5',117:'F6',118:'F7',119:'F8',120:'F9',121:'F10',122:'F11',123:'F12',160:'LShift',161:'RShift',162:'LCtrl',163:'RCtrl',164:'LAlt',165:'RAlt'}};
for(let i=65;i<=90;i++)VK_MAP[i]=String.fromCharCode(i);
for(let i=48;i<=57;i++)VK_MAP[i]=String(i-48);
function startListen(key,el){{
  if(_listening===key){{stopListen();return;}}
  if(_listening)stopListen();
  _listening=key;el.classList.add('listening');
  el.innerHTML='<span class="hk-prompt">Press key…</span>';
  document.addEventListener('keydown',_onKC,{{once:true,capture:true}});
  document.addEventListener('mousedown',_onMC,{{once:true,capture:true}});
}}
function _onKC(e){{e.preventDefault();e.stopImmediatePropagation();_applyHK(_listening,VK_MAP[e.keyCode]||('K'+e.keyCode));}}
function _onMC(e){{_applyHK(_listening,{{0:'LMB',1:'MMB',2:'RMB',3:'Mouse4',4:'Mouse5'}}[e.button]||('M'+e.button));}}
function _applyHK(key,name){{
  const el=document.getElementById('hk-'+key);
  if(el){{el.classList.remove('listening');el.innerHTML='<span class="hk-badge" id="hkv-'+key+'">'+name+'</span>';}}
  if(bridge)bridge.setSetting(key,JSON.stringify(name));
  _listening=null;
  document.removeEventListener('keydown',_onKC,{{capture:true}});
  document.removeEventListener('mousedown',_onMC,{{capture:true}});
}}
function stopListen(){{
  if(!_listening)return;
  const el=document.getElementById('hk-'+_listening);
  if(el){{el.classList.remove('listening');if(!document.getElementById('hkv-'+_listening))el.innerHTML='<span class="hk-badge" id="hkv-'+_listening+'">?</span>';}}
  document.removeEventListener('keydown',_onKC,{{capture:true}});
  document.removeEventListener('mousedown',_onMC,{{capture:true}});
  _listening=null;
}}

// ── WEBCHANNEL ────────────────────────────────────────────────
new QWebChannel(qt.webChannelTransport,ch=>{{
  bridge=ch.objects.bridge;
  bridge.statsUpdated.connect(onStats);
  bridge.toastMessage.connect(toast);
  bridge.configListUpdated.connect(j=>fillSel('s-configlist',JSON.parse(j)));
  init();
}});

function init(){{
  const ps=document.getElementById('s-antirecoilpatterncombo');
  const pp=document.getElementById('s-patternselect');
  ALL_PATTERNS.forEach(v=>{{
    [ps,pp].forEach(sel=>{{
      const o=document.createElement('option');o.value=o.textContent=v;sel.appendChild(o);
    }});
  }});
  bridge.getAllSettings(j=>{{
    const s=JSON.parse(j);
    Object.entries(s).forEach(([k,v])=>applyUI(k,v));
    drawPatPreview();
  }});
  refreshModels();refreshConfigs();
}}

// ── TOGGLE SWITCH — instant visual via .sw-on class ──────────
// CSS sibling selector (input:checked ~ .sw-knob) can delay render
// in QtWebEngine. We bypass it by setting .sw-on directly on the
// knob element — immediate repaint, zero delay, works first click.
function swClick(key,e){{
  e.stopPropagation();
  const inp=document.getElementById('sw-'+key);
  if(!inp)return;
  inp.checked=!inp.checked;
  const knob=inp.nextElementSibling;
  if(knob){{
    if(inp.checked)knob.classList.add('sw-on');
    else knob.classList.remove('sw-on');
  }}
  if(bridge)bridge.setSetting(key,JSON.stringify(inp.checked));
}}

// ── APPLY UI FROM SETTINGS ────────────────────────────────────
function applyUI(k,v){{
  const sw=document.getElementById('sw-'+k);
  if(sw&&sw.type==='checkbox'){{
    sw.checked=!!v;
    const knob=sw.nextElementSibling;
    if(knob){{
      if(!!v)knob.classList.add('sw-on');
      else knob.classList.remove('sw-on');
    }}
    return;
  }}
  const vEl=document.getElementById('v-'+k);
  if(vEl){{
    vEl.textContent=v;
    const sl=vEl.closest('.sl');
    if(sl){{const i=sl.querySelector('input[type=range]');if(i){{i.value=v;_fillSlider(i);}}}}
    return;
  }}
  const sel=document.getElementById('s-'+k);if(sel){{sel.value=v;return;}}
  const pls=document.getElementById('pills-'+k);
  if(pls){{pls.querySelectorAll('.pill').forEach(p=>p.classList.toggle('on',p.textContent.trim()===String(v)));return;}}
  const hkb=document.getElementById('hkv-'+k);if(hkb){{hkb.textContent=v||'None';return;}}
  if(Array.isArray(v)){{
    const hex=rgb2hex(v[0],v[1],v[2]);
    const cp=document.getElementById('sw-'+k+'colorpicker')||document.getElementById('sw-'+k);
    const hx=document.getElementById('hex-'+k);
    if(cp&&cp.classList.contains('cp-swatch'))cp.style.background=hex;
    if(hx)hx.textContent=hex;
  }}
}}

function onSl(k,el){{
  const v=parseInt(el.value);
  const vEl=document.getElementById('v-'+k);if(vEl)vEl.textContent=v;
  if(bridge)bridge.setSetting(k,JSON.stringify(v));
  _fillSlider(el);
}}
function _fillSlider(el){{
  const mn=parseFloat(el.min)||0,mx=parseFloat(el.max)||100;
  const pct=(parseFloat(el.value)-mn)/(mx-mn);
  const wrap=el.parentNode;
  if(wrap&&wrap.classList.contains('range-wrap')){{
    const fill=wrap.querySelector('.range-fill');
    if(fill){{const tw=el.offsetWidth-13;fill.style.width=(pct*tw)+'px';}}
  }}
}}
document.querySelectorAll('input[type=range]').forEach(_fillSlider);
function onSel(k,el){{if(bridge)bridge.setSetting(k,JSON.stringify(el.value));}}
function onSetting(k,v){{if(bridge)bridge.setSetting(k,JSON.stringify(v));}}
function onPill(k,val,group){{
  group.querySelectorAll('.pill').forEach(p=>p.classList.toggle('on',p.textContent.trim()===val));
  if(bridge)bridge.setSetting(k,JSON.stringify(val));
}}
function onPatSel(el){{if(bridge)bridge.setSetting('patternselect',JSON.stringify(el.value));drawPatPreview();}}
function applyCustomPat(){{
  const v=document.getElementById('inp-patterncustom').value.trim();
  if(!v){{toast('Enter points first','error');return;}}
  if(bridge)bridge.setSetting('patterncustom',JSON.stringify(v));
  toast('Applied','ok');
}}

// ── PATTERN PREVIEW ───────────────────────────────────────────
const PAT_DATA={{"default":[[0,1],[0,2],[0,2],[0,3],[0,3],[0,3],[0,2],[0,2],[0,1],[0,1]],"ak":[[0,2],[0,3],[-1,3],[1,3],[0,4],[0,4],[-1,3],[1,3],[0,3],[0,2]],"smg":[[0,1],[0,1],[0,2],[0,2],[0,2],[0,1],[0,1],[0,1],[0,1],[0,1]],"lmg":[[0,2],[0,2],[0,3],[0,3],[0,4],[0,4],[0,3],[0,3],[0,2],[0,2]],"sniper":[[0,4],[0,1],[0,1],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0],[0,0]],"valorant_vandal":[[0,2],[0,3],[-1,3],[1,3],[0,4],[-1,3],[1,3],[0,3],[-1,2],[1,2]],"valorant_phantom":[[0,1],[0,2],[-1,2],[1,2],[0,3],[0,3],[-1,2],[1,2],[0,2],[0,1]],"csgo_ak47":[[0,3],[0,4],[-1,4],[1,4],[0,5],[-1,4],[1,4],[0,4],[-1,3],[1,3]],"csgo_m4":[[0,2],[0,3],[-1,3],[1,3],[0,3],[-1,3],[1,3],[0,3],[-1,2],[1,2]],"fortnite_ar":[[0,1],[0,2],[0,2],[0,2],[0,3],[0,3],[0,2],[0,2],[0,1],[0,1]]}};
function drawPatPreview(){{
  const canvas=document.getElementById('pat-preview');if(!canvas)return;
  const ctx=canvas.getContext('2d');const W=canvas.width,H=canvas.height;
  ctx.clearRect(0,0,W,H);ctx.fillStyle='#18181c';ctx.fillRect(0,0,W,H);
  const sel=document.getElementById('s-patternselect');const name=sel?sel.value:'default';
  const scale=(document.getElementById('v-patternscaleslider')?.textContent||10)/10;
  const pts=PAT_DATA[name];if(!pts)return;
  let x=W/2,y=H*0.15,maxY=0,minX=999,maxX=-999;const path=[[x,y]];
  for(const [dx,dy] of pts){{x+=dx*scale*4;y+=dy*scale*4;path.push([x,y]);maxY=Math.max(maxY,y);minX=Math.min(minX,x);maxX=Math.max(maxX,x);}}
  const fitScale=Math.min((W-40)/Math.max(maxX-minX,1),(H-28)/Math.max(maxY-H*0.15,1),1);
  const ox=(W/2)-(((minX+maxX)/2)-W/2)*fitScale;const oy=H*0.12;
  ctx.strokeStyle='rgba(255,255,255,0.04)';ctx.lineWidth=1;
  for(let gx=0;gx<W;gx+=20){{ctx.beginPath();ctx.moveTo(gx,0);ctx.lineTo(gx,H);ctx.stroke();}}
  for(let gy=0;gy<H;gy+=20){{ctx.beginPath();ctx.moveTo(0,gy);ctx.lineTo(W,gy);ctx.stroke();}}
  ctx.beginPath();path.forEach(([px,py],i)=>{{const sx=(px-W/2)*fitScale+ox;const sy=(py-H*0.15)*fitScale+oy;i===0?ctx.moveTo(sx,sy):ctx.lineTo(sx,sy);}});
  ctx.strokeStyle='rgba(255,255,255,0.18)';ctx.lineWidth=1;ctx.stroke();
  path.forEach(([px,py],i)=>{{const sx=(px-W/2)*fitScale+ox;const sy=(py-H*0.15)*fitScale+oy;const t=i/(path.length-1);ctx.beginPath();ctx.arc(sx,sy,i===0?3.5:2,0,Math.PI*2);ctx.fillStyle=i===0?'#fff':`rgba(255,255,255,${{0.9-t*0.5}})`;ctx.fill();}});
  const info=document.getElementById('pat-info');if(info)info.textContent=pts.length+' pts · ×'+scale.toFixed(1);
}}

// ── NAVIGATION — smooth tab-switch animation ──────────────────
function nav(id,btn){{
  document.querySelectorAll('.panel').forEach(p=>p.classList.remove('on'));
  document.querySelectorAll('.nb').forEach(b=>b.classList.remove('on'));
  document.getElementById('panel-'+id).classList.add('on');
  btn.classList.add('on');
  const m=PANELS[id]||{{}};
  document.getElementById('p-ic').textContent=m.ic||'';
  document.getElementById('p-title').textContent=m.title||id;
  document.getElementById('panel-'+id).querySelectorAll('input[type=range]').forEach(_fillSlider);
  if(id==='pattern')setTimeout(drawPatPreview,50);
  if(id==='misc')setTimeout(()=>{{
    const h=document.getElementById('cap-mode-hint');
    if(h&&bridge)bridge.getStats(j=>{{const s=JSON.parse(j);if(h)h.textContent='Capture: '+s.capture;}});
  }},100);
}}
function tog(hdr){{hdr.classList.toggle('cls');hdr.nextElementSibling.classList.toggle('hide');}}

// ── MODELS / CONFIGS ──────────────────────────────────────────
function refreshModels(){{if(bridge)bridge.getModelList(j=>fillSel('s-modelcombobox',JSON.parse(j)));}}
function fillSel(id,items){{
  const s=document.getElementById(id);if(!s)return;
  const cur=s.value;s.innerHTML='';
  items.forEach(v=>{{const o=document.createElement('option');o.value=o.textContent=v;s.appendChild(o);}});
  if(items.includes(cur))s.value=cur;
}}
function loadSelectedModel(){{
  if(!bridge)return;
  const name=document.getElementById('s-modelcombobox').value;
  bridge.setSetting('modelcombobox',JSON.stringify(name));
  bridge.loadModel(name);
  document.getElementById('model-status').textContent='Loading '+name+'…';
}}
function refreshConfigs(){{if(bridge)bridge.getConfigList(j=>fillSel('s-configlist',JSON.parse(j)));}}
function loadCfg(){{
  if(!bridge)return;
  const n=document.getElementById('s-configlist').value;
  if(!n){{toast('Select a config','error');return;}}
  bridge.loadConfig(n);
  setTimeout(()=>bridge.getAllSettings(j=>{{const s=JSON.parse(j);Object.entries(s).forEach(([k,v])=>applyUI(k,v));}}),300);
}}
function saveCfg(){{if(bridge)bridge.saveConfig(document.getElementById('s-configlist').value);}}
function createCfg(){{
  if(!bridge)return;
  bridge.createConfig(document.getElementById('newcfg').value.trim());
  setTimeout(refreshConfigs,300);
}}
function startLog(){{if(bridge)bridge.startLogging(document.getElementById('logpath').value||'aim_log.csv','');}}
function stopLog(){{if(bridge)bridge.stopLogging();}}

// ── PREVIEW WINDOW TOGGLE ─────────────────────────────────────
let _previewOpen=false;
function togglePreviewWindow(e){{
  e.stopPropagation();
  _previewOpen=!_previewOpen;
  const inp=document.getElementById('sw-previewwindow');
  const knob=document.getElementById('preview-knob');
  if(inp)inp.checked=_previewOpen;
  if(knob){{_previewOpen?knob.classList.add('sw-on'):knob.classList.remove('sw-on');}}
  if(bridge)bridge.togglePreview();
}}

// ── DISCORD ───────────────────────────────────────────────────
function openDiscord(){{
  if(bridge){{
    // Use Qt to open URL — bridge calls Python which opens in browser
    bridge.setSetting('__discord_open__',JSON.stringify('https://discord.gg/jN9q5ceYYp'));
  }}
  // Also try direct JS approach
  try{{
    new QWebEngineScript();
  }}catch(e){{}}
}}

// ── STATS ─────────────────────────────────────────────────────
function onStats(json){{
  const s=JSON.parse(json);
  const tm=document.getElementById('tp-model');if(tm){{tm.classList.toggle('on',s.loaded);document.getElementById('tp-mt').textContent=s.loaded?'ONLINE':'OFFLINE';}}
  const tt=document.getElementById('tp-target');if(tt){{tt.classList.toggle('on',s.has_target);document.getElementById('tp-tt').textContent=s.has_target?'TARGET':'NO TARGET';}}
  const prov=s.provider||'CPU';
  const tg=document.getElementById('tp-gpu');if(tg){{tg.classList.toggle('on',prov!=='CPU');document.getElementById('tp-gt').textContent=prov;}}
  document.getElementById('head-fps').textContent=s.fps+' FPS';
  if(s.loaded){{const ms=document.getElementById('model-status');if(ms&&(ms.textContent.startsWith('Loading')||ms.textContent==='No model loaded'))ms.textContent='Loaded: '+s.model+' ['+prov+']';}}
}}

// ── TOAST ─────────────────────────────────────────────────────
function toast(msg,type){{
  const t=document.createElement('div');
  t.className='toast '+(type==='success'?'ok':(type||''));
  t.textContent=msg;
  document.getElementById('toasts').appendChild(t);
  setTimeout(()=>t.remove(),3200);
}}

// ── COLOR PICKER ──────────────────────────────────────────────
function hex2rgb(h){{return{{r:parseInt(h.slice(1,3),16),g:parseInt(h.slice(3,5),16),b:parseInt(h.slice(5,7),16)}};}}
function rgb2hex(r,g,b){{return'#'+[r,g,b].map(x=>Math.max(0,Math.min(255,x)).toString(16).padStart(2,'0')).join('');}}
function rgb2hsl(r,g,b){{r/=255;g/=255;b/=255;const max=Math.max(r,g,b),min=Math.min(r,g,b);let h,s,l=(max+min)/2;if(max===min){{h=s=0;}}else{{const d=max-min;s=l>.5?d/(2-max-min):d/(max+min);switch(max){{case r:h=((g-b)/d+(g<b?6:0))/6;break;case g:h=((b-r)/d+2)/6;break;case b:h=((r-g)/d+4)/6;break;}}}}return{{h:h*360,s:s*100,l:l*100}};}}
function hsl2hex(h,s,l){{s/=100;l/=100;const a=s*Math.min(l,1-l);const f=n=>{{const k=(n+h/30)%12;const c=l-a*Math.max(-1,Math.min(k-3,9-k,1));return Math.round(255*c).toString(16).padStart(2,'0');}};return'#'+f(0)+f(8)+f(4);}}
let _cpCurrent=null;
function cpOpen(k,swatchEl){{if(_cpCurrent===k){{cpClose();return;}}if(_cpCurrent)cpClose();_cpCurrent=k;const popup=document.getElementById('cpp-'+k);if(!popup)return;const startHex=swatchEl.style.background||'#ffffff';popup.innerHTML=cpBuild(k,startHex);popup.classList.add('open');cpDrawWheel(document.getElementById('cpcanvas-'+k));cpSetBrightSlider(k,startHex);setTimeout(()=>document.addEventListener('click',_cpOut,{{once:true,capture:true}}),50);}}
function cpClose(){{if(!_cpCurrent)return;const p=document.getElementById('cpp-'+_cpCurrent);if(p)p.classList.remove('open');_cpCurrent=null;document.removeEventListener('click',_cpOut,{{capture:true}});}}
function _cpOut(e){{if(!_cpCurrent)return;const p=document.getElementById('cpp-'+_cpCurrent);if(p&&!p.contains(e.target))cpClose();else if(p&&p.contains(e.target))document.addEventListener('click',_cpOut,{{once:true,capture:true}});}}
function cpBuild(k,initHex){{return`<canvas id="cpcanvas-${{k}}" class="cp-canvas" width="142" height="142" onclick="cpPickWheel(event,'${{k}}',this)"></canvas><input type="range" class="cp-bright" id="cpbright-${{k}}" min="0" max="100" value="100" oninput="cpBrightChange('${{k}}',this)"><div class="cp-row"><input class="cp-hex-in" id="cphex-${{k}}" type="text" value="${{initHex}}" maxlength="7" onchange="cpHexCommit('${{k}}',this)"><button class="cp-ok" onclick="cpClose()">OK</button></div>`;}}
function cpDrawWheel(canvas){{if(!canvas)return;const ctx=canvas.getContext('2d'),cx=canvas.width/2,cy=canvas.height/2,r=cx-2;for(let a=0;a<360;a++){{const a1=(a-1)*Math.PI/180,a2=(a+1)*Math.PI/180;const g=ctx.createRadialGradient(cx,cy,0,cx,cy,r);g.addColorStop(0,'#fff');g.addColorStop(1,'hsl('+a+',100%,50%)');ctx.beginPath();ctx.moveTo(cx,cy);ctx.arc(cx,cy,r,a1,a2);ctx.closePath();ctx.fillStyle=g;ctx.fill();}}}}
function cpPickWheel(e,k,canvas){{const rect=canvas.getBoundingClientRect();const x=(e.clientX-rect.left)/rect.width*canvas.width-canvas.width/2;const y=(e.clientY-rect.top)/rect.height*canvas.height-canvas.height/2;const r=canvas.width/2-2;if(Math.hypot(x,y)>r)return;const hue=(Math.atan2(y,x)*180/Math.PI+360)%360;const sat=Math.min(Math.hypot(x,y)/r,1);const bl=document.getElementById('cpbright-'+k);const L=100-((bl?parseInt(bl.value):100)/100)*50;cpApply(k,hsl2hex(hue,sat*100,Math.max(0,Math.min(100,L))));}}
function cpBrightChange(k,el){{const hi=document.getElementById('cphex-'+k);if(!hi)return;const rgb=hex2rgb(hi.value),hsl=rgb2hsl(rgb.r,rgb.g,rgb.b);cpApply(k,hsl2hex(hsl.h,hsl.s,parseInt(el.value)));}}
function cpHexCommit(k,el){{let v=el.value.trim();if(v[0]!=='#')v='#'+v;if(!/^#[0-9a-fA-F]{{6}}$/.test(v))return;cpApply(k,v);cpSetBrightSlider(k,v);}}
function cpApply(k,hex){{const hi=document.getElementById('cphex-'+k);if(hi)hi.value=hex;onCol(k,hex);}}
function cpSetBrightSlider(k,hex){{const rgb=hex2rgb(hex),hsl=rgb2hsl(rgb.r,rgb.g,rgb.b);const el=document.getElementById('cpbright-'+k);if(el){{el.value=Math.round(hsl.l);el.style.background=`linear-gradient(to right,#000,hsl(${{hsl.h}},100%,50%),#fff)`;}}}}
function onCol(k,hex){{const sw=document.getElementById('sw-'+k+'colorpicker')||document.getElementById('sw-'+k);if(sw&&sw.classList.contains('cp-swatch'))sw.style.background=hex;const hx=document.getElementById('hex-'+k);if(hx)hx.textContent=hex;const rgb=hex2rgb(hex);if(bridge)bridge.setSetting(k,JSON.stringify([rgb.r,rgb.g,rgb.b,255]));}}
window.addEventListener('load',()=>{{document.querySelectorAll('input[type=range]').forEach(_fillSlider);}});
</script>
</body>
</html>"""


def mainloop(frame_q, result_q, overlay: Visuals, bridge_ref=None):
    global fps_val
    fps_val=0; framecount=0; starttime=time.perf_counter()
    while True:
        if not loaded: time.sleep(0.05); continue
        framecount+=1
        elapsed=time.perf_counter()-starttime
        if elapsed>=1.0:
            fps_val=framecount/elapsed; framecount=0; starttime=time.perf_counter()
        try: r: DetectionResult=result_q.queue[-1]
        except (IndexError,AttributeError): r=None

        detection_results_overlay=[]
        if r is not None and r.box is not None and time.perf_counter()-r.timestamp<0.12:
            detection_results_overlay.append({"bbox":list(r.box)})

        show_boxes=settings.get("drawtargetboxescheckbox",False)
        show_tracers=settings.get("drawtargettracerscheckbox",False)
        if show_boxes or show_tracers:
            overlay.detectionresults=detection_results_overlay
            overlay.update(); QApplication.processEvents()

        # Feed preview window if open
        if bridge_ref is not None:
            pw = bridge_ref._preview_win
            if pw is not None and pw.isVisible():
                # grab latest frame from queue without consuming it
                try:
                    frame = frame_q.queue[-1]
                    pw.set_frame(frame)
                except (IndexError, AttributeError):
                    pass
                pw.set_detection(r)

        global previousads
        current_ads=ads()
        if current_ads!=previousads:
            previousads=current_ads
            if settings.get("drawfovcirclecheckbox",False):
                overlay.update(); QApplication.processEvents()
        time.sleep(0.002)


def main():
    print("="*60)
    print("  JONNY AI v6.6  — Key System · Drag Fix · Preview Window")
    print(f"  Capture: {'bettercam' if _BETTERCAM_AVAILABLE else 'mss (install bettercam)'}")
    print(f"  ORT: {ort.__version__} | {ort.get_available_providers()}")
    print("  INSERT → toggle GUI")
    print("="*60)

    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)

    # ── Try silent auto-login with saved key BEFORE showing any window ──
    hwid = _get_hwid()
    saved = _load_saved_key()
    silent_ok = False
    if saved and saved.get("hwid") == hwid:
        ok, msg, expiry = keysystem_validate(saved["key"], hwid)
        if ok:
            global _AUTHED_HWID, _AUTHED_EXPIRY
            _AUTHED_HWID   = hwid
            _AUTHED_EXPIRY = expiry or saved.get("expiry", "")
            _save_key(saved["key"], hwid, _AUTHED_EXPIRY)
            print(f"[KeySystem] Auto-login OK · expires {_AUTHED_EXPIRY[:10]}")
            silent_ok = True

    if silent_ok:
        # Jump straight into aimbot — no key window shown at all
        _start_aimbot(app, None)
    else:
        # Show key entry window
        key_win = KeyWindow()
        key_win.show()

        def _on_auth():
            key_win.hide()
            _start_aimbot(app, key_win)

        key_win.auth_success.connect(_on_auth)

    ret = app.exec()
    sys.exit(ret)


def _start_aimbot(app: QApplication, key_win):
    """Called after successful key validation. Launches the full aimbot."""

    overlay = Visuals(); overlay.show()

    frame_q  = queue.Queue(maxsize=2)
    result_q = queue.Queue(maxsize=2)
    capturer = ScreenCapture(frame_q)
    detector = Detector(frame_q, result_q)
    aimer    = SmoothAimer(result_q)

    capturer.start(); detector.start(); aimer.start()

    try:
        import ctypes as _ct
        _ct.windll.kernel32.SetThreadPriority(_ct.windll.kernel32.GetCurrentThread(), 1)
    except: pass

    bridge = Bridge(overlay, aimer, frame_q, result_q)
    gui    = MainWindow(bridge)
    bridge.set_main_window(gui)
    gui.show()

    last_model = settings.get("modelcombobox", "")
    if last_model and last_model != "—":
        mp = os.path.join(os.getcwd(), last_model)
        if os.path.isfile(mp):
            threading.Thread(
                target=lambda: (time.sleep(1.5), bridge.loadModel(last_model)),
                daemon=True
            ).start()

    threading.Thread(
        target=mainloop, args=(frame_q, result_q, overlay, bridge), daemon=True
    ).start()

    # ── Periodic loader check every 5 minutes ──────────────────
    def _periodic_check():
        if _AUTHED_HWID:
            ok, msg = keysystem_loader_check(_AUTHED_HWID)
            if not ok:
                print(f"[KeySystem] Access revoked: {msg}")
                # Show message and quit
                from PyQt6.QtWidgets import QMessageBox
                box = QMessageBox()
                box.setWindowTitle("JONNY AI — Access Revoked")
                box.setText(f"Your license has been revoked:\n{msg}")
                box.setIcon(QMessageBox.Icon.Critical)
                box.exec()
                QApplication.quit()
                return
        QTimer.singleShot(5 * 60 * 1000, _periodic_check)  # 5 min

    QTimer.singleShot(5 * 60 * 1000, _periodic_check)

    def check_hotkey():
        if win32api.GetAsyncKeyState(0xA1) & 0x8000:
            gui.setVisible(not gui.isVisible())
        QTimer.singleShot(200, check_hotkey)

    QTimer.singleShot(200, check_hotkey)



if __name__=="__main__":
    main()
