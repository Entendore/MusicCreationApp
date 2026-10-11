from __future__ import annotations
import sys
import os
import json
import struct
import random
import time
import copy
import wave
import threading
import traceback
from dataclasses import dataclass, field, asdict
from typing import List, Optional, Dict, Tuple, Set
import fluidsynth

try:
    import rtmidi
    RTMIDI_AVAILABLE = True
except ImportError:
    RTMIDI_AVAILABLE = False

from PySide6.QtWidgets import (QApplication, QMainWindow, QWidget, QVBoxLayout, 
                               QHBoxLayout, QPushButton, QLabel, QDockWidget, 
                               QComboBox, QGroupBox, QFormLayout, QSlider, QFrame,
                               QFileDialog, QLineEdit, QSpinBox, QToolButton, 
                               QDialog, QGraphicsView, QGraphicsScene, QGraphicsRectItem,
                               QGraphicsLineItem, QMessageBox, QStatusBar, QCheckBox,
                               QDoubleSpinBox, QSplitter, QScrollArea, QMenu, QToolBar,
                               QButtonGroup, QPlainTextEdit, QInputDialog)
from PySide6.QtCore import (Qt, QTimer, QRectF, QPointF, Signal, QEvent, QThread, QObject, 
                            QUrl)
from PySide6.QtGui import (QPainter, QPen, QBrush, QColor, QFont, QAction, QKeyEvent,
                           QShortcut, QKeySequence, QMouseEvent, QWheelEvent, QPainterPath,
                           QToolTip, QCursor, QUndoStack, QUndoCommand)
from PySide6.QtMultimedia import QMediaPlayer, QAudioOutput
from PySide6.QtMultimediaWidgets import QVideoWidget

# ==========================================
# 1. Constants & Music Theory
# ==========================================
PROJECT_VERSION = 1

DIATONIC_STEPS = {0: 0, 2: 1, 4: 2, 5: 3, 7: 4, 9: 5, 11: 6}
NOTE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
DYN_TO_CC = {"pp": 30, "p": 50, "mp": 70, "mf": 90, "f": 110, "ff": 127}

EXPRESSION_MAP = {
    "legato": 0, "pizz": 2, "spicc": 4, "tremolo": 5, "marcato": 7
}

SCALES = {
    "Chromatic": [0,1,2,3,4,5,6,7,8,9,10,11],
    "Major": [0,2,4,5,7,9,11],
    "Minor": [0,2,3,5,7,8,10],
    "Harmonic Minor": [0,2,3,5,7,8,11],
    "Dorian": [0,2,3,5,7,9,10],
    "Pentatonic": [0,2,4,7,9]
}

CHORD_LIB = {
    "": [0, 4, 7], "maj": [0, 4, 7], "min": [0, 3, 7], "dim": [0, 3, 6],
    "maj7": [0, 4, 7, 11], "min7": [0, 3, 7, 10], "7": [0, 4, 7, 10],
    "sus4": [0, 5, 7], "add9": [0, 4, 7, 2]
}

# Layout Constants
STAFF_LINE_SPACING = 7.5
STAFF_HEIGHT = 80
STAFF_GAP = 40
SCORE_TOP = 50
LEFT_MARGIN = 140
BASE_BEAT_WIDTH = 40
RULER_HEIGHT = 30

# ==========================================
# 2. Data Models
# ==========================================
@dataclass
class Note:
    pitch: int = 60
    start_beat: float = 0.0
    duration_beats: float = 1.0
    velocity: int = 90
    voice: int = 1
    delay_ms: int = 0
    staff_id: int = 0  
    dynamic: str = ""
    articulation: str = "legato"
    tuplet: int = 0
    
    def to_dict(self) -> dict: return asdict(self)
    @staticmethod
    def from_dict(d: dict) -> 'Note': return Note(**d)

@dataclass
class ChordSymbol:
    beat: float = 0.0
    duration_beats: float = 4.0
    root: str = "C"
    quality: str = "maj"

@dataclass
class AutomationPoint:
    beat: float = 0.0
    cc_type: int = 1
    value: int = 0
    staff_id: int = 0

@dataclass
class TempoPoint:
    beat: float = 0.0
    bpm: float = 90.0

@dataclass
class Marker:
    beat: float = 0.0
    name: str = "Cue"

def pitch_to_staff_step(pitch: int) -> Tuple[int, Optional[str]]:
    pc = pitch % 12
    octave = pitch // 12 - 5
    if pc in DIATONIC_STEPS:
        return DIATONIC_STEPS[pc] + octave * 7, None
    else:
        lower = pc - 1
        return DIATONIC_STEPS[lower] + octave * 7, 'sharp'

# ==========================================
# 3. Audio Engine (Enhanced)
# ==========================================
class CadenzaAudioEngine:
    def __init__(self):
        self.fs = None
        self.is_active = False
        self.sf_id = -1
        self.sf_path = ""
        self.channel_programs: Dict[int, int] = {i: 48 for i in range(16)}
        self.current_articulations: Dict[int, str] = {}
        self.midi_in = None
        self.midi_out = None
        
        try:
            self.fs = fluidsynth.Synth(gain=0.8)
            for driver in ("alsa", "pulseaudio", "dsound", "coreaudio", "jack"):
                try:
                    self.fs.start(driver=driver)
                    break
                except Exception:
                    continue
            else:
                self.fs.start()
            self.is_active = True
            self.fs.reverb_on(1)
            self.fs.chorus_on(1)
        except Exception as e:
            print(f"Audio Engine failed to initialize: {e}")

        # External MIDI I/O
        if RTMIDI_AVAILABLE:
            try:
                self.midi_in = rtmidi.MidiIn()
                ports = self.midi_in.get_ports()
                if ports: self.midi_in.open_port(0)
                else: self.midi_in.open_virtual_port("Cadenza Virtual In")
                self.midi_in.ignore_types(True, False, True)
            except Exception as e:
                print(f"MIDI Input init failed: {e}")
            try:
                self.midi_out = rtmidi.MidiOut()
                ports = self.midi_out.get_ports()
                if ports: self.midi_out.open_port(0)
                else: self.midi_out.open_virtual_port("Cadenza Clock Out")
            except Exception as e:
                print(f"MIDI Output init failed: {e}")

    def load_soundfont(self, sf2_path: str) -> bool:
        if not self.is_active: return False
        try:
            if self.sf_id != -1: self.fs.funload(self.sf_id, False)
            self.sf_id = self.fs.sfload(sf2_path)
            self.sf_path = sf2_path
            for i in range(5): self.set_program(i, 48)
            return True
        except Exception as e:
            print(f"Failed to load SoundFont: {e}")
            return False

    def set_master_volume(self, volume: float):
        if self.is_active: self.fs.gain = max(0.0, min(1.0, volume))

    def set_program(self, channel: int, program: int):
        if not self.is_active or self.sf_id == -1: return
        self.fs.program_select(channel, self.sf_id, 0, program)
        self.channel_programs[channel] = program

    def set_dynamics(self, channel: int, value: int):
        if not self.is_active: return
        self.fs.cc(channel, 1, value)
        self.fs.cc(channel, 11, value)

    def set_volume(self, channel: int, value: int):
        if not self.is_active: return
        self.fs.cc(channel, 7, max(0, min(127, value)))

    def set_pan(self, channel: int, pan: float):
        if not self.is_active: return
        self.fs.cc(channel, 10, int(max(0, min(127, (pan + 1.0) * 63.5))))

    def set_reverb_send(self, channel: int, value: int):
        if not self.is_active: return
        self.fs.cc(channel, 91, max(0, min(127, value)))

    def send_keyswitch(self, channel: int, ks_note: int):
        if not self.is_active: return
        self.fs.noteon(channel, ks_note, 127)
        QTimer.singleShot(50, lambda: self.fs.noteoff(channel, ks_note))

    def note_on(self, note: int, velocity: int = 90, channel: int = 0):
        if self.is_active: self.fs.noteon(channel, note, velocity)

    def note_off(self, note: int, channel: int = 0):
        if self.is_active: self.fs.noteoff(channel, note)

    def all_notes_off(self):
        if self.is_active:
            for ch in range(16): self.fs.cc(ch, 123, 0)

    def set_midi_callback(self, callback):
        if self.midi_in: self.midi_in.set_callback(callback)

    def send_midi_clock_start(self):
        if self.midi_out:
            self.midi_out.send_message([0xFA])
            self._send_clock_pulse()

    def send_midi_clock_stop(self):
        if self.midi_out:
            self.midi_out.send_message([0xFC])

    def _send_clock_pulse(self):
        if self.midi_out:
            self.midi_out.send_message([0xF8])

# ==========================================
# 4. Piano Roll Dialog
# ==========================================
class VelocityBar(QGraphicsRectItem):
    def __init__(self, note_ref: Note, lane_top: float, lane_bottom: float, parent=None):
        super().__init__(parent)
        self.note_ref = note_ref
        self.lane_top = lane_top
        self.lane_bottom = lane_bottom
        self.setFlag(QGraphicsRectItem.ItemIsMovable, True)
        self.setCursor(Qt.SizeVerCursor)

    def mouseMoveEvent(self, e):
        y = max(self.lane_top, min(self.lane_bottom, e.scenePos().y() - self.rect().height()/2))
        self.setPos(self.x(), y)
        
    def mouseReleaseEvent(self, e):
        y = self.y()
        ratio = 1 - (y - self.lane_top) / (self.lane_bottom - self.lane_top)
        self.note_ref.velocity = max(0, min(127, int(ratio * 127)))
        super().mouseReleaseEvent(e)

class PianoRollDialog(QDialog):
    def __init__(self, notes_data: List[Note], measure_num: int, staff_id: int, parent=None):
        super().__init__(parent)
        self.notes_data = notes_data
        self.measure_num = measure_num
        self.staff_id = staff_id
        self.measure_start_beat = measure_num * 4
        self.setWindowTitle(f"Piano Roll — Measure {measure_num} (Interactive)")
        self.resize(800, 600)
        self.setStyleSheet("background-color: #1a1a1a;")
        
        layout = QVBoxLayout(self)
        self.view = QGraphicsView()
        self.scene = QGraphicsScene(self)
        self.view.setScene(self.scene)
        layout.addWidget(self.view)

        self.key_width = 60
        self.grid_w = 600
        self.grid_h = 300
        self.vel_lane_top = 360
        self.vel_lane_bot = 400
        self._draw_grid()
        self._draw_notes()

    def keyPressEvent(self, e: QKeyEvent):
        if e.key() == Qt.Key_Delete:
            selected_items = self.scene.selectedItems()
            for item in selected_items:
                if hasattr(item, 'note_ref') and not isinstance(item, VelocityBar):
                    if item.note_ref in self.notes_data:
                        self.notes_data.remove(item.note_ref)
                    self.scene.removeItem(item)
        else:
            super().keyPressEvent(e)

    def _draw_grid(self):
        for i in range(36):
            y = i * 8
            pc = (72 - i) % 12
            color = "#222" if pc in {1,3,6,8,10} else "#333"
            self.scene.addRect(0, y, self.key_width, 8, QPen(QColor("#111")), QBrush(QColor(color)))
            if pc == 0:
                t = self.scene.addText(f"C{72 - i // 12}", QFont("Arial", 7))
                t.setPos(2, y - 2); t.setDefaultTextColor(QColor("#888"))
        
        for i in range(0, self.grid_w + 1, 30):
            pen = QPen(QColor("#555"), 1) if i % 120 == 0 else QPen(QColor("#333"), 1)
            self.scene.addLine(self.key_width + i, 0, self.key_width + i, self.grid_h, pen)
        for i in range(0, self.grid_h + 1, 8):
            self.scene.addLine(self.key_width, i, self.key_width + self.grid_w, i, QPen(QColor("#222"), 1))

    def _draw_notes(self):
        for note in self.notes_data:
            if note.staff_id != self.staff_id: continue
            if not (self.measure_start_beat <= note.start_beat < self.measure_start_beat + 4): continue
            
            rel_beat = note.start_beat - self.measure_start_beat
            x = self.key_width + rel_beat * 30
            y = (72 - note.pitch) * 8
            w = note.duration_beats * 30
            item = QGraphicsRectItem(x, y, max(w, 5), 7)
            item.setBrush(QBrush(QColor("#4a9eff")))
            item.setPen(QPen(QColor("#fff"), 1))
            item.setFlag(QGraphicsRectItem.ItemIsMovable, True)
            item.setFlag(QGraphicsRectItem.ItemIsSelectable, True)
            item.note_ref = note
            self.scene.addItem(item)
            
            vel_h = int(note.velocity / 127 * 40)
            vel_item = VelocityBar(note, self.vel_lane_top, self.vel_lane_bot, x, self.vel_lane_bot - vel_h, max(w, 5), vel_h)
            vel_item.setBrush(QBrush(QColor("#ff9900")))
            self.scene.addItem(vel_item)

# ==========================================
# 5. Patcher View
# ==========================================
class PatcherView(QWidget):
    def __init__(self, audio_engine: CadenzaAudioEngine):
        super().__init__()
        self.audio_engine = audio_engine
        self.setMinimumHeight(180)
        self.nodes = [
            {"name": "Instruments", "x": 30, "y": 60, "color": "#cc99ff", "fx": None},
            {"name": "EQ (Low Cut)", "x": 180, "y": 30, "color": "#ffcc99", "fx": "eq"},
            {"name": "Convolution Reverb", "x": 330, "y": 90, "color": "#99ccff", "fx": "reverb"},
            {"name": "Master Out", "x": 480, "y": 60, "color": "#ff9999", "fx": None}
        ]
        self.connections = [(0,1), (1,2), (2,3), (0,3)]
        self.dragging_idx = -1

    def mousePressEvent(self, e: QMouseEvent):
        if e.button() == Qt.LeftButton:
            for i, n in enumerate(self.nodes):
                if QRectF(n["x"], n["y"], 100, 30).contains(e.position()):
                    self.dragging_idx = i
                    if n["fx"] == "reverb" and self.audio_engine.is_active:
                        self.audio_engine.fs.reverb_on(1)
                        self.audio_engine.fs.reverb_setroomsize(0.8)
                    return

    def mouseMoveEvent(self, e: QMouseEvent):
        if self.dragging_idx != -1:
            self.nodes[self.dragging_idx]["x"] = e.position().x()
            self.nodes[self.dragging_idx]["y"] = e.position().y()
            self.update()

    def mouseReleaseEvent(self, e: QMouseEvent): 
        self.dragging_idx = -1

    def paintEvent(self, e: QEvent):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing)
        p.setPen(QPen(QColor("#555"), 2, Qt.DashLine))
        for s, d in self.connections:
            p1 = QPointF(self.nodes[s]["x"]+100, self.nodes[s]["y"]+15)
            p2 = QPointF(self.nodes[d]["x"], self.nodes[d]["y"]+15)
            path = QPainterPath(p1); path.cubicTo(p1.x()+50, p1.y(), p2.x()-50, p2.y(), p2)
            p.drawPath(path)
        p.setFont(QFont("Arial", 8))
        for n in self.nodes:
            p.setBrush(QBrush(QColor(n["color"])))
            p.setPen(QPen(QColor("#000"), 1))
            p.drawRoundedRect(QRectF(n["x"], n["y"], 100, 30), 5, 5)
            p.drawText(QRectF(n["x"], n["y"], 100, 30), Qt.AlignCenter, n["name"])

# ==========================================
# 6. Note Inspector & Mixing Console
# ==========================================
class NoteInspector(QWidget):
    noteChanged = Signal()

    def __init__(self):
        super().__init__()
        self.setMinimumWidth(250)
        layout = QFormLayout(self)
        self.pitch_spin = QSpinBox(); self.pitch_spin.setRange(0, 127)
        self.vel_spin = QSpinBox(); self.vel_spin.setRange(0, 127)
        self.dur_spin = QDoubleSpinBox(); self.dur_spin.setRange(0.25, 16.0); self.dur_spin.setSingleStep(0.25)
        self.dyn_combo = QComboBox(); self.dyn_combo.addItems(["", "pp", "p", "mp", "mf", "f", "ff"])
        self.art_combo = QComboBox()
        self.art_combo.addItems(["legato", "pizz", "spicc", "tremolo", "marcato"])
        
        self.pitch_spin.valueChanged.connect(self.update_note)
        self.vel_spin.valueChanged.connect(self.update_note)
        self.dur_spin.valueChanged.connect(self.update_note)
        self.dyn_combo.currentTextChanged.connect(self.update_note)
        self.art_combo.currentTextChanged.connect(self.update_note)
        
        layout.addRow("Pitch (MIDI):", self.pitch_spin)
        layout.addRow("Velocity:", self.vel_spin)
        layout.addRow("Duration (beats):", self.dur_spin)
        layout.addRow("Dynamic:", self.dyn_combo)
        layout.addRow("Articulation:", self.art_combo)
        self.current_notes: List[Note] = []
        self._updating = False
        
    def set_notes(self, notes: List[Note]):
        self.current_notes = notes
        self.setEnabled(len(notes) > 0)
        if notes:
            self._updating = True
            n = notes[0]
            self.pitch_spin.setValue(n.pitch)
            self.vel_spin.setValue(n.velocity)
            self.dur_spin.setValue(n.duration_beats)
            self.dyn_combo.setCurrentText(n.dynamic)
            self.art_combo.setCurrentText(n.articulation)
            self._updating = False
            
    def update_note(self):
        if self._updating or not self.current_notes: return
        for n in self.current_notes:
            n.pitch = self.pitch_spin.value()
            n.velocity = self.vel_spin.value()
            n.duration_beats = self.dur_spin.value()
            n.dynamic = self.dyn_combo.currentText()
            n.articulation = self.art_combo.currentText()
        self.noteChanged.emit()

class ChannelStrip(QWidget):
    def __init__(self, engine: CadenzaAudioEngine, idx: int, name: str):
        super().__init__()
        self.engine = engine; self.idx = idx
        lay = QVBoxLayout(self)
        lay.addWidget(QLabel(name, alignment=Qt.AlignCenter))

        self.solo = QCheckBox("S"); self.mute = QCheckBox("M")
        row = QHBoxLayout(); row.addWidget(self.solo); row.addWidget(self.mute)
        lay.addLayout(row)

        self.slider = QSlider(Qt.Vertical); self.slider.setRange(0,127); self.slider.setValue(100)
        self.pan = QSlider(Qt.Horizontal); self.pan.setRange(-64, 64); self.pan.setValue(0)
        self.val_lbl = QLabel("100", alignment=Qt.AlignCenter)

        self.slider.valueChanged.connect(self._update)
        self.pan.valueChanged.connect(lambda v: engine.set_pan(idx, v/64.0))
        self.mute.toggled.connect(self._update)

        lay.addWidget(self.slider); lay.addWidget(self.val_lbl)
        lay.addWidget(QLabel("Pan")); lay.addWidget(self.pan)

    def _update(self, v=None):
        if self.mute.isChecked(): self.engine.set_volume(self.idx, 0)
        else: self.engine.set_volume(self.idx, self.slider.value())
        self.val_lbl.setText(str(self.slider.value()))

# ==========================================
# 7. Undo/Redo
# ==========================================
class NotesStateCommand(QUndoCommand):
    def __init__(self, view, old_notes: List[Note], new_notes: List[Note], text: str):
        super().__init__(text)
        self.view = view
        self.old_notes = copy.deepcopy(old_notes)
        self.new_notes = copy.deepcopy(new_notes)

    def undo(self):
        self.view.notes_data = copy.deepcopy(self.old_notes)
        self.view.selected_notes.clear()
        self.view.update()

    def redo(self):
        self.view.notes_data = copy.deepcopy(self.new_notes)
        self.view.selected_notes.clear()
        self.view.update()

class StatefulUndoStack(QUndoStack):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.clean_data: List[Note] = []

    def commit(self, view, text: str):
        self.push(NotesStateCommand(view, self.clean_data, copy.deepcopy(view.notes_data), text))
        self.clean_data = copy.deepcopy(view.notes_data)

# ==========================================
# 8. Score View (Multi-Staff, Grid, Chords, Video Sync)
# ==========================================
class ScoreView(QWidget):
    def __init__(self, audio_engine: CadenzaAudioEngine, undo_stack: StatefulUndoStack):
        super().__init__()
        self.audio_engine = audio_engine
        self.undo_stack = undo_stack
        self.setMinimumSize(1000, 600)
        self.setFocusPolicy(Qt.StrongFocus)
        self.setMouseTracking(True)
        
        self.tempo = 90
        self.grid_mode = False
        self.playhead_beat = 0.0
        
        self.staves = [
            {"name": "Violin I", "clef": "treble", "ch": 0, "b_step": 2, "color": "#4a9eff"},
            {"name": "Violin II", "clef": "treble", "ch": 1, "b_step": 2, "color": "#39ff14"},
            {"name": "Viola", "clef": "alto", "ch": 2, "b_step": -3, "color": "#ff5555"},
            {"name": "Cello", "clef": "bass", "ch": 3, "b_step": -10, "color": "#ff9900"},
            {"name": "Bass", "clef": "bass", "ch": 4, "b_step": -10, "color": "#cc99ff"}
        ]
        
        self.notes_data: List[Note] = [
            Note(pitch=74, start_beat=0, duration_beats=2, staff_id=0, dynamic="mf"),
            Note(pitch=67, start_beat=0, duration_beats=2, staff_id=1),
            Note(pitch=60, start_beat=0, duration_beats=2, staff_id=2),
            Note(pitch=48, start_beat=0, duration_beats=2, staff_id=3),
            Note(pitch=36, start_beat=0, duration_beats=2, staff_id=4),
        ]
        self.chord_symbols: List[ChordSymbol] = [
            ChordSymbol(0, 4, "C", "maj7"),
            ChordSymbol(4, 4, "A", "min7")
        ]
        self.automation: List[AutomationPoint] = [
            AutomationPoint(0, 1, 40, 0), AutomationPoint(4, 1, 90, 0)
        ]
        self.tempo_track: List[TempoPoint] = [TempoPoint(0, self.tempo)]
        self.markers: List[Marker] = [Marker(0, "Intro"), Marker(16, "Theme A")]
        
        self.left_margin = LEFT_MARGIN
        self.base_beat_width = BASE_BEAT_WIDTH
        self.zoom = 1.0
        self.staff_height = STAFF_HEIGHT
        self.score_top = SCORE_TOP
        
        self.selected_notes: Set[Note] = set()
        self.hovered_note: Optional[Note] = None
        
        self.current_tool = "select"
        self.snap_value = 0.5
        
        self.drag_mode = "none"
        self.drag_offset = 0.0
        self.rubber_band_origin = QPointF()
        self.loop_drag_mode = None
        self.dragging_auto_point: Optional[AutomationPoint] = None
        
        self.loop_enabled = False
        self.loop_start = 0.0
        self.loop_end = 16.0

        # Automation UI State
        self.auto_view_staff: int = 0
        self.auto_view_cc: int = 1
        
        # Scale & Ghost State
        self.current_key: str = "C"
        self.current_scale: str = "Minor"
        self.ghost_staves: Set[int] = set()

        # Cached Fonts
        self._font_clef  = QFont("Times", 32, QFont.Bold)
        self._font_label = QFont("Arial", 8, QFont.Bold)
        self._font_dyn   = QFont("Times", 10, QFont.Bold)
        self._font_chord = QFont("Times", 10, QFont.Bold)
        self._font_text  = QFont("Arial", 8)
        
    @property
    def beat_width(self) -> float:
        return self.base_beat_width * self.zoom
        
    def beat_to_x(self, b: float) -> float: return self.left_margin + b * self.beat_width
    def x_to_beat(self, x: float) -> float: return (x - self.left_margin) / self.beat_width
    
    def get_staff_top(self, staff_id: int) -> int: return self.score_top + staff_id * (self.staff_height + STAFF_GAP) + 50

    def pitch_to_y(self, pitch: int, staff_id: int) -> float:
        step, _ = pitch_to_staff_step(pitch)
        b_step = self.staves[staff_id]["b_step"]
        return self.get_staff_top(staff_id) + (b_step - step) * STAFF_LINE_SPACING

    def y_to_pitch(self, y: float, staff_id: int) -> int:
        b_step = self.staves[staff_id]["b_step"]
        step = round(b_step - (y - self.get_staff_top(staff_id)) / STAFF_LINE_SPACING)
        octaves = step // 7
        pc = [0,2,4,5,7,9,11][step % 7]
        return (5 + octaves) * 12 + pc

    def snap_beat(self, beat: float) -> float:
        return round(beat / self.snap_value) * self.snap_value

    def snap_to_scale_pitch(self, pitch: int, beat: float) -> int:
        active_chord = None
        for cs in self.chord_symbols:
            if cs.beat <= beat < cs.beat + cs.duration_beats:
                active_chord = cs
                break
                
        if active_chord:
            root_pc = NOTE_NAMES.index(active_chord.root)
            intervals = CHORD_LIB.get(active_chord.quality, [0, 4, 7])
            valid_pcs = [(root_pc + i) % 12 for i in intervals]
            if pitch % 12 in valid_pcs: return pitch
            for offset in range(1, 5):
                if (pitch - offset) % 12 in valid_pcs: return pitch - offset
                if (pitch + offset) % 12 in valid_pcs: return pitch + offset
            return pitch
            
        if self.current_scale == "Chromatic": return pitch
        root_pc = NOTE_NAMES.index(self.current_key)
        scale_pcs = [(root_pc + s) % 12 for s in SCALES[self.current_scale]]
        if pitch % 12 in scale_pcs: return pitch
        for offset in range(1, 5):
            if (pitch - offset) % 12 in scale_pcs: return pitch - offset
            if (pitch + offset) % 12 in scale_pcs: return pitch + offset
        return pitch

    def get_tempo_at_beat(self, beat: float) -> float:
        if not self.tempo_track: return self.tempo
        pts = sorted(self.tempo_track, key=lambda p: p.beat)
        if beat <= pts[0].beat: return pts[0].bpm
        if beat >= pts[-1].beat: return pts[-1].bpm
        for i in range(len(pts)-1):
            if pts[i].beat <= beat < pts[i+1].beat:
                t = (beat - pts[i].beat) / (pts[i+1].beat - pts[i].beat)
                return pts[i].bpm + (pts[i+1].bpm - pts[i].bpm) * t
        return self.tempo

    def wheelEvent(self, e: QWheelEvent):
        if e.modifiers() & Qt.ControlModifier:
            self.zoom = max(0.25, min(4.0, self.zoom + (e.angleDelta().y() / 120) * 0.1))
            self.update()

    def commit_state(self, text: str):
        self.undo_stack.commit(self, text)

    def mouseDoubleClickEvent(self, e: QMouseEvent):
        if e.position().y() < 30:
            beat = self.snap_beat(self.x_to_beat(e.position().x()))
            val = 120
            self.tempo_track.append(TempoPoint(beat, val))
            self.tempo_track.sort(key=lambda p: p.beat)
            self.update()
            return

        auto_top = self.get_staff_top(4) + 90
        if e.position().y() > auto_top - 20 and e.position().y() < auto_top + 20:
            beat = self.snap_beat(self.x_to_beat(e.position().x()))
            val = int(max(0, min(127, (auto_top - e.position().y() + 40) / 80 * 127)))
            self.automation.append(AutomationPoint(beat, self.auto_view_cc, val, self.auto_view_staff))
            self.automation.sort(key=lambda p: p.beat)
            self.update()
            return

        staff_id = -1
        for i in range(len(self.staves)):
            if self.get_staff_top(i) < e.position().y() < self.get_staff_top(i) + 60:
                staff_id = i; break
        if staff_id == -1: return
        
        m_num = int(self.x_to_beat(e.position().x()) / 4)
        dlg = PianoRollDialog(self.notes_data, m_num, staff_id, self)
        dlg.exec()
        self.commit_state("Edit Piano Roll")
        self.update()

    def mousePressEvent(self, e: QMouseEvent):
        self.undo_stack.clean_data = copy.deepcopy(self.notes_data)
        
        if self.grid_mode:
            self._handle_grid_click(e)
            return
            
        if e.position().y() < 30:
            x = e.position().x()
            lx_start = self.beat_to_x(self.loop_start)
            lx_end = self.beat_to_x(self.loop_end)
            if abs(x - lx_start) < 6: self.loop_drag_mode = "start"; return
            elif abs(x - lx_end) < 6: self.loop_drag_mode = "end"; return
            else:
                self.playhead_beat = max(0, self.x_to_beat(e.position().x()))
                main_win = self.window()
                if hasattr(main_win, 'video_player') and main_win.video_player.source() != QUrl():
                    target_ms = int((self.playhead_beat / self.get_tempo_at_beat(self.playhead_beat)) * 60000)
                    main_win.video_player.setPosition(target_ms)
                self.update(); return

        auto_top = self.get_staff_top(4) + 90
        if e.position().y() > auto_top - 20 and e.position().y() < auto_top + 20:
            if e.button() == Qt.RightButton:
                closest_pt = None
                min_dist = 20
                for pt in self.automation:
                    if pt.staff_id != self.auto_view_staff or pt.cc_type != self.auto_view_cc: continue
                    dist = abs(self.beat_to_x(pt.beat) - e.position().x())
                    if dist < min_dist: min_dist = dist; closest_pt = pt
                if closest_pt:
                    self.automation.remove(closest_pt)
                    self.update()
                return
            
            for pt in self.automation:
                if pt.staff_id != self.auto_view_staff or pt.cc_type != self.auto_view_cc: continue
                if abs(self.beat_to_x(pt.beat) - e.position().x()) < 8:
                    self.dragging_auto_point = pt
                    return

        if e.button() == Qt.LeftButton:
            for n in self.notes_data:
                x = self.beat_to_x(n.start_beat)
                y = self.pitch_to_y(n.pitch, n.staff_id)
                note_rect = QRectF(x, y-8, max(20, n.duration_beats * self.beat_width), 16)
                vel_rect = QRectF(x, y+8, max(20, n.duration_beats * self.beat_width), 15)
                
                if self.current_tool == "velocity" and vel_rect.contains(e.position()):
                    self.drag_mode = "velocity"
                    self.selected_notes = {n}
                    self.update()
                    return

                if note_rect.contains(e.position()):
                    if self.current_tool == "erase":
                        self.notes_data.remove(n)
                        self.commit_state("Erase Note")
                        return
                    if abs(e.position().x() - (x + n.duration_beats * self.beat_width)) < 6:
                        self.drag_mode = "resize"
                        if not e.modifiers() & Qt.ControlModifier: self.selected_notes = {n}
                        else: self.selected_notes.add(n)
                    else:
                        self.drag_mode = "move"
                        if not e.modifiers() & Qt.ControlModifier: self.selected_notes = {n}
                        else: self.selected_notes.add(n)
                        self.drag_offset = self.x_to_beat(e.position().x()) - n.start_beat
                    self.update()
                    return
            
            staff_id = -1
            for i in range(len(self.staves)):
                if self.get_staff_top(i) < e.position().y() < self.get_staff_top(i) + 60:
                    staff_id = i; break
                    
            if self.current_tool == "draw" and staff_id != -1:
                beat = self.snap_beat(self.x_to_beat(e.position().x()))
                raw_pitch = self.y_to_pitch(e.position().y(), staff_id)
                pitch = self.snap_to_scale_pitch(raw_pitch, beat)
                n = Note(pitch, beat, 1.0, 90, 1, 0, staff_id)
                self.notes_data.append(n)
                self.selected_notes = {n}
                self.drag_mode = "move"
                self.drag_offset = 0.0
                self.audio_engine.note_on(pitch, 90, self.staves[staff_id]["ch"])
                QTimer.singleShot(300, lambda p=pitch, c=self.staves[staff_id]["ch"]: self.audio_engine.note_off(p, c))
                self.commit_state("Draw Note")
            else:
                if not (e.modifiers() & Qt.ControlModifier):
                    self.selected_notes.clear()
                self.drag_mode = "rubber_band"
                self.rubber_band_origin = e.position()
                self.update()

        elif e.button() == Qt.RightButton and self.current_tool == "erase":
            for n in self.notes_data:
                x = self.beat_to_x(n.start_beat)
                y = self.pitch_to_y(n.pitch, n.staff_id)
                if QRectF(x, y-8, 20, 16).contains(e.position()):
                    self.notes_data.remove(n)
                    self.commit_state("Erase Note")
                    break

    def _handle_grid_click(self, e: QMouseEvent):
        staff_id = -1
        for i in range(len(self.staves)):
            y_start = 50 + i * 120
            if y_start < e.position().y() < y_start + (24 * 5):
                staff_id = i
                break
        if staff_id == -1: return
        beat = self.snap_beat(self.x_to_beat(e.position().x()))
        if beat < 0: return
        y_start = 50 + staff_id * 120
        py = int((e.position().y() - y_start) / 5)
        pitch = 72 - py
        
        existing = [n for n in self.notes_data if n.staff_id == staff_id and n.start_beat == beat and n.pitch == pitch]
        if existing:
            for n in existing: self.notes_data.remove(n)
        else:
            n = Note(pitch, beat, self.snap_value, 90, 1, 0, staff_id)
            self.notes_data.append(n)
            self.audio_engine.note_on(pitch, 90, self.staves[staff_id]["ch"])
            QTimer.singleShot(150, lambda p=pitch, c=self.staves[staff_id]["ch"]: self.audio_engine.note_off(p, c))
        self.update()

    def mouseMoveEvent(self, e: QMouseEvent):
        if self.loop_drag_mode:
            beat = self.snap_beat(self.x_to_beat(e.position().x()))
            if self.loop_drag_mode == "start": self.loop_start = min(beat, self.loop_end - 1)
            else: self.loop_end = max(beat, self.loop_start + 1)
            self.update(); return

        if self.dragging_auto_point:
            self.dragging_auto_point.beat = self.snap_beat(self.x_to_beat(e.position().x()))
            auto_top = self.get_staff_top(4) + 90
            self.dragging_auto_point.value = int(max(0, min(127, (auto_top - e.position().y() + 40) / 80 * 127)))
            self.automation.sort(key=lambda p: p.beat)
            self.update(); return

        if self.drag_mode == "move":
            for n in self.selected_notes:
                staff_id = -1
                for i in range(len(self.staves)):
                    if self.get_staff_top(i) < e.position().y() < self.get_staff_top(i) + 60:
                        staff_id = i; break
                if staff_id != -1:
                    n.staff_id = staff_id
                    n.pitch = self.y_to_pitch(e.position().y(), staff_id)
                n.start_beat = max(0, self.snap_beat(self.x_to_beat(e.position().x()) - self.drag_offset))
            self.update(); return
            
        elif self.drag_mode == "resize":
            for n in self.selected_notes:
                new_dur = self.snap_beat(self.x_to_beat(e.position().x()) - n.start_beat)
                n.duration_beats = max(0.25, new_dur)
            self.update(); return

        elif self.drag_mode == "velocity":
            for n in self.selected_notes:
                y = e.position().y()
                n.velocity = max(10, min(127, int(127 - (y - self.pitch_to_y(n.pitch, n.staff_id) - 8) / 15 * 127)))
            self.update(); return

        elif self.drag_mode == "rubber_band":
            rect = QRectF(self.rubber_band_origin, e.position()).normalized()
            self.selected_notes.clear()
            for n in self.notes_data:
                x = self.beat_to_x(n.start_beat)
                y = self.pitch_to_y(n.pitch, n.staff_id)
                if rect.intersects(QRectF(x, y-8, max(20, n.duration_beats * self.beat_width), 16)):
                    self.selected_notes.add(n)
            self.update(); return

        hovered = None
        cursor = Qt.ArrowCursor
        for n in self.notes_data:
            x = self.beat_to_x(n.start_beat)
            y = self.pitch_to_y(n.pitch, n.staff_id)
            note_rect = QRectF(x, y-8, max(20, n.duration_beats * self.beat_width), 16)
            if note_rect.contains(e.position()):
                hovered = n
                if self.current_tool == "erase": cursor = Qt.PointingHandCursor
                elif abs(e.position().x() - (x + n.duration_beats * self.beat_width)) < 6: cursor = Qt.SizeHorCursor
                else: cursor = Qt.OpenHandCursor
                break
        
        if hovered != self.hovered_note:
            self.hovered_note = hovered
            if hovered:
                pitch_name = NOTE_NAMES[hovered.pitch % 12] + str(hovered.pitch // 12 - 1)
                QToolTip.showText(e.globalPosition().toPoint(), f"{pitch_name}\nVel: {hovered.velocity}", self)
            else:
                QToolTip.hideText()
            self.update()
        self.setCursor(cursor)

    def mouseReleaseEvent(self, e: QMouseEvent):
        if self.loop_drag_mode: self.loop_drag_mode = None; return
        if self.dragging_auto_point: self.dragging_auto_point = None; return

        if self.drag_mode in ["move", "resize", "velocity", "draw"]:
            self.commit_state(f"{self.drag_mode.capitalize()} Note(s)")
            if self.hovered_note:
                n = self.hovered_note
                self.audio_engine.note_on(n.pitch, n.velocity, self.staves[n.staff_id]["ch"])
                QTimer.singleShot(200, lambda p=n.pitch, c=self.staves[n.staff_id]["ch"]: self.audio_engine.note_off(p, c))
        
        self.drag_mode = "none"
        self.setCursor(Qt.ArrowCursor)
        win = self.window()
        if hasattr(win, "update_inspector"): win.update_inspector()

    def keyPressEvent(self, e: QKeyEvent):
        if e.key() == Qt.Key_Delete:
            if self.selected_notes:
                for n in list(self.selected_notes):
                    if n in self.notes_data: self.notes_data.remove(n)
                self.selected_notes.clear()
                self.commit_state("Delete Notes")
                self.update()

    def contextMenuEvent(self, e: QEvent):
        beat = self.snap_beat(self.x_to_beat(e.position().x()))
        menu = QMenu(self)
        add_marker_act = menu.addAction(f"Add Marker at Beat {beat}")
        chord_menu = menu.addMenu("Set Chord Track Here")
        roots_menu = chord_menu.addMenu("Root")
        root_actions = {r: roots_menu.addAction(r) for r in NOTE_NAMES}
        qual_menu = chord_menu.addMenu("Quality")
        qual_actions = {q: qual_menu.addAction(q) for q in CHORD_LIB.keys()}

        staff_id = -1
        for i in range(len(self.staves)):
            if self.get_staff_top(i) < e.position().y() < self.get_staff_top(i) + 60:
                staff_id = i; break
        ghost_action = menu.addAction(f"Toggle Ghost Track ({self.staves[staff_id]['name']})") if staff_id != -1 else None
        
        action = menu.exec(e.globalPos())
        
        if action == add_marker_act:
            name, ok = QInputDialog().getText(self, "Add Marker", "Marker Name:")
            if ok and name:
                self.markers.append(Marker(beat, name))
                self.markers.sort(key=lambda m: m.beat)
                self.update()
        elif action == ghost_action and staff_id != -1:
            if staff_id in self.ghost_staves: self.ghost_staves.remove(staff_id)
            else: self.ghost_staves.add(staff_id)
            self.update()
        elif action in root_actions.values():
            root = [r for r, a in root_actions.items() if a == action][0]
            self.chord_symbols.append(ChordSymbol(beat, 4.0, root, "maj"))
            self.chord_symbols.sort(key=lambda c: c.beat)
            self.update()

    def paintEvent(self, e: QEvent):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing)
        p.fillRect(self.rect(), QColor("#1e1e1e"))
        
        total_beats = max([n.start_beat + n.duration_beats for n in self.notes_data], default=16) + 4
        if not self.loop_enabled or self.loop_end == 16.0:
            self.loop_end = total_beats
        
        self._draw_ruler(p, total_beats)
        
        if self.grid_mode:
            self._draw_grid_mode(p, total_beats)
        else:
            self._draw_score_mode(p, total_beats)
            
        if self.loop_enabled:
            lx_start = self.beat_to_x(self.loop_start)
            lx_end = self.beat_to_x(self.loop_end)
            p.fillRect(QRectF(lx_start, 30, lx_end - lx_start, self.height()-30), QColor(255, 100, 100, 20))
            p.setBrush(QBrush(QColor("#ff5555")))
            p.drawPolygon(QPointF(lx_start, 0), QPointF(lx_start+6, 0), QPointF(lx_start, 8))
            p.drawPolygon(QPointF(lx_end, 0), QPointF(lx_end-6, 0), QPointF(lx_end, 8))
            
        ph_x = self.beat_to_x(self.playhead_beat)
        p.setPen(QPen(QColor("#ff5555"), 2))
        p.drawLine(ph_x, 30, ph_x, self.height())
        
        m = int(self.playhead_beat / 4) + 1
        b = int(self.playhead_beat % 4) + 1
        p.setPen(QColor("#fff"))
        p.drawText(QRectF(ph_x + 4, 4, 80, 22), Qt.AlignLeft, f"{m}.{b}")

        if self.drag_mode == "rubber_band":
            p.setPen(QPen(QColor("#4a9eff"), 1, Qt.DashLine))
            p.setBrush(QBrush(QColor(74, 158, 255, 30)))
            p.drawRect(QRectF(self.rubber_band_origin, self.mapFromGlobal(QCursor.pos())).normalized())

    def _draw_ruler(self, p: QPainter, total_beats: float):
        p.setBrush(QColor("#252525")); p.setPen(Qt.NoPen)
        p.drawRect(0, 0, self.width(), 30)
        p.setPen(QPen(QColor("#555"), 1))
        for m in range(int(total_beats / 4) + 2):
            x = self.beat_to_x(m * 4)
            p.drawLine(x, 0, x, 30)
            p.setPen(QColor("#aaa")); p.setFont(self._font_label)
            p.drawText(QRectF(x + 2, 2, 40, 20), Qt.AlignLeft, f"{m+1}")
            p.setPen(QPen(QColor("#555"), 1))
            for b in range(1, 4):
                bx = self.beat_to_x(m * 4 + b)
                p.drawLine(bx, 20, bx, 30)
                
        if self.tempo_track:
            path = QPainterPath()
            pts = sorted(self.tempo_track, key=lambda p: p.beat)
            for i, pt in enumerate(pts):
                x = self.beat_to_x(pt.beat)
                y = 26 - ((max(40, min(200, pt.bpm)) - 40) / 160.0) * 22
                if i == 0: path.moveTo(x, y)
                else: path.lineTo(x, y)
                p.setBrush(QBrush(QColor("#ffcc00")))
                p.drawEllipse(QPointF(x, y), 3, 3)
            p.setPen(QPen(QColor("#ffcc00"), 1.5))
            p.drawPath(path)
        
    def _draw_score_mode(self, p: QPainter, total_beats: float):
        marker_top = 35
        chord_top = 50
        p.setPen(QPen(QColor("#333"), 1))
        p.drawLine(self.left_margin, chord_top + 20, self.beat_to_x(total_beats), chord_top + 20)
        
        for cs in self.chord_symbols:
            x1 = self.beat_to_x(cs.beat)
            x2 = self.beat_to_x(cs.beat + cs.duration_beats)
            p.fillRect(QRectF(x1, chord_top, x2 - x1, 20), QColor(255, 204, 0, 40))
            p.setPen(QColor("#ffcc00")); p.setFont(self._font_chord)
            p.drawText(QRectF(x1 + 4, chord_top, 100, 20), Qt.AlignLeft | Qt.AlignVCenter, f"{cs.root}{cs.quality}")
            
        for m in self.markers:
            x = self.beat_to_x(m.beat)
            p.setPen(QPen(QColor("#4a9eff"), 2))
            p.drawLine(x, marker_top, x, marker_top + 15)
            p.fillRect(QRectF(x+1, marker_top, 60, 15), QColor("#4a9eff"))
            p.setPen(QColor("#fff")); p.setFont(self._font_label)
            p.drawText(QRectF(x+3, marker_top, 60, 15), Qt.AlignLeft | Qt.AlignVCenter, m.name)

        for i, staff in enumerate(self.staves):
            top = self.get_staff_top(i)
            p.setPen(QPen(QColor("#ccc"), 1))
            for j in range(5):
                p.drawLine(self.left_margin, top + j * 15, self.beat_to_x(total_beats), top + j * 15)
            p.setPen(QColor("#e0e0e0")); p.setFont(self._font_clef)
            clef_char = {"treble": "𝄞", "alto": "𝄡", "bass": "𝄢"}.get(staff["clef"], "𝄞")
            p.drawText(QRectF(60, top - 15, 60, 70), Qt.AlignCenter, clef_char)
            p.setPen(QColor("#888")); p.setFont(self._font_label)
            p.drawText(QRectF(10, top + 20, 50, 20), Qt.AlignLeft, staff["name"])
            
        for m in range(int(total_beats / 4) + 1):
            x = self.beat_to_x(m * 4)
            p.setPen(QPen(QColor("#888"), 1))
            p.drawLine(x, self.get_staff_top(0), x, self.get_staff_top(4) + 60)

        for n in self.notes_data:
            self._draw_note(p, n)
            
        auto_top = self.get_staff_top(4) + 90
        p.setPen(QColor("#333")); p.drawLine(self.left_margin, auto_top, self.width(), auto_top)
        visible_auto = [pt for pt in self.automation if pt.staff_id == self.auto_view_staff and pt.cc_type == self.auto_view_cc]
        p.setPen(QColor("#39ff14")); p.setFont(self._font_text)
        staff_name = self.staves[self.auto_view_staff]["name"]
        cc_name = {1: "CC1 Mod", 7: "CC7 Vol", 11: "CC11 Expr", 74: "CC74 Bright"}.get(self.auto_view_cc, f"CC{self.auto_view_cc}")
        p.drawText(10, auto_top + 4, f"{staff_name} - {cc_name}")
        path = QPainterPath()
        for i, pt in enumerate(visible_auto):
            x = self.beat_to_x(pt.beat)
            y = auto_top - (pt.value / 127 * 40)
            if i == 0: path.moveTo(x, y)
            else: path.lineTo(x, y)
            p.setBrush(QBrush(QColor("#39ff14")))
            p.drawEllipse(QPointF(x, y), 4, 4)
        p.setPen(QPen(QColor("#39ff14"), 2)); p.drawPath(path)

    def _draw_note(self, p: QPainter, n: Note):
        staff = self.staves[n.staff_id]
        color = QColor(staff["color"])
        x = self.beat_to_x(n.start_beat)
        y = self.pitch_to_y(n.pitch, n.staff_id)
        
        is_ghost = n.staff_id in self.ghost_staves
        if is_ghost: color.setAlpha(60)
        
        if n in self.selected_notes:
            p.setPen(QPen(QColor("#fff"), 2)); p.setBrush(QBrush(QColor(color)))
            p.drawRoundedRect(QRectF(x-2, y-10, n.duration_beats * self.beat_width + 4, 20), 3, 3)
        elif n == self.hovered_note and not is_ghost:
            color = "#ffffff"
            
        p.setPen(QPen(QColor(color), 1 if not is_ghost else 0))
        p.setBrush(QBrush(QColor(color)))
        
        p.setPen(QPen(QColor(color), 2 if not is_ghost else 1))
        p.setBrush(Qt.NoBrush if (n.duration_beats >= 2.0 and not is_ghost) else QBrush(QColor(color)))
        p.drawEllipse(QPointF(x + 8, y), 8, 6)
            
        stem_x = x + 16 if n.pitch >= 60 else x
        p.setPen(QPen(QColor(color), 2 if not is_ghost else 1))
        p.drawLine(stem_x, y, stem_x, y + (35 if n.pitch < 60 else -35))
        
        vel_h = int(n.velocity / 127 * 15)
        p.drawLine(x + 4, y + 8, x + 4, y + 8 + vel_h)
        
        if n.articulation == "staccato":
            p.setBrush(QBrush(QColor(color)))
            p.drawEllipse(QPointF(x + 8, y + (15 if n.pitch < 60 else -15)), 2, 2)
        elif n.articulation == "marcato":
            p.drawLine(x + 2, y - 20, x + 14, y - 20)
            
        if n.dynamic and not is_ghost:
            p.setPen(QColor("#44aaff")); p.setFont(self._font_dyn)
            p.drawText(QRectF(x, y + 30, 20, 15), Qt.AlignCenter, n.dynamic)

    def _draw_grid_mode(self, p: QPainter, total_beats: float):
        p.setPen(QColor("#555")); p.setFont(self._font_text)
        notes_by_staff: Dict[int, List[Note]] = {i: [] for i in range(len(self.staves))}
        for n in self.notes_data: notes_by_staff[n.staff_id].append(n)

        for i, staff in enumerate(self.staves):
            y = 50 + i * 120
            p.setPen(QColor("#888"))
            p.drawText(10, y + 15, staff["name"])
            for j in range(24):
                py = y + j * 5
                pc = 72 - j
                is_black = pc % 12 in {1,3,6,8,10}
                p.setPen(QPen(QColor("#222"), 1))
                p.drawLine(100, py, self.beat_to_x(total_beats), py)
                if is_black:
                    p.fillRect(100, py, self.beat_to_x(total_beats)-100, 5, QColor("#222"))
            for n in notes_by_staff.get(i, []):
                nx = self.beat_to_x(n.start_beat)
                ny = y + (72 - n.pitch) * 5
                c = "#fff" if n in self.selected_notes else staff["color"]
                p.setBrush(QBrush(QColor(c))); p.setPen(QPen(QColor("#fff"), 1))
                p.drawRect(nx, ny, n.duration_beats * self.beat_width, 4)

# ==========================================
# 9. Spatial Mixer (3D)
# ==========================================
class SpatialMixer(QWidget):
    def __init__(self, engine: CadenzaAudioEngine):
        super().__init__()
        self.engine = engine
        self.setMinimumSize(280, 280)
        self.instruments = [
            {"name": "Vln I", "x": 0.3, "y": 0.2, "ch": 0},
            {"name": "Vln II", "x": 0.4, "y": 0.3, "ch": 1},
            {"name": "Vla", "x": 0.6, "y": 0.5, "ch": 2},
            {"name": "Vlc", "x": 0.7, "y": 0.7, "ch": 3},
            {"name": "Cb", "x": 0.8, "y": 0.8, "ch": 4}
        ]
        self.drag_idx = -1
        for inst in self.instruments:
            self.engine.set_reverb_send(inst["ch"], int(inst["y"] * 127))

    def mousePressEvent(self, e: QMouseEvent):
        for i, inst in enumerate(self.instruments):
            ix = inst["x"]*self.width()
            iy = inst["y"]*self.height()
            if (e.position().x() - ix)**2 + (e.position().y() - iy)**2 < 400:
                self.drag_idx = i; return

    def mouseMoveEvent(self, e: QMouseEvent):
        if self.drag_idx != -1:
            inst = self.instruments[self.drag_idx]
            inst["x"] = max(0, min(1, e.position().x() / self.width()))
            inst["y"] = max(0, min(1, e.position().y() / self.height()))
            pan = (inst["x"] - 0.5) * 2.0
            self.engine.set_pan(inst["ch"], pan)
            self.engine.set_reverb_send(inst["ch"], int(inst["y"] * 127))
            self.update()

    def mouseReleaseEvent(self, e: QMouseEvent): self.drag_idx = -1

    def paintEvent(self, e: QEvent):
        p = QPainter(self); p.setRenderHint(QPainter.Antialiasing)
        p.setBrush(QBrush(QColor("#252525"))); p.setPen(QPen(QColor("#444"), 2))
        p.drawEllipse(QRectF(20, 20, self.width()-40, self.height()-40))
        p.setPen(QPen(QColor("#444"), 1, Qt.DashLine))
        p.drawLine(20, self.height()/2, self.width()-20, self.height()/2)
        p.setPen(QColor("#888")); p.setFont(QFont("Arial", 7))
        p.drawText(5, 15, "Dry/Front")
        p.drawText(5, self.height()-5, "Wet/Back")
        
        for inst in self.instruments:
            x, y = inst["x"]*self.width(), inst["y"]*self.height()
            depth = inst["y"]
            radius = 14 - (depth * 6)
            alpha = 255 - int(depth * 100)
            color = QColor("#4a9eff")
            color.setAlpha(alpha)
            p.setBrush(QBrush(color)); p.setPen(QPen(QColor("#000"), 1))
            p.drawEllipse(QPointF(x, y), radius, radius)
            p.setPen(QPen(QColor("#fff"))); p.setFont(QFont("Arial", 8))
            p.drawText(QRectF(x-20, y+radius+2, 40, 12), Qt.AlignCenter, inst["name"])

# ==========================================
# 10. WAV Rendering Thread
# ==========================================
class RenderThread(QThread):
    progress = Signal(int)
    failed = Signal(str)

    def __init__(self, sf_path, notes_data, tempo, staves, base_filepath, stems_mode=False):
        super().__init__()
        self.sf_path = sf_path
        self.notes_data = notes_data
        self.tempo = tempo
        self.staves = staves
        self.base_filepath = base_filepath
        self.stems_mode = stems_mode

    def run(self):
        if not self.sf_path:
            self.failed.emit("No SoundFont loaded"); return
        wav = None
        try:
            fs = fluidsynth.Synth(gain=0.8)
            sf_id = fs.sfload(self.sf_path)
            for i in range(5): fs.program_select(i, sf_id, 0, 48)
            
            tracks_to_render = self.staves if self.stems_mode else [{"name": "FullMix", "ch": -1}]
            
            for track_idx, track in enumerate(tracks_to_render):
                if self.stems_mode:
                    for i in range(5): fs.cc(i, 7, 0)
                    fs.cc(track["ch"], 7, 100)
                
                events = []
                for n in self.notes_data:
                    if self.stems_mode and n.staff_id != track_idx: continue
                    ch = self.staves[n.staff_id]["ch"]
                    start_tick = int(n.start_beat * 480)
                    end_tick = int((n.start_beat + n.duration_beats) * 480)
                    events.append((start_tick, 0x90 | ch, n.pitch, n.velocity))
                    events.append((end_tick, 0x80 | ch, n.pitch, 0))
                events.sort(key=lambda x: (x[0], x[1]))
                
                sample_rate = 44100
                total_ticks = max([e[0] for e in events], default=480) + 480
                total_seconds = (total_ticks / 480) * (60.0 / self.tempo)
                total_samples = int(total_seconds * sample_rate)
                
                filepath = f"{self.base_filepath}_{track['name'].replace(' ', '')}.wav" if self.stems_mode else self.base_filepath
                wav = wave.open(filepath, "wb")
                wav.setnchannels(2); wav.setsampwidth(2); wav.setframerate(sample_rate)
                
                current_sample = 0
                chunk_size = 1024
                
                while current_sample < total_samples:
                    target_tick = (current_sample + chunk_size) / sample_rate * (self.tempo * 480 / 60.0)
                    while events and events[0][0] <= target_tick:
                        ev = events.pop(0)
                        if (ev[1] & 0xF0) == 0x90: fs.noteon(ev[1] & 0x0F, ev[2], ev[3])
                        else: fs.noteoff(ev[1] & 0x0F, ev[2])
                    
                    samples = fs.get_samples(chunk_size)
                    pcm = b''
                    for s in samples:
                        pcm += struct.pack('<h', int(max(-1.0, min(1.0, s)) * 32767))
                    wav.writeframes(pcm)
                    current_sample += chunk_size
                    self.progress.emit(int(current_sample / total_samples * 100))
                wav.close()
                wav = None
        except Exception as e:
            self.failed.emit(str(e))
        finally:
            if wav: wav.close()

# ==========================================
# 11. Python Scripting Console
# ==========================================
class ScriptConsole(QWidget):
    def __init__(self, main_window):
        super().__init__()
        self.main_window = main_window
        layout = QVBoxLayout(self)
        layout.setContentsMargins(2, 2, 2, 2)
        
        self.output = QPlainTextEdit()
        self.output.setReadOnly(True)
        self.output.setStyleSheet("background-color: #111; color: #39ff14; font-family: Consolas, monospace;")
        
        self.input = QLineEdit()
        self.input.setStyleSheet("background-color: #111; color: #ddd; font-family: Consolas, monospace;")
        self.input.setPlaceholderText("Type Python command... e.g. [n.pitch += 12 for n in score.selected_notes]")
        
        layout.addWidget(self.output)
        layout.addWidget(self.input)
        
        self.input.returnPressed.connect(self.execute)
        
        self.globals = {
            'score': main_window.score_view,
            'audio': main_window.audio_engine,
            'main': main_window,
            'Note': Note,
            'ChordSymbol': ChordSymbol,
            'AutomationPoint': AutomationPoint,
            'TempoPoint': TempoPoint
        }
        
    def execute(self):
        cmd = self.input.text()
        if not cmd: return
        self.input.clear()
        self.output.appendPlainText(f">>> {cmd}")
        
        old_stdout = sys.stdout
        class StreamRedirector:
            def __init__(self, target): self.target = target
            def write(self, text): self.target.appendPlainText(text)
            def flush(self): pass
        sys.stdout = StreamRedirector(self.output)
        
        try:
            try:
                result = eval(cmd, self.globals)
                if result is not None: print(result)
            except SyntaxError:
                exec(cmd, self.globals)
        except Exception as e:
            print(f"Error: {e}")
            print(traceback.format_exc())
        finally:
            sys.stdout = old_stdout
            self.main_window.score_view.update()

# ==========================================
# 12. Main Window & DAW Logic
# ==========================================
class CadenzaMainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("Cadenza — Orchestral DAW v5.0")
        self.resize(1400, 900)
        self.audio_engine = CadenzaAudioEngine()
        self.undo_stack = StatefulUndoStack(self)
        self.undo_stack.clean_data = []
        
        self.setup_ui()
        self.setup_menu()
        self.setup_shortcuts()
        
        self.playhead_beat = 0.0
        self.playback_timer = QTimer(self)
        self.playback_timer.timeout.connect(self.update_playback)
        self.is_playing = False
        self.last_time = 0.0
        self.currently_playing_notes: Set[Tuple[int, int, int]] = set()
        self.auditioned_notes = {}
        self.live_octave = 3
        
        self.midi_clock_timer = QTimer(self)
        self.midi_clock_timer.timeout.connect(self._pulse_midi_clock)
        
        if self.audio_engine.is_active and self.audio_engine.midi_in:
            self.audio_engine.set_midi_callback(self.handle_midi_input)

    def setup_ui(self):
        cw = QWidget(); self.setCentralWidget(cw)
        lay = QVBoxLayout(cw); lay.setContentsMargins(0,0,0,0); lay.setSpacing(0)
        lay.addWidget(self.create_transport())
        
        main_splitter = QSplitter(Qt.Horizontal)
        self.tool_bar = QToolBar("Tools")
        self.tool_bar.setMovable(False)
        self.tool_group = QButtonGroup(self)
        self.tool_group.setExclusive(True)
        
        tools = [("Select", "select", Qt.ArrowCursor), ("Draw", "draw", Qt.CrossCursor), 
                 ("Erase", "erase", Qt.PointingHandCursor), ("Velocity", "velocity", Qt.SizeVerCursor)]
        for name, tool_id, cursor in tools:
            btn = QToolButton()
            btn.setText(name)
            btn.setCheckable(True)
            btn.setProperty("tool_id", tool_id)
            btn.setProperty("cursor", cursor)
            btn.clicked.connect(lambda checked, t=tool_id, c=cursor: self.set_tool(t, c))
            self.tool_group.addButton(btn)
            self.tool_bar.addWidget(btn)
        self.tool_group.buttons()[0].click()
        
        self.score_view = ScoreView(self.audio_engine, self.undo_stack)
        scroll = QScrollArea(); scroll.setWidget(self.score_view); scroll.setWidgetResizable(True)
        
        main_splitter.addWidget(self.tool_bar)
        main_splitter.addWidget(scroll)
        main_splitter.setSizes([50, 1350])
        lay.addWidget(main_splitter)
        
        self.patcher_dock = QDockWidget("Patcher (FX Routing)", self)
        self.patcher_dock.setWidget(PatcherView(self.audio_engine))
        self.addDockWidget(Qt.BottomDockWidgetArea, self.patcher_dock)
        
        self.mixer_dock = QDockWidget("Spatial Mixer", self)
        self.mixer_dock.setWidget(SpatialMixer(self.audio_engine))
        self.addDockWidget(Qt.RightDockWidgetArea, self.mixer_dock)
        
        self.console_dock = QDockWidget("Mixing Console", self)
        mixer_widget = QWidget()
        mixer_layout = QHBoxLayout(mixer_widget)
        for i, staff in enumerate(self.score_view.staves):
            mixer_layout.addWidget(ChannelStrip(self.audio_engine, i, staff["name"]))
        self.console_dock.setWidget(mixer_widget)
        self.addDockWidget(Qt.BottomDockWidgetArea, self.console_dock)
        
        self.inspector = NoteInspector()
        self.inspector.noteChanged.connect(lambda: self.score_view.update())
        self.inspector_dock = QDockWidget("Note Inspector", self)
        self.inspector_dock.setWidget(self.inspector)
        self.addDockWidget(Qt.RightDockWidgetArea, self.inspector_dock)

        self.video_dock = QDockWidget("Video Sync", self)
        self.video_widget = QVideoWidget()
        self.video_player = QMediaPlayer()
        self.video_player.setVideoOutput(self.video_widget)
        self.video_dock.setWidget(self.video_widget)
        self.addDockWidget(Qt.BottomDockWidgetArea, self.video_dock)
        self.video_dock.hide()
        
        self.console_script = QDockWidget("Python REPL", self)
        self.console = ScriptConsole(self)
        self.console_script.setWidget(self.console)
        self.addDockWidget(Qt.BottomDockWidgetArea, self.console_script)

        ins_dock = QDockWidget("Orchestral Tools", self)
        w = QWidget(); f = QFormLayout(w)
        self.humanize_btn = QPushButton("Apply Humanize"); self.humanize_btn.clicked.connect(self.humanize)
        self.divisi_btn = QPushButton("Smart Auto-Divisi"); self.divisi_btn.clicked.connect(self.auto_divisi)
        self.ostinato_btn = QPushButton("Generate Ostinato"); self.ostinato_btn.clicked.connect(self.generate_ostinato)
        
        self.invert_btn = QPushButton("Invert Pitch (Mirror)")
        self.invert_btn.clicked.connect(lambda: self.transform_notes("invert"))
        self.retro_btn = QPushButton("Retrograde (Reverse)")
        self.retro_btn.clicked.connect(lambda: self.transform_notes("retrograde"))
        self.harmonize_btn = QPushButton("Auto-Harmonize (Chords)")
        self.harmonize_btn.clicked.connect(self.auto_harmonize)
        
        self.cresc_btn = QPushButton("Add Crescendo (CC11)")
        self.cresc_btn.clicked.connect(lambda: self.add_hairpin(True))
        self.dim_btn = QPushButton("Add Diminuendo (CC11)")
        self.dim_btn.clicked.connect(lambda: self.add_hairpin(False))
        
        self.clear_btn = QPushButton("Clear Score"); self.clear_btn.setStyleSheet("background-color: #553333;")
        self.clear_btn.clicked.connect(self.clear_score)
        
        self.grid_toggle = QCheckBox("Step Sequencer View")
        self.grid_toggle.toggled.connect(lambda s: setattr(self.score_view, 'grid_mode', s))
        self.grid_toggle.toggled.connect(lambda: self.score_view.update())
        
        f.addRow(self.grid_toggle)
        f.addRow(self.humanize_btn); f.addRow(self.divisi_btn)
        f.addRow(self.ostinato_btn)
        f.addRow(QLabel("--- Transform ---"))
        f.addRow(self.invert_btn); f.addRow(self.retro_btn)
        f.addRow(self.harmonize_btn)
        f.addRow(QLabel("--- Expression ---"))
        f.addRow(self.cresc_btn); f.addRow(self.dim_btn)
        f.addRow(QLabel("--- Project ---"))
        f.addRow(self.clear_btn)
        ins_dock.setWidget(w)
        self.addDockWidget(Qt.LeftDockWidgetArea, ins_dock)

    def create_transport(self) -> QFrame:
        f = QFrame(); f.setStyleSheet("background-color: #2b2b2b;")
        l = QHBoxLayout(f)
        self.play_btn = QPushButton("▶ Play"); self.play_btn.clicked.connect(self.toggle_play)
        self.play_btn.setToolTip("Space - Start/Pause playback")
        self.stop_btn = QPushButton("■ Stop"); self.stop_btn.clicked.connect(self.stop_play)
        self.stop_btn.setToolTip("Stop and rewind to start")
        
        self.loop_btn = QPushButton("↻ Loop")
        self.loop_btn.setCheckable(True)
        self.loop_btn.toggled.connect(self.toggle_loop)
        self.loop_btn.setToolTip("Toggle loop region (drag handles in ruler)")
        
        self.tempo_spin = QSpinBox(); self.tempo_spin.setRange(40, 240)
        self.tempo_spin.setValue(self.score_view.tempo)
        self.tempo_spin.setSuffix(" BPM")
        self.tempo_spin.valueChanged.connect(lambda v: setattr(self.score_view, 'tempo', v))
        self.tempo_spin.setToolTip("Project tempo in BPM")
        
        self.quant_combo = QComboBox()
        self.quant_combo.addItems(["1/1", "1/2", "1/4", "1/8", "1/16"])
        self.quant_combo.setCurrentText("1/2")
        self.quant_combo.currentTextChanged.connect(self.change_quantize)
        self.quant_combo.setToolTip("Grid snap value")
        
        self.vol_slider = QSlider(Qt.Horizontal); self.vol_slider.setRange(0, 100); self.vol_slider.setValue(80)
        self.vol_slider.setFixedWidth(100)
        self.vol_slider.valueChanged.connect(lambda v: self.audio_engine.set_master_volume(v / 100.0))
        
        self.auto_track_combo = QComboBox()
        for staff in self.score_view.staves: self.auto_track_combo.addItem(staff["name"])
        self.auto_track_combo.currentIndexChanged.connect(lambda i: setattr(self.score_view, 'auto_view_staff', i))
        
        self.auto_cc_combo = QComboBox()
        self.auto_cc_combo.addItems(["CC1 Mod", "CC7 Vol", "CC11 Expr", "CC74 Bright"])
        self.auto_cc_combo.currentIndexChanged.connect(lambda i: setattr(self.score_view, 'auto_view_cc', [1, 7, 11, 74][i]))
        
        self.key_combo = QComboBox()
        self.key_combo.addItems(NOTE_NAMES)
        self.key_combo.currentTextChanged.connect(lambda t: setattr(self.score_view, 'current_key', t))
        
        self.scale_combo = QComboBox()
        self.scale_combo.addItems(list(SCALES.keys()))
        self.scale_combo.setCurrentText("Minor")
        self.scale_combo.currentTextChanged.connect(lambda t: setattr(self.score_view, 'current_scale', t))
        
        l.addWidget(self.play_btn); l.addWidget(self.stop_btn); l.addWidget(self.loop_btn)
        l.addWidget(QLabel("Tempo:")); l.addWidget(self.tempo_spin)
        l.addWidget(QLabel("Quant:")); l.addWidget(self.quant_combo)
        l.addWidget(QLabel("Vol:")); l.addWidget(self.vol_slider)
        l.addWidget(QLabel("| Auto:")); l.addWidget(self.auto_track_combo); l.addWidget(self.auto_cc_combo)
        l.addStretch()
        l.addWidget(QLabel("Key:")); l.addWidget(self.key_combo)
        l.addWidget(QLabel("Scale:")); l.addWidget(self.scale_combo)
        return f

    def setup_menu(self):
        mb = self.menuBar()
        m_file = mb.addMenu("File")
        m_file.addAction(QAction("Load SoundFont...", self, triggered=self.load_soundfont))
        m_file.addAction(QAction("Import MIDI...", self, triggered=self.import_midi))
        m_file.addSeparator()
        m_file.addAction(QAction("Save Project...", self, triggered=self.save_project))
        m_file.addAction(QAction("Load Project...", self, triggered=self.load_project))
        m_file.addSeparator()
        m_file.addAction(QAction("Export MIDI...", self, triggered=self.export_midi))
        m_file.addAction(QAction("Render to WAV...", self, triggered=self.render_wav))
        m_file.addAction(QAction("Export MusicXML (Sheet Music)...", self, triggered=self.export_musicxml))
        m_file.addSeparator()
        m_file.addAction(QAction("Load Video for Sync...", self, triggered=self.load_video))
        
        m_edit = mb.addMenu("Edit")
        m_edit.addAction(self.undo_stack.createUndoAction(self, "Undo"))
        m_edit.addAction(self.undo_stack.createRedoAction(self, "Redo"))
        
        m_view = mb.addMenu("View")
        m_view.addAction(self.patcher_dock.toggleViewAction())
        m_view.addAction(self.mixer_dock.toggleViewAction())
        m_view.addAction(self.console_dock.toggleViewAction())
        m_view.addAction(self.console_script.toggleViewAction())
        m_view.addAction(self.video_dock.toggleViewAction())

    def setup_shortcuts(self):
        QShortcut(QKeySequence(Qt.Key_Space), self, activated=self.toggle_play)
        QShortcut(QKeySequence("Ctrl+C"), self, activated=self.copy_notes)
        QShortcut(QKeySequence("Ctrl+V"), self, activated=self.paste_notes)
        QShortcut(QKeySequence("Ctrl+D"), self, activated=self.duplicate_notes)

    def set_tool(self, tool_id, cursor):
        self.score_view.current_tool = tool_id
        self.score_view.setCursor(cursor)

    def change_quantize(self, text):
        mapping = {"1/1": 4.0, "1/2": 2.0, "1/4": 1.0, "1/8": 0.5, "1/16": 0.25}
        self.score_view.snap_value = mapping.get(text, 0.5)

    def keyPressEvent(self, e: QKeyEvent):
        if isinstance(self.focusWidget(), QLineEdit): return
            
        key_map = {
            Qt.Key_A: 0, Qt.Key_W: 1, Qt.Key_S: 2, Qt.Key_E: 3, Qt.Key_D: 4,
            Qt.Key_F: 5, Qt.Key_T: 6, Qt.Key_G: 7, Qt.Key_Y: 8, Qt.Key_H: 9,
            Qt.Key_U: 10, Qt.Key_J: 11, Qt.Key_K: 12, Qt.Key_O: 13, Qt.Key_L: 14
        }
        
        if e.key() == Qt.Key_Z: self.live_octave = max(0, self.live_octave - 1); return
        if e.key() == Qt.Key_X: self.live_octave = min(6, self.live_octave + 1); return
        
        if e.isAutoRepeat(): return
        
        if e.key() in key_map:
            staff_id = self.score_view.hovered_note.staff_id if self.score_view.hovered_note else 0
            ch = self.score_view.staves[staff_id]["ch"]
            pitch = self.live_octave * 12 + key_map[e.key()]
            self.audio_engine.note_on(pitch, 100, ch)
            self.auditioned_notes[e.key()] = (pitch, ch)
        else:
            super().keyPressEvent(e)

    def keyReleaseEvent(self, e: QKeyEvent):
        if e.isAutoRepeat(): return
        if e.key() in self.auditioned_notes:
            pitch, ch = self.auditioned_notes.pop(e.key())
            self.audio_engine.note_off(pitch, ch)

    def update_inspector(self):
        notes = list(self.score_view.selected_notes)
        if not notes and self.score_view.hovered_note:
            notes = [self.score_view.hovered_note]
        self.inspector.set_notes(notes)
        
        m = int(self.score_view.playhead_beat / 4) + 1
        b = int(self.score_view.playhead_beat % 4) + 1
        if self.video_player.source() != QUrl():
            smpte = self.beats_to_smpte(self.playhead_beat)
            self.statusBar().showMessage(f"Measure: {m} | Beat: {b} | SMPTE: {smpte}")
        else:
            self.statusBar().showMessage(f"Measure: {m} | Beat: {b} | Octave: {self.live_octave}")

    # --- Features ---
    def copy_notes(self):
        if self.score_view.selected_notes:
            self.clipboard = copy.deepcopy(list(self.score_view.selected_notes))

    def paste_notes(self):
        if hasattr(self, 'clipboard') and self.clipboard:
            min_beat = min(n.start_beat for n in self.clipboard)
            offset = self.score_view.playhead_beat - min_beat
            for n in self.clipboard:
                new_n = copy.deepcopy(n)
                new_n.start_beat += offset
                self.score_view.notes_data.append(new_n)
            self.score_view.commit_state("Paste Notes")
            self.score_view.update()

    def duplicate_notes(self):
        if self.score_view.selected_notes:
            new_sel = set()
            for n in list(self.score_view.selected_notes):
                new_n = copy.deepcopy(n)
                new_n.start_beat += n.duration_beats
                self.score_view.notes_data.append(new_n)
                new_sel.add(new_n)
            self.score_view.selected_notes = new_sel
            self.score_view.commit_state("Duplicate Notes")
            self.score_view.update()

    def clear_score(self):
        self.score_view.notes_data.clear()
        self.score_view.automation.clear()
        self.score_view.commit_state("Clear Score")
        self.statusBar().showMessage("Score Cleared.", 3000)

    def load_soundfont(self):
        path, _ = QFileDialog.getOpenFileName(self, "Load SoundFont", "", "SoundFont Files (*.sf2 *.sf3)")
        if path:
            if self.audio_engine.load_soundfont(path):
                QMessageBox.information(self, "SoundFont", "Loaded successfully!")
            else:
                QMessageBox.warning(self, "SoundFont", "Failed to load.")

    def toggle_loop(self, checked: bool):
        self.score_view.loop_enabled = checked
        self.score_view.update()

    def humanize(self):
        for n in self.score_view.notes_data:
            n.delay_ms = random.randint(0, 30)
            n.velocity = max(10, min(127, n.velocity + random.randint(-10, 10)))
        self.score_view.commit_state("Humanize")
        self.statusBar().showMessage("Humanized notes.", 3000)

    def auto_divisi(self):
        sel = list(self.score_view.selected_notes)
        if not sel:
            QMessageBox.warning(self, "Auto-Divisi", "Please select a chord (notes) to distribute.")
            return
        by_beat = {}
        for n in sel:
            b = round(n.start_beat * 4) / 4.0
            by_beat.setdefault(b, []).append(n)
        for beat, group in by_beat.items():
            group.sort(key=lambda x: x.pitch, reverse=True)
            for i, n in enumerate(group):
                if i < 5:
                    n.staff_id = i
                    if i == 4 and n.pitch > 55: n.pitch -= 12
                    elif i == 3 and n.pitch > 67: n.pitch -= 12
                    elif i == 2 and n.pitch > 74: n.pitch -= 12
                else:
                    n.staff_id = 0 
        self.score_view.commit_state("Smart Auto-Divisi")
        self.score_view.update()
        self.statusBar().showMessage(f"Distributed {len(sel)} notes across staves.", 3000)

    def generate_ostinato(self):
        scale = [60, 62, 63, 65, 67, 68, 70]
        start_beat = max([n.start_beat + n.duration_beats for n in self.score_view.notes_data if n.staff_id == 0], default=0)
        for beat in [b * 0.5 for b in range(32)]:
            pitch = random.choice(scale)
            self.score_view.notes_data.append(Note(pitch, start_beat + beat, 0.5, 90, 1, 0, 0))
        self.score_view.commit_state("Generate Ostinato")

    def transform_notes(self, mode: str):
        sel = list(self.score_view.selected_notes)
        if len(sel) < 2:
            QMessageBox.warning(self, "Transform", "Select at least 2 notes to transform.")
            return
        if mode == "invert":
            root_pitch = sel[0].pitch
            for n in sel:
                n.pitch = max(0, min(127, root_pitch - (n.pitch - root_pitch)))
        elif mode == "retrograde":
            beats = sorted([n.start_beat for n in sel])
            reversed_beats = sorted([n.start_beat for n in sel], reverse=True)
            for i, n in enumerate(sel):
                n.start_beat = reversed_beats[i]
        self.score_view.commit_state(f"Transform: {mode}")
        self.score_view.update()

    def auto_harmonize(self):
        sel = list(self.score_view.selected_notes)
        if not sel:
            QMessageBox.warning(self, "Harmonize", "Select melody notes to harmonize.")
            return
        generated = 0
        for n in sel:
            active_chord = None
            for cs in self.score_view.chord_symbols:
                if cs.beat <= n.start_beat < cs.beat + cs.duration_beats:
                    active_chord = cs
                    break
            if not active_chord: continue
            root_pc = NOTE_NAMES.index(active_chord.root)
            intervals = CHORD_LIB.get(active_chord.quality, [0, 4, 7])
            cello_pitch = 36 + (root_pc % 12)
            self.score_view.notes_data.append(Note(cello_pitch, n.start_beat, n.duration_beats, 80, 1, 0, 3, dynamic=n.dynamic))
            fifth_pc = (root_pc + 7) % 12
            viola_pitch = 48 + (fifth_pc % 12)
            self.score_view.notes_data.append(Note(viola_pitch, n.start_beat, n.duration_beats, 80, 1, 0, 2, dynamic=n.dynamic))
            generated += 2
        self.score_view.commit_state("Auto-Harmonize")
        self.score_view.update()
        self.statusBar().showMessage(f"Generated {generated} harmony notes.", 3000)

    def add_hairpin(self, is_crescendo: bool):
        sel = list(self.score_view.selected_notes)
        if not sel:
            QMessageBox.warning(self, "Hairpin", "Select notes on a single staff to apply a hairpin.")
            return
        staff_id = sel[0].staff_id
        min_beat = min(n.start_beat for n in sel)
        max_beat = max(n.start_beat + n.duration_beats for n in sel)
        start_val = 40 if is_crescendo else 110
        end_val = 110 if is_crescendo else 40
        self.score_view.automation = [p for p in self.score_view.automation if not (p.staff_id == staff_id and p.cc_type == 11 and min_beat <= p.beat <= max_beat)]
        self.score_view.automation.append(AutomationPoint(min_beat, 11, start_val, staff_id))
        self.score_view.automation.append(AutomationPoint(max_beat, 11, end_val, staff_id))
        self.score_view.automation.sort(key=lambda p: p.beat)
        self.auto_track_combo.setCurrentIndex(staff_id)
        self.auto_cc_combo.setCurrentIndex(2)
        self.score_view.update()
        self.statusBar().showMessage("Hairpin automation generated.", 3000)

    def handle_midi_input(self, event, data=None):
        message, delta_time = event
        status, data1, data2 = message[0], message[1], message[2]
        cmd = status & 0xF0
        if cmd == 0x90 and data2 > 0:
            self.audio_engine.note_on(data1, data2, 0)
            if not self.is_playing:
                n = Note(data1, self.score_view.snap_beat(self.score_view.playhead_beat), 0.5, data2, 1, 0, 0)
                self.score_view.notes_data.append(n)
                self.score_view.playhead_beat += 0.5
                self.score_view.update()
        elif cmd == 0x80 or (cmd == 0x90 and data2 == 0):
            self.audio_engine.note_off(data1, 0)
        elif cmd == 0xB0:
            if data1 == 1: self.audio_engine.set_dynamics(0, data2)

    def beats_to_smpte(self, beat: float, fps: int = 24) -> str:
        tempo = self.score_view.get_tempo_at_beat(beat)
        seconds = (beat / tempo) * 60.0
        frames = int(seconds * fps)
        h = frames // (3600 * fps); frames %= (3600 * fps)
        m = frames // (60 * fps); frames %= (60 * fps)
        s = frames // fps; f = frames % fps
        return f"{h:02d}:{m:02d}:{s:02d}:{f:02d}"

    def load_video(self):
        path, _ = QFileDialog.getOpenFileName(self, "Load Video", "", "Video Files (*.mp4 *.avi *.mov *.mkv)")
        if path:
            self.video_player.setSource(QUrl.fromLocalFile(path))
            self.video_dock.show()
            self.video_player.play()
            self.video_player.pause()
            self.statusBar().showMessage("Video loaded. Press Play to sync.", 3000)

    def save_project(self):
        path, _ = QFileDialog.getSaveFileName(self, "Save Project", "", "Cadenza Project (*.cadz)")
        if not path: return
        data = {
            "version": PROJECT_VERSION,
            "tempo": self.score_view.tempo,
            "notes": [n.to_dict() for n in self.score_view.notes_data],
            "chords": [asdict(c) for c in self.score_view.chord_symbols],
            "automation": [asdict(a) for a in self.score_view.automation],
            "tempo_track": [asdict(t) for t in self.score_view.tempo_track],
            "markers": [asdict(m) for m in self.score_view.markers]
        }
        with open(path, 'w') as f:
            json.dump(data, f, indent=4)
        self.statusBar().showMessage("Project saved.", 3000)

    def load_project(self):
        path, _ = QFileDialog.getOpenFileName(self, "Load Project", "", "Cadenza Project (*.cadz)")
        if not path: return
        with open(path, 'r') as f:
            data = json.load(f)
        if data.get("version") != PROJECT_VERSION:
            QMessageBox.warning(self, "Project", f"Version mismatch: file={data.get('version')}, app={PROJECT_VERSION}")
        self.score_view.tempo = data.get("tempo", 90)
        self.tempo_spin.setValue(self.score_view.tempo)
        self.score_view.notes_data = [Note.from_dict(n) for n in data.get("notes", [])]
        self.score_view.chord_symbols = [ChordSymbol(**c) for c in data.get("chords", [])]
        self.score_view.automation = [AutomationPoint(**a) for a in data.get("automation", [])]
        self.score_view.tempo_track = [TempoPoint(**t) for t in data.get("tempo_track", [TempoPoint(0, 90)])]
        self.score_view.markers = [Marker(**m) for m in data.get("markers", [])]
        self.undo_stack.clean_data = copy.deepcopy(self.score_view.notes_data)
        self.score_view.update()
        self.statusBar().showMessage("Project loaded.", 3000)

    def import_midi(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import MIDI", "", "MIDI Files (*.mid)")
        if not path: return
        with open(path, "rb") as f:
            data = f.read()
        notes = []
        idx = 0
        while idx < len(data):
            if data[idx:idx+4] == b'MTrk':
                track_len = struct.unpack(">I", data[idx+4:idx+8])[0]
                track_data = data[idx+8:idx+8+track_len]
                tick = 0; t_idx = 0; active_notes = {}
                while t_idx < len(track_data):
                    delta = 0
                    while True:
                        byte = track_data[t_idx]; t_idx += 1
                        delta = (delta << 7) | (byte & 0x7F)
                        if not (byte & 0x80): break
                    tick += delta
                    event = track_data[t_idx]
                    if event == 0xFF:
                        t_idx += 1; meta_type = track_data[t_idx]; t_idx += 1
                        vlq = 0
                        while True:
                            byte = track_data[t_idx]; t_idx += 1
                            vlq = (vlq << 7) | (byte & 0x7F)
                            if not (byte & 0x80): break
                        t_idx += vlq
                    else:
                        cmd = event & 0xF0; ch = event & 0x0F
                        if cmd in [0x90, 0x80]:
                            note = track_data[t_idx]; vel = track_data[t_idx+1]; t_idx += 2
                            if cmd == 0x90 and vel > 0: active_notes[note] = tick
                            else:
                                if note in active_notes:
                                    start_tick = active_notes.pop(note)
                                    dur = tick - start_tick
                                    beat = start_tick / 480; dur_beats = dur / 480
                                    if note >= 74: staff_id = 0
                                    elif note >= 67: staff_id = 1
                                    elif note >= 60: staff_id = 2
                                    elif note >= 48: staff_id = 3
                                    else: staff_id = 4
                                    notes.append(Note(note, beat, dur_beats, vel, 1, 0, staff_id))
                        elif cmd in [0xB0, 0xC0, 0xE0]: t_idx += 2
                idx += 8 + track_len
            else: idx += 1
        self.score_view.notes_data = notes
        self.undo_stack.clean_data = copy.deepcopy(notes)
        self.score_view.update()
        self.statusBar().showMessage(f"Imported {len(notes)} notes.", 3000)

    def export_midi(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export MIDI", "", "MIDI Files (*.mid)")
        if not path: return
        
        def write_var_len(value):
            buffer = value & 0x7F; output = []
            while value >> 7:
                value >>= 7; output.append(buffer | 0x80); buffer = value & 0x7F
            output.append(buffer)
            return bytes(output)

        with open(path, "wb") as f:
            num_tracks = 6
            f.write(b'MThd' + struct.pack(">IHHH", 6, 1, num_tracks, 480))
            micros_per_quarter = int(60_000_000 / self.score_view.tempo)
            track0_data = b'\x00\xFF\x51\x03' + micros_per_quarter.to_bytes(3, 'big')
            track0_data += b'\x00\xFF\x2F\x00'
            f.write(b'MTrk' + struct.pack(">I", len(track0_data)) + track0_data)
            
            for staff_id in range(5):
                events = []
                for n in self.score_view.notes_data:
                    if n.staff_id == staff_id:
                        ch = self.score_view.staves[n.staff_id]["ch"]
                        start_tick = int(n.start_beat * 480)
                        end_tick = int((n.start_beat + n.duration_beats) * 480)
                        events.append((start_tick, 0x90 | ch, n.pitch, n.velocity))
                        events.append((end_tick, 0x80 | ch, n.pitch, 0))
                events.sort(key=lambda x: (x[0], x[1]))
                track_data = b''
                name_str = self.score_view.staves[staff_id]["name"].encode('ascii')
                track_data += b'\x00\xFF\x03' + write_var_len(len(name_str)) + name_str
                last_tick = 0
                for ev in events:
                    delta = ev[0] - last_tick; last_tick = ev[0]
                    track_data += write_var_len(delta) + bytes([ev[1], ev[2], ev[3]])
                track_data += b'\x00\xFF\x2F\x00'
                f.write(b'MTrk' + struct.pack(">I", len(track_data)) + track_data)
        QMessageBox.information(self, "MIDI Export", "Type-1 MIDI file exported successfully.")

    def export_musicxml(self):
        path, _ = QFileDialog.getSaveFileName(self, "Export MusicXML", "", "MusicXML Files (*.xml)")
        if not path: return
        xml = ['<?xml version="1.0" encoding="UTF-8"?>', '<score-partwise version="3.0">', '<part-list>']
        for i, staff in enumerate(self.score_view.staves):
            xml.append(f'<score-part id="P{i}"><part-name>{staff["name"]}</part-name></score-part>')
        xml.append('</part-list>')
        for i, staff in enumerate(self.score_view.staves):
            xml.append(f'<part id="P{i}">')
            staff_notes = [n for n in self.score_view.notes_data if n.staff_id == i]
            staff_notes.sort(key=lambda n: n.start_beat)
            current_beat = 0.0; measure_num = 1
            def pitch_to_xml(p):
                pc = p % 12; octave = p // 12 - 1
                step = NOTE_NAMES[pc][0]
                alter = NOTE_NAMES[pc][1] if len(NOTE_NAMES[pc]) > 1 else None
                return step, alter, octave
            while current_beat < max([n.start_beat + n.duration_beats for n in staff_notes], default=4):
                xml.append(f'<measure number="{measure_num}">')
                if measure_num == 1:
                    clef = staff["clef"]
                    clef_xml = {"treble": "G", "alto": "C", "bass": "F"}.get(clef, "G")
                    xml.append(f'<attributes><divisions>4</divisions><clef><sign>{clef_xml}</sign></clef></attributes>')
                measure_notes = [n for n in staff_notes if current_beat <= n.start_beat < current_beat + 4.0]
                for n in measure_notes:
                    step, alter, octave = pitch_to_xml(n.pitch)
                    dur = int(n.duration_beats * 4)
                    xml.append('<note>')
                    if alter:
                        xml.append(f'<pitch><step>{step}</step><alter>{1 if alter=="#" else 0}</alter><octave>{octave}</octave></pitch>')
                    else:
                        xml.append(f'<pitch><step>{step}</step><octave>{octave}</octave></pitch>')
                    xml.append(f'<duration>{dur}</duration>')
                    xml.append(f'<type>{"whole" if dur>=16 else "half" if dur>=8 else "quarter" if dur>=4 else "eighth" if dur>=2 else "16th"}</type>')
                    xml.append('</note>')
                if not measure_notes:
                    xml.append('<note><rest/><duration>16</duration><type>whole</type></note>')
                xml.append('</measure>')
                current_beat += 4.0; measure_num += 1
            xml.append('</part>')
        xml.append('</score-partwise>')
        with open(path, 'w') as f:
            f.write("\n".join(xml))
        QMessageBox.information(self, "MusicXML", "Sheet music exported successfully!")

    def render_wav(self):
        if not self.audio_engine.sf_path:
            QMessageBox.warning(self, "Render", "Please load a SoundFont first.")
            return
        reply = QMessageBox.question(self, "Render Mode", "Render Individual Stems?\n(No = Full Mix)", 
                                     QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
        stems_mode = (reply == QMessageBox.Yes)
        path, _ = QFileDialog.getSaveFileName(self, "Render to WAV", "", "WAV Files (*.wav)")
        if not path: return
        
        self.statusBar().showMessage("Rendering offline...")
        self.render_thread = RenderThread(self.audio_engine.sf_path, self.score_view.notes_data, 
                                          self.score_view.tempo, self.score_view.staves, path, stems_mode)
        self.render_thread.progress.connect(lambda p: self.statusBar().showMessage(f"Rendering... {p}%"))
        self.render_thread.failed.connect(lambda msg: QMessageBox.critical(self, "Render Failed", msg))
        self.render_thread.start()

    # --- Playback ---
    def toggle_play(self):
        if self.is_playing:
            self.playback_timer.stop()
            self.midi_clock_timer.stop()
            self.audio_engine.send_midi_clock_stop()
            self.audio_engine.all_notes_off()
            self.currently_playing_notes.clear()
            self.is_playing = False
            self.play_btn.setText("▶ Play")
            if self.video_player.source() != QUrl(): self.video_player.pause()
        else:
            self.playback_timer.start(16)
            self.is_playing = True
            self.play_btn.setText("❚❚ Pause")
            self.last_time = time.time()
            self.audio_engine.send_midi_clock_start()
            self.midi_clock_timer.start(int(60000.0 / self.score_view.tempo / 24.0))
            
            for n in self.score_view.notes_data:
                if n.staff_id in self.score_view.ghost_staves: continue
                start_beat = n.start_beat
                end_beat = start_beat + n.duration_beats
                if start_beat < self.playhead_beat < end_beat:
                    ch = self.score_view.staves[n.staff_id]["ch"]
                    key = (id(n), n.pitch, ch)
                    current_art = self.audio_engine.current_articulations.get(ch, "legato")
                    if n.articulation != current_art:
                        ks_note = EXPRESSION_MAP.get(n.articulation, 0)
                        self.audio_engine.send_keyswitch(ch, ks_note)
                        self.audio_engine.current_articulations[ch] = n.articulation
                    if n.dynamic in DYN_TO_CC:
                        self.audio_engine.set_dynamics(ch, DYN_TO_CC[n.dynamic])
                    self.audio_engine.note_on(n.pitch, n.velocity, ch)
                    self.currently_playing_notes.add(key)

            if self.video_player.source() != QUrl():
                self.video_player.setPosition(int((self.playhead_beat / self.score_view.get_tempo_at_beat(self.playhead_beat)) * 60000))
                self.video_player.play()

    def stop_play(self):
        self.playback_timer.stop()
        self.midi_clock_timer.stop()
        self.audio_engine.send_midi_clock_stop()
        self.is_playing = False
        self.playhead_beat = 0.0
        self.audio_engine.all_notes_off()
        self.currently_playing_notes.clear()
        self.play_btn.setText("▶ Play")
        self.score_view.playhead_beat = 0.0
        self.score_view.update()
        self.update_inspector()
        if self.video_player.source() != QUrl(): self.video_player.stop()

    def _pulse_midi_clock(self):
        current_bpm = self.score_view.get_tempo_at_beat(self.playhead_beat)
        interval_ms = int(60000.0 / current_bpm / 24.0)
        if self.midi_clock_timer.interval() != interval_ms:
            self.midi_clock_timer.setInterval(interval_ms)
        self.audio_engine._send_clock_pulse()

    def update_playback(self):
        now = time.time()
        dt = now - self.last_time
        self.last_time = now
        
        current_bpm = self.score_view.get_tempo_at_beat(self.playhead_beat)
        self.playhead_beat += (current_bpm / 60.0) * dt
        total_beats = max([n.start_beat + n.duration_beats for n in self.score_view.notes_data], default=16)
        
        if self.score_view.loop_enabled and self.playhead_beat > self.score_view.loop_end:
            self.playhead_beat = self.score_view.loop_start
            self.audio_engine.all_notes_off()
            self.currently_playing_notes.clear()
        elif not self.score_view.loop_enabled and self.playhead_beat > total_beats + 2:
            self.stop_play()
            return

        expected_playing: Set[Tuple[int, int, int]] = set()
        
        for n in self.score_view.notes_data:
            if n.staff_id in self.score_view.ghost_staves: continue
            start_beat = n.start_beat + (n.delay_ms / 1000.0) * (current_bpm / 60.0)
            end_beat = start_beat + n.duration_beats
            
            if start_beat <= self.playhead_beat < end_beat:
                ch = self.score_view.staves[n.staff_id]["ch"]
                key = (id(n), n.pitch, ch)
                expected_playing.add(key)
                
                if key not in self.currently_playing_notes:
                    current_art = self.audio_engine.current_articulations.get(ch, "legato")
                    if n.articulation != current_art:
                        ks_note = EXPRESSION_MAP.get(n.articulation, 0)
                        self.audio_engine.send_keyswitch(ch, ks_note)
                        self.audio_engine.current_articulations[ch] = n.articulation
                    if n.dynamic in DYN_TO_CC:
                        self.audio_engine.set_dynamics(ch, DYN_TO_CC[n.dynamic])
                    self.audio_engine.note_on(n.pitch, n.velocity, ch)
                    self.currently_playing_notes.add(key)
        
        for item in self.currently_playing_notes - expected_playing:
            _, pitch, ch = item
            self.audio_engine.note_off(pitch, ch)
                
        self.currently_playing_notes = expected_playing
        
        for ch_idx in range(5):
            pts = [p for p in self.score_view.automation if p.staff_id == ch_idx]
            pts.sort(key=lambda p: p.beat)
            for i in range(len(pts) - 1):
                p1, p2 = pts[i], pts[i+1]
                if p1.beat <= self.playhead_beat < p2.beat:
                    t = (self.playhead_beat - p1.beat) / (p2.beat - p1.beat)
                    val = int(p1.value + (p2.value - p1.value) * t)
                    self.audio_engine.fs.cc(ch_idx, p1.cc_type, val)
                    break
                
        self.score_view.playhead_beat = self.playhead_beat
        self.score_view.update()
        self.update_inspector()

# ==========================================
# 13. Entry Point
# ==========================================
if __name__ == "__main__":
    app = QApplication(sys.argv)
    app.setStyleSheet("""
        QMainWindow { background-color: #1e1e1e; }
        QDockWidget { color: #ddd; border: 1px solid #333; }
        QDockWidget::title { background-color: #2b2b2b; padding: 6px; }
        QLabel { color: #ccc; }
        QPushButton { background-color: #333; color: #ddd; padding: 6px; border: 1px solid #555; border-radius: 4px; }
        QPushButton:hover { background-color: #444; }
        QPushButton:checked { background-color: #555; border: 1px solid #aaa; }
        QLineEdit { background-color: #111; color: #ddd; padding: 6px; border: 1px solid #555; border-radius: 4px; }
        QScrollArea { border: none; background: #1e1e1e; }
        QCheckBox { color: #ddd; }
        QSpinBox, QDoubleSpinBox, QComboBox { background-color: #111; color: #ddd; padding: 4px; border: 1px solid #555; border-radius: 4px; }
        QSlider::groove:horizontal { border: 1px solid #555; height: 4px; background: #111; }
        QSlider::handle:horizontal { background: #4a9eff; width: 10px; margin: -4px 0; border-radius: 2px; }
        QSlider::groove:vertical { border: 1px solid #555; width: 4px; background: #111; }
        QSlider::handle:vertical { background: #4a9eff; height: 10px; margin: 0 -4px; border-radius: 2px; }
        QToolBar { background-color: #252525; border: none; spacing: 2px; }
        QToolButton { background-color: #333; color: #ddd; padding: 6px; border: 1px solid #555; border-radius: 4px; }
        QToolButton:checked { background-color: #555; border: 1px solid #aaa; }
    """)
    win = CadenzaMainWindow()
    win.show()
    sys.exit(app.exec())