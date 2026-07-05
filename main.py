"""
PrimeRobo AI Interface
=======================
A polished, self-contained desktop chat assistant built with Tkinter.

Highlights
----------
* An extensible "Skills" system (clock, calendar, dictionary, Wikipedia,
  calculator, help, learn-as-you-go knowledge base) — adding a new
  capability means adding one small class.
* Three switchable visual themes plus a custom-background color picker.
* Multiple, persisted chat sessions with search, rename, clear, and delete.
* A calculator that understands words, percentages, powers, roots and mod.
* Multi-line message composer (Enter to send, Shift+Enter for a new line).
* Smart auto-scroll that never yanks you away from history you're reading,
  plus a "jump to latest" pill when you're scrolled up.
* Consecutive messages from the same sender are visually grouped.
* An animated "thinking…" indicator while a network lookup is in flight
  (which itself always runs on a background thread, so the UI never
  freezes).
* Right-click any message to copy or delete it; right-click any chat to
  rename, clear, or delete it.
* Window size and chosen theme are remembered between launches.

Only the Python standard library is required.
"""

from __future__ import annotations

import json
import math
import re
import threading
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass, field, replace
from datetime import datetime
from difflib import get_close_matches
from pathlib import Path
from tkinter import colorchooser, simpledialog, ttk
from typing import Callable, Optional

# --------------------------------------------------------------------------- #
# Paths
# --------------------------------------------------------------------------- #

BASE_DIR = Path(__file__).resolve().parent
KNOWLEDGE_BASE_PATH = BASE_DIR / "knowledge_base.json"
CHATS_PATH = BASE_DIR / "chats.json"
SETTINGS_PATH = BASE_DIR / "settings.json"


# --------------------------------------------------------------------------- #
# Word-number parsing
# --------------------------------------------------------------------------- #

_UNITS = {
    "zero": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
    "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10, "eleven": 11,
    "twelve": 12, "thirteen": 13, "fourteen": 14, "fifteen": 15,
    "sixteen": 16, "seventeen": 17, "eighteen": 18, "nineteen": 19,
}
_TENS = {
    "twenty": 20, "thirty": 30, "forty": 40, "fifty": 50,
    "sixty": 60, "seventy": 70, "eighty": 80, "ninety": 90,
}
_SCALES = {"hundred": 100, "thousand": 1000, "million": 1_000_000}


def words_to_number(text: str) -> float:
    """Convert a plain number or an English number phrase to a float.

    Accepts digits ("42", "-3.5") as well as words ("two hundred and five",
    "negative four"). Raises ValueError if a token isn't recognized.
    """
    raw = text.lower().strip()

    # A bare (optionally signed) digit literal — check this first, before
    # any hyphen normalization, since "-5" is a sign here but a hyphen
    # inside a word like "twenty-five" is just a separator.
    if re.match(r"^-?\d+(?:\.\d+)?$", raw):
        return float(raw)

    negative = False
    cleaned = raw
    for prefix in ("negative ", "minus "):
        if cleaned.startswith(prefix):
            negative = True
            cleaned = cleaned[len(prefix):]
            break

    cleaned = cleaned.replace("-", " ").replace(" and ", " ").strip()
    if not cleaned:
        raise ValueError("No number given.")

    current = 0
    total = 0
    for word in cleaned.split():
        if word in _UNITS:
            current += _UNITS[word]
        elif word in _TENS:
            current += _TENS[word]
        elif word in _SCALES:
            scale = _SCALES[word]
            current = max(current, 1) * scale
            if scale >= 1000:
                total += current
                current = 0
        else:
            raise ValueError(f"Unrecognized number word: '{word}'")

    result = float(total + current)
    return -result if negative else result


# --------------------------------------------------------------------------- #
# Calculator
# --------------------------------------------------------------------------- #

def _divide(a: float, b: float) -> float:
    if b == 0:
        raise ValueError("Cannot divide by zero.")
    return a / b


def _modulo(a: float, b: float) -> float:
    if b == 0:
        raise ValueError("Cannot divide by zero.")
    return a % b


def _percent_of(a: float, b: float) -> float:
    return (a / 100) * b


# Order matters: more specific / multi-word phrases are listed first so they
# win over shorter phrases that might otherwise also appear in the text.
_OPERATORS: list[tuple[str, str]] = [
    ("divided by", "/"), ("divide", "/"),
    ("to the power of", "**"),
    ("modulo", "%"), ("mod", "%"),
    ("plus", "+"), ("add", "+"),
    ("minus", "-"), ("subtract", "-"),
    ("times", "*"), ("multiply", "*"),
    ("+", "+"), ("-", "-"), ("*", "*"), ("/", "/"), ("^", "**"), ("%", "%"),
]
_OPS: dict[str, Callable[[float, float], float]] = {
    "+": lambda a, b: a + b,
    "-": lambda a, b: a - b,
    "*": lambda a, b: a * b,
    "/": _divide,
    "**": lambda a, b: a ** b,
    "%": _modulo,
}

_SQRT_RE = re.compile(r"^(?:square root of|sqrt(?: of)?)\s+(.+)$")
_SQUARE_RE = re.compile(r"^(.+?)\s+squared$")
_CUBE_RE = re.compile(r"^(.+?)\s+cubed$")
_PERCENT_RE = re.compile(r"^(.+?)\s*(?:percent|%)\s*of\s+(.+)$")


def _find_operator(lowered: str) -> Optional[tuple[str, re.Match]]:
    """Find the first (by priority list, not position) operator keyword or
    symbol present in `lowered`, matched on a word boundary for alphabetic
    keywords so we don't trigger on substrings like 'address' or 'modem'.
    """
    for keyword, symbol in _OPERATORS:
        if keyword.replace(" ", "").isalpha():
            pattern = r"\b" + re.escape(keyword) + r"\b"
        else:
            pattern = re.escape(keyword)
        match = re.search(pattern, lowered)
        if match:
            return symbol, match
    return None


def _safe_number(text: str) -> Optional[float]:
    """words_to_number that returns None instead of raising, for use where
    a parse failure should mean 'this wasn't really math' rather than a
    user-facing error.
    """
    try:
        return words_to_number(text)
    except ValueError:
        return None


def parse_and_calculate(text: str) -> Optional[float]:
    """Try to interpret `text` as a math expression and evaluate it.

    Returns None if the text doesn't look like math at all (so the caller
    can fall through to something else, like the knowledge base). Raises
    ValueError only for expressions that clearly *are* math but are
    mathematically invalid (division by zero, a negative square root) —
    those deserve a visible error rather than silent fallback.
    """
    lowered = text.lower().strip()

    m = _SQRT_RE.match(lowered)
    if m:
        value = _safe_number(m.group(1).strip())
        if value is None:
            return None
        if value < 0:
            raise ValueError("Can't take the square root of a negative number.")
        return math.sqrt(value)

    m = _SQUARE_RE.match(lowered)
    if m:
        value = _safe_number(m.group(1).strip())
        return None if value is None else value ** 2

    m = _CUBE_RE.match(lowered)
    if m:
        value = _safe_number(m.group(1).strip())
        return None if value is None else value ** 3

    m = _PERCENT_RE.match(lowered)
    if m:
        a = _safe_number(m.group(1).strip())
        b = _safe_number(m.group(2).strip())
        return None if a is None or b is None else _percent_of(a, b)

    found = _find_operator(lowered)
    if found:
        symbol, match = found
        left = lowered[:match.start()].strip()
        right = lowered[match.end():].strip()
        if not left or not right:
            return None
        num1 = _safe_number(left)
        num2 = _safe_number(right)
        if num1 is None or num2 is None:
            return None
        return _OPS[symbol](num1, num2)  # may raise ValueError (e.g. /0)

    return None


# --------------------------------------------------------------------------- #
# Knowledge base (learned Q&A)
# --------------------------------------------------------------------------- #

class KnowledgeBase:
    """A tiny persisted question/answer store with fuzzy matching."""

    def __init__(self, path: Path = KNOWLEDGE_BASE_PATH):
        self.path = path
        self.data: dict = self._load()

    def _load(self) -> dict:
        if not self.path.exists() or self.path.stat().st_size == 0:
            return {"questions": []}
        try:
            return json.loads(self.path.read_text())
        except json.JSONDecodeError:
            return {"questions": []}

    def save(self) -> None:
        self.path.write_text(json.dumps(self.data, indent=4))

    def find_answer(self, question: str) -> Optional[str]:
        known = [q["question"] for q in self.data["questions"]]
        match = get_close_matches(question, known, n=1, cutoff=0.75)
        if not match:
            return None
        for entry in self.data["questions"]:
            if entry["question"].lower() == match[0].lower():
                return entry["answer"]
        return None

    def teach(self, question: str, answer: str) -> None:
        self.data["questions"].append({"question": question, "answer": answer})
        self.save()


# --------------------------------------------------------------------------- #
# Network lookups (run off the UI thread)
# --------------------------------------------------------------------------- #

class NetworkService:
    """Runs the dictionary/Wikipedia HTTP lookups on a background thread and
    delivers the result back on the Tk main thread via `root.after`.
    """

    def __init__(self, root: tk.Tk):
        self._root = root

    def run(self, worker: Callable[[], Optional[str]], on_done: Callable[[Optional[str]], None]) -> None:
        def _target():
            try:
                result = worker()
            except Exception:
                result = None
            self._root.after(0, on_done, result)

        threading.Thread(target=_target, daemon=True).start()

    @staticmethod
    def fetch_definition(word: str) -> Optional[str]:
        encoded = urllib.parse.quote(word.strip().lower())
        url = f"https://api.dictionaryapi.dev/api/v2/entries/en/{encoded}"
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
            with urllib.request.urlopen(req, timeout=5) as response:
                data = json.loads(response.read().decode())
        except (urllib.error.URLError, TimeoutError, ValueError, OSError):
            return None

        if not data or not isinstance(data, list):
            return None

        meanings = data[0].get("meanings", [])
        lines = [f"Definitions for '{word.strip()}':"]
        for item in meanings[:2]:
            part_of_speech = item.get("partOfSpeech", "general")
            lines.append(f"\n[{part_of_speech.upper()}]")
            for definition in item.get("definitions", [])[:2]:
                lines.append(f"  • {definition.get('definition')}")
        return "\n".join(lines).strip()

    @staticmethod
    def fetch_wikipedia_summary(query: str) -> Optional[str]:
        formatted = query.strip().title().replace(" ", "_")
        encoded = urllib.parse.quote(formatted)
        url = f"https://en.wikipedia.org/api/rest_v1/page/summary/{encoded}"
        try:
            req = urllib.request.Request(
                url, headers={"User-Agent": "Mozilla/5.0 (PrimeRoboInterface/1.0)"}
            )
            with urllib.request.urlopen(req, timeout=5) as response:
                data = json.loads(response.read().decode())
        except (urllib.error.URLError, TimeoutError, ValueError, OSError):
            return None

        extract = data.get("extract")
        if not extract:
            return None
        if "may refer to:" in extract or "refer to:" in extract:
            return (
                f"'{data.get('title')}' could mean several things — try being "
                f"more specific (e.g. 'Sonic the Hedgehog' instead of 'Sonic')."
            )
        return f"{data.get('title')}:\n{extract}"


# --------------------------------------------------------------------------- #
# Chat data model + persistence
# --------------------------------------------------------------------------- #

@dataclass
class Message:
    sender: str
    text: str
    is_user: bool
    timestamp: str = field(default_factory=lambda: datetime.now().strftime("%H:%M"))


class ChatStore:
    """Holds every chat session in memory and mirrors it to disk."""

    def __init__(self, path: Path = CHATS_PATH):
        self.path = path
        self.chats: dict[str, list[Message]] = {}
        self.order: list[str] = []
        if not self._load():
            self._seed_default()

    def _seed_default(self) -> None:
        self.chats = {
            "Chat Alpha": [Message("PrimeRobo", "System initialized. Active channel: Alpha.", False)]
        }
        self.order = ["Chat Alpha"]

    def _load(self) -> bool:
        if not self.path.exists():
            return False
        try:
            raw = json.loads(self.path.read_text())
        except (json.JSONDecodeError, OSError):
            return False
        chats = raw.get("chats", {})
        if not chats:
            return False
        self.chats = {name: [Message(**m) for m in msgs] for name, msgs in chats.items()}
        self.order = [n for n in raw.get("order", list(self.chats.keys())) if n in self.chats]
        if not self.order:
            self.order = list(self.chats.keys())
        return True

    def save(self) -> None:
        payload = {
            "order": self.order,
            "chats": {name: [asdict(m) for m in msgs] for name, msgs in self.chats.items()},
        }
        self.path.write_text(json.dumps(payload, indent=2))

    def add_chat(self, name: str, greeting: str) -> None:
        self.chats[name] = [Message("PrimeRobo", greeting, False)]
        self.order.append(name)
        self.save()

    def delete_chat(self, name: str) -> None:
        if len(self.chats) <= 1:
            return
        del self.chats[name]
        self.order.remove(name)
        self.save()

    def rename_chat(self, old: str, new: str) -> None:
        self.chats[new] = self.chats.pop(old)
        self.order[self.order.index(old)] = new
        self.save()

    def clear_chat(self, name: str) -> None:
        self.chats[name] = [Message("PrimeRobo", "Chat cleared. Fresh start.", False)]
        self.save()

    def append(self, name: str, message: Message) -> None:
        self.chats[name].append(message)
        self.save()

    def delete_message(self, name: str, index: int) -> bool:
        """Delete one message. Returns False (and does nothing) if the
        index is invalid or it's the last remaining message in the chat —
        a chat is never left completely empty.
        """
        messages = self.chats.get(name)
        if not messages or not (0 <= index < len(messages)) or len(messages) <= 1:
            return False
        del messages[index]
        self.save()
        return True


# --------------------------------------------------------------------------- #
# Settings persistence (window geometry + theme choice)
# --------------------------------------------------------------------------- #

class Settings:
    def __init__(self, path: Path = SETTINGS_PATH):
        self.path = path
        data = self._load()
        self.geometry: str = data.get("geometry", "960x640")
        self.palette_name: str = data.get("palette", "Midnight")
        self.custom_bg: Optional[str] = data.get("custom_bg")

    def _load(self) -> dict:
        if not self.path.exists():
            return {}
        try:
            return json.loads(self.path.read_text())
        except (json.JSONDecodeError, OSError):
            return {}

    def save(self) -> None:
        payload = {
            "geometry": self.geometry,
            "palette": self.palette_name,
            "custom_bg": self.custom_bg,
        }
        try:
            self.path.write_text(json.dumps(payload, indent=2))
        except OSError:
            pass


# --------------------------------------------------------------------------- #
# Visual theme
# --------------------------------------------------------------------------- #

@dataclass(frozen=True)
class Palette:
    name: str
    bg: str
    sidebar: str
    sidebar_item: str
    accent: str
    accent_hover: str
    bubble_user: str
    bubble_bot: str
    text_on_accent: str
    text_primary: str
    text_bot: str
    text_muted: str
    danger: str
    danger_hover: str
    border: str


PALETTES: dict[str, Palette] = {
    "Midnight": Palette(
        name="Midnight", bg="#11141a", sidebar="#1a1f29", sidebar_item="#252c3b",
        accent="#ff9f43", accent_hover="#ffb56b", bubble_user="#3457d5", bubble_bot="#232b3a",
        text_on_accent="#161616", text_primary="#ffffff", text_bot="#e7ecf5",
        text_muted="#8b96ab", danger="#ff5d5d", danger_hover="#ff7d7d", border="#3d495e",
    ),
    "Aurora": Palette(
        name="Aurora", bg="#0f1720", sidebar="#141d2b", sidebar_item="#1d2a3d",
        accent="#5eead4", accent_hover="#8ff3e3", bubble_user="#7c5cff", bubble_bot="#1c2739",
        text_on_accent="#0a1620", text_primary="#f2f5f9", text_bot="#dbe6f5",
        text_muted="#7c8ba3", danger="#ff6b81", danger_hover="#ff8a9c", border="#2c3c52",
    ),
    "Daylight": Palette(
        name="Daylight", bg="#f4f6fb", sidebar="#e9edf7", sidebar_item="#dde3f2",
        accent="#3457d5", accent_hover="#5674e0", bubble_user="#3457d5", bubble_bot="#ffffff",
        text_on_accent="#ffffff", text_primary="#1b2233", text_bot="#1b2233",
        text_muted="#6b7385", danger="#e5484d", danger_hover="#f16d71", border="#c7cee2",
    ),
}

FONT_FAMILY = "Segoe UI"
SIZE_TITLE = 13
SIZE_BODY = 11
SIZE_SMALL = 9
SIZE_TINY = 8


def font(size: int = SIZE_BODY, weight: str = "normal") -> tuple:
    return (FONT_FAMILY, size, weight)


def rounded_rect(canvas: tk.Canvas, x1, y1, x2, y2, radius, **kwargs):
    """Draw a rounded rectangle on `canvas` using a smoothed polygon."""
    points = [
        x1 + radius, y1,
        x2 - radius, y1,
        x2, y1,
        x2, y1 + radius,
        x2, y2 - radius,
        x2, y2,
        x2 - radius, y2,
        x1 + radius, y2,
        x1, y2,
        x1, y2 - radius,
        x1, y1 + radius,
        x1, y1,
    ]
    return canvas.create_polygon(points, smooth=True, **kwargs)


# --------------------------------------------------------------------------- #
# Skills — each capability is a small, self-contained, easy-to-extend class
# --------------------------------------------------------------------------- #

class Skill:
    """Base class for a single conversational capability.

    `try_handle` should return True if it fully handled the message
    (including by showing a helpful error), or False to let the next
    skill in line have a turn.
    """

    description: str = ""

    def try_handle(self, app: "PrimeRoboApp", text: str, lowered: str) -> bool:
        raise NotImplementedError


class HelpSkill(Skill):
    description = "Ask 'help' any time to see everything I can do."
    _QUERIES = {"help", "/help", "commands", "what can you do", "what can you do?"}

    def try_handle(self, app, text, lowered):
        if lowered not in self._QUERIES:
            return False
        lines = ["Here's what I can help with:", ""]
        for skill in app.skills:
            if isinstance(skill, HelpSkill) or not skill.description:
                continue
            lines.append(f"• {skill.description}")
        lines.append("• Type 'quit' to exit.")
        app.reply("\n".join(lines))
        return True


class ClockSkill(Skill):
    description = "Ask 'what time is it' for the current time."
    _QUERIES = {"what is the time", "what is time", "time", "current time", "what time is it"}

    def try_handle(self, app, text, lowered):
        if lowered not in self._QUERIES:
            return False
        app.reply(f"Current time: {datetime.now().strftime('%I:%M %p')}")
        return True


class CalendarSkill(Skill):
    description = "Ask 'what is the date' or 'today' for today's date."
    _QUERIES = {
        "what is the date", "what is date", "date", "today's date",
        "what is today", "today", "day",
    }

    def try_handle(self, app, text, lowered):
        if lowered not in self._QUERIES:
            return False
        app.reply(f"Today is {datetime.now().strftime('%A, %B %d, %Y')}")
        return True


class DefineSkill(Skill):
    description = "Ask 'define <word>' for an online dictionary lookup."
    _PATTERN = re.compile(r"^(?:define|meaning of|what is the meaning of)\s+([a-zA-Z0-9\s\-_]+)$")

    def try_handle(self, app, text, lowered):
        m = self._PATTERN.match(lowered)
        if not m:
            return False
        app.lookup_definition(m.group(1).strip())
        return True


class WikipediaSkill(Skill):
    description = "Ask 'who is <name>' or 'tell me about <topic>' for a Wikipedia summary."
    _PATTERN = re.compile(r"^(?:who is|who was|tell me about|search up)\s+([a-zA-Z0-9\s\-_]+)$")

    def try_handle(self, app, text, lowered):
        m = self._PATTERN.match(lowered)
        if not m:
            return False
        app.lookup_wikipedia(m.group(1).strip())
        return True


class MathSkill(Skill):
    description = "Ask things like '12 plus 8', '20 percent of 50', 'sqrt of 81', or '5 squared'."

    def try_handle(self, app, text, lowered):
        try:
            result = parse_and_calculate(text)
        except ValueError as exc:
            app.reply(f"⚠️ {exc}")
            return True
        if result is None:
            return False
        app.reply(f"Result: {result:g}")
        return True


class KnowledgeBaseSkill(Skill):
    """Terminal fallback: always handles the message, one way or another."""

    description = "Ask me anything else — I'll try to remember it, or ask you to teach me."

    def try_handle(self, app, text, lowered):
        answer = app.knowledge_base.find_answer(text)
        if answer:
            app.reply(answer)
        else:
            app.reply(
                "I don't know that one yet. Reply with the answer to teach me, "
                "or type 'skip' to move on."
            )
            app.teaching_mode = True
            app.pending_question = text
        return True


# --------------------------------------------------------------------------- #
# Main application
# --------------------------------------------------------------------------- #

class PrimeRoboApp:
    BUBBLE_PAD_X = 16
    BUBBLE_PAD_Y = 12
    MIN_WRAP = 220
    MAX_INPUT_LINES = 5

    def __init__(self, root: tk.Tk):
        self.root = root
        self.settings = Settings()

        base_palette = PALETTES.get(self.settings.palette_name, PALETTES["Midnight"])
        self.palette = replace(base_palette, bg=self.settings.custom_bg) if self.settings.custom_bg else base_palette

        self.root.title("PrimeRobo AI Interface")
        self.root.geometry(self.settings.geometry)
        self.root.minsize(560, 480)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        self.knowledge_base = KnowledgeBase()
        self.chat_store = ChatStore()
        self.network = NetworkService(root)
        self.skills: list[Skill] = [
            HelpSkill(), ClockSkill(), CalendarSkill(), DefineSkill(),
            WikipediaSkill(), MathSkill(), KnowledgeBaseSkill(),
        ]

        self.current_chat = self.chat_store.order[0]
        self.chat_counter = len(self.chat_store.order)
        self.teaching_mode = False
        self.pending_question = ""
        self._resize_job: Optional[str] = None
        self._near_bottom = True
        self._thinking_job: Optional[str] = None
        self._thinking_base_text = ""
        self._thinking_chat = ""
        self._thinking_frame = 0
        self._flash_active = False
        self._search_placeholder = "🔍  Search chats…"

        self._build_layout()
        self._apply_theme()
        self.entry.focus_set()

    # ----------------------------- layout ------------------------------- #

    def _build_layout(self) -> None:
        self.root.grid_columnconfigure(1, weight=1)
        self.root.grid_rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_main_panel()

        self.context_menu = tk.Menu(self.root, tearoff=0, bd=0)
        self.message_menu = tk.Menu(self.root, tearoff=0, bd=0)
        self.root.bind("<Control-n>", lambda e: self.create_chat())

    def _build_sidebar(self) -> None:
        self.sidebar = tk.Frame(self.root, width=240)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)

        self.sidebar_header = tk.Frame(self.sidebar)
        self.sidebar_header.pack(fill=tk.X, pady=(15, 8), padx=12)
        self.sidebar_title_label = tk.Label(self.sidebar_header, text="🤖 CHAT LOGS", font=font(10, "bold"))
        self.sidebar_title_label.pack(side=tk.LEFT)
        self.new_chat_btn = self._pill_button(self.sidebar_header, "+ NEW", self.create_chat, side=tk.RIGHT)

        self.search_frame = tk.Frame(self.sidebar)
        self.search_frame.pack(fill=tk.X, padx=12, pady=(0, 8))
        self.search_entry = tk.Entry(self.search_frame, font=font(SIZE_SMALL), bd=0,
                                      highlightthickness=1)
        self.search_entry.pack(fill=tk.X, ipady=4)
        self.search_entry.bind("<FocusIn>", self._on_search_focus_in)
        self.search_entry.bind("<FocusOut>", self._on_search_focus_out)
        self.search_entry.bind("<KeyRelease>", lambda e: self._refresh_sidebar())

        self.chat_list = tk.Frame(self.sidebar)
        self.chat_list.pack(fill=tk.BOTH, expand=True)

        self.sidebar_footer = tk.Frame(self.sidebar, pady=10, padx=12)
        self.sidebar_footer.pack(fill=tk.X, side=tk.BOTTOM)
        self.appearance_btn = self._pill_button(
            self.sidebar_footer, "🎨  Appearance", self.open_appearance_panel, fill=tk.X,
        )

    def _build_main_panel(self) -> None:
        self.main = tk.Frame(self.root)
        self.main.grid(row=0, column=1, sticky="nsew", padx=12, pady=12)
        self.main.grid_columnconfigure(0, weight=1)
        self.main.grid_rowconfigure(1, weight=1)

        self.header_bar = tk.Frame(self.main)
        self.header_bar.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        self.title_label = tk.Label(self.header_bar, text=self.current_chat, font=font(SIZE_TITLE, "bold"), anchor="w")
        self.title_label.pack(side=tk.LEFT)
        self.status_label = tk.Label(self.header_bar, text="", font=font(SIZE_SMALL))
        self.status_label.pack(side=tk.RIGHT)

        self.body = tk.Frame(self.main)
        self.body.grid(row=1, column=0, sticky="nsew")
        self.body.grid_columnconfigure(0, weight=1)
        self.body.grid_rowconfigure(0, weight=1)

        self.canvas = tk.Canvas(self.body, bd=0, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(self.body, orient="vertical", command=self._on_scrollbar_move)
        self.scroll_frame = tk.Frame(self.canvas)

        self.scroll_frame.bind(
            "<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )
        self.canvas_window = self.canvas.create_window((0, 0), window=self.scroll_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.scrollbar.grid(row=0, column=1, sticky="ns")

        # Bind wheel-scrolling to the canvas and its (empty) background
        # frame once here; each bubble row binds itself too when created,
        # so scrolling works anywhere over the chat log without walking
        # the whole widget tree on every render.
        for w in (self.canvas, self.scroll_frame):
            w.bind("<MouseWheel>", self._on_mousewheel)
            w.bind("<Button-4>", lambda e: self._scroll_units(-2))
            w.bind("<Button-5>", lambda e: self._scroll_units(2))

        self.jump_pill = tk.Button(
            self.body, text="↓  Jump to latest", font=font(SIZE_SMALL, "bold"),
            relief=tk.FLAT, bd=0, padx=12, pady=6, cursor="hand2", command=self._jump_to_bottom,
        )

        input_bar = tk.Frame(self.main)
        self.input_bar = input_bar
        input_bar.grid(row=2, column=0, sticky="ew", pady=(10, 0))
        input_bar.grid_columnconfigure(0, weight=1)

        self.entry = tk.Text(input_bar, font=font(SIZE_BODY), bd=0, height=1, wrap="word",
                              highlightthickness=1)
        self.entry.grid(row=0, column=0, sticky="ew", padx=(0, 8), ipady=6)
        self.entry.bind("<Return>", self._on_return)
        self.entry.bind("<KeyRelease>", self._autogrow_input)
        self.entry.bind("<Escape>", self._cancel_teaching)

        self.send_button = tk.Button(
            input_bar, text="TRANSMIT", font=font(SIZE_SMALL, "bold"),
            command=self.handle_send, relief=tk.FLAT, bd=0, padx=16, pady=8, cursor="hand2",
        )
        self.send_button.grid(row=0, column=1, sticky="e")

    def _pill_button(self, parent, text, command, side=None, fill=None) -> tk.Button:
        btn = tk.Button(
            parent, text=text, font=font(SIZE_SMALL, "bold"), relief=tk.FLAT, bd=0,
            padx=10, pady=6, cursor="hand2", command=command,
        )
        if fill:
            btn.pack(fill=fill)
        else:
            btn.pack(side=side or tk.LEFT)
        return btn

    # ------------------------------ theming ------------------------------- #

    def _apply_theme(self) -> None:
        p = self.palette
        self.root.configure(bg=p.bg)

        self.sidebar.configure(bg=p.sidebar)
        self.sidebar_header.configure(bg=p.sidebar)
        self.sidebar_title_label.configure(bg=p.sidebar, fg=p.accent)
        self.new_chat_btn.configure(bg=p.sidebar_item, fg=p.accent,
                                     activebackground=p.accent, activeforeground=p.text_on_accent)

        self.search_frame.configure(bg=p.sidebar)
        self.search_entry.configure(
            bg=p.sidebar_item, insertbackground=p.text_primary,
            highlightbackground=p.border, highlightcolor=p.accent,
        )
        self._restyle_search_entry()

        self.chat_list.configure(bg=p.sidebar)
        self.sidebar_footer.configure(bg=p.sidebar)
        self.appearance_btn.configure(bg=p.sidebar_item, fg=p.accent,
                                       activebackground=p.accent, activeforeground=p.text_on_accent)

        self.main.configure(bg=p.bg)
        self.header_bar.configure(bg=p.bg)
        self.title_label.configure(bg=p.bg, fg=p.text_primary)
        self.status_label.configure(bg=p.bg, fg=p.text_muted)

        self.body.configure(bg=p.bg)
        self.canvas.configure(bg=p.bg)
        self.scroll_frame.configure(bg=p.bg)
        self.jump_pill.configure(bg=p.accent, fg=p.text_on_accent, activebackground=p.accent_hover)

        self.input_bar.configure(bg=p.bg)
        self.entry.configure(
            bg=p.sidebar_item, fg=p.text_primary, insertbackground=p.text_primary,
            highlightbackground=p.border, highlightcolor=p.accent,
        )
        self.send_button.configure(bg=p.accent, fg=p.text_on_accent, activebackground=p.accent_hover)

        self.context_menu.configure(bg=p.sidebar_item, fg=p.text_primary,
                                     activebackground=p.accent, activeforeground=p.text_on_accent)
        self.message_menu.configure(bg=p.sidebar_item, fg=p.text_primary,
                                     activebackground=p.accent, activeforeground=p.text_on_accent)

        self._refresh_sidebar()
        self._render_chat()

    def _restyle_search_entry(self) -> None:
        p = self.palette
        current = self.search_entry.get()
        if current == self._search_placeholder or not current.strip():
            self.search_entry.configure(fg=p.text_muted)
        else:
            self.search_entry.configure(fg=p.text_primary)

    # --------------------------- sidebar / search -------------------------- #

    def _on_search_focus_in(self, _e=None) -> None:
        if self.search_entry.get() == self._search_placeholder:
            self.search_entry.delete(0, tk.END)
        self.search_entry.configure(fg=self.palette.text_primary)

    def _on_search_focus_out(self, _e=None) -> None:
        if not self.search_entry.get().strip():
            self._set_search_placeholder()

    def _set_search_placeholder(self) -> None:
        self.search_entry.delete(0, tk.END)
        self.search_entry.insert(0, self._search_placeholder)
        self.search_entry.configure(fg=self.palette.text_muted)

    def _current_search_query(self) -> str:
        text = self.search_entry.get().strip()
        if text == self._search_placeholder:
            return ""
        return text.lower()

    def _refresh_sidebar(self) -> None:
        p = self.palette
        for widget in self.chat_list.winfo_children():
            widget.destroy()

        # Ensure the placeholder is showing when appropriate (e.g. right
        # after a theme switch tears down and rebuilds nothing here, but
        # focus state may have changed).
        if not self.search_entry.get().strip() and self.search_entry.focus_get() != self.search_entry:
            self._set_search_placeholder()

        query = self._current_search_query()
        names = [n for n in self.chat_store.order if query in n.lower()] if query else list(self.chat_store.order)

        if not names:
            tk.Label(self.chat_list, text="No matching chats", fg=p.text_muted, bg=p.sidebar,
                      font=font(SIZE_SMALL)).pack(pady=20)
            return

        for name in names:
            row = tk.Frame(self.chat_list, bg=p.sidebar)
            row.pack(fill=tk.X, padx=10, pady=3)

            active = name == self.current_chat
            btn = tk.Button(
                row, text=name, font=font(SIZE_SMALL, "bold" if active else "normal"),
                bg=p.accent if active else p.sidebar_item,
                fg=p.text_on_accent if active else p.text_primary,
                relief=tk.FLAT, bd=0, pady=8, anchor="w", padx=10, cursor="hand2",
                command=lambda n=name: self.switch_chat(n),
            )
            btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
            btn.bind("<Double-Button-1>", lambda e, n=name: self.rename_chat(n))
            btn.bind("<Button-3>", lambda e, n=name: self._show_chat_menu(e, n))
            btn.bind("<Button-2>", lambda e, n=name: self._show_chat_menu(e, n))

            delete_btn = tk.Button(
                row, text="🗑", font=font(SIZE_SMALL), bg=p.danger, fg="white",
                activebackground=p.danger_hover, relief=tk.FLAT, bd=0, padx=8, pady=8,
                cursor="hand2", command=lambda n=name: self.delete_chat(n),
            )
            delete_btn.pack(side=tk.RIGHT, padx=(4, 0))

    def _show_chat_menu(self, event, chat_name: str) -> None:
        menu = self.context_menu
        menu.delete(0, tk.END)
        menu.add_command(label="📝 Rename", command=lambda: self.rename_chat(chat_name))
        menu.add_command(label="🧹 Clear messages", command=lambda: self.clear_chat(chat_name))
        menu.add_separator()
        menu.add_command(label="🗑 Delete", command=lambda: self.delete_chat(chat_name))
        menu.tk_popup(event.x_root, event.y_root)

    def create_chat(self) -> None:
        self.chat_counter += 1
        name = f"Chat Session {self.chat_counter}"
        self.chat_store.add_chat(name, f"New session online: {name}.")
        self.current_chat = name
        self._near_bottom = True
        self._refresh_sidebar()
        self._render_chat()
        self.entry.focus_set()

    def delete_chat(self, name: str) -> None:
        if len(self.chat_store.chats) <= 1:
            self._flash_status("At least one chat must remain.")
            return
        self.chat_store.delete_chat(name)
        if self.current_chat == name:
            self.current_chat = self.chat_store.order[0]
            self._near_bottom = True
        self._refresh_sidebar()
        self._render_chat()

    def rename_chat(self, name: str) -> None:
        new_name = simpledialog.askstring(
            "Rename Chat", f"New name for '{name}':", parent=self.root, initialvalue=name
        )
        if not new_name or not new_name.strip():
            return
        new_name = new_name.strip()
        if new_name == name or new_name in self.chat_store.chats:
            return
        self.chat_store.rename_chat(name, new_name)
        if self.current_chat == name:
            self.current_chat = new_name
        self._refresh_sidebar()
        self._render_chat()

    def clear_chat(self, name: str) -> None:
        self.chat_store.clear_chat(name)
        if self.current_chat == name:
            self._near_bottom = True
            self._render_chat()

    def switch_chat(self, name: str) -> None:
        self.current_chat = name
        self._near_bottom = True
        self._refresh_sidebar()
        self._render_chat()
        self.entry.focus_set()

    # --------------------------- appearance panel -------------------------- #

    def open_appearance_panel(self) -> None:
        p = self.palette
        win = tk.Toplevel(self.root)
        win.title("Appearance")
        win.configure(bg=p.sidebar)
        win.resizable(False, False)
        win.transient(self.root)

        tk.Label(win, text="Choose a theme", bg=p.sidebar, fg=p.text_primary,
                 font=font(SIZE_BODY, "bold")).pack(padx=18, pady=(18, 8), anchor="w")

        for name, palette in PALETTES.items():
            row = tk.Frame(win, bg=p.sidebar)
            row.pack(fill=tk.X, padx=18, pady=4)

            swatch = tk.Canvas(row, width=22, height=22, bg=p.sidebar, highlightthickness=0)
            swatch.create_oval(2, 2, 20, 20, fill=palette.accent, outline=palette.bg)
            swatch.pack(side=tk.LEFT, padx=(0, 10))

            is_active = palette.name == self.palette.name
            btn = tk.Button(
                row, text=name + ("  ✓" if is_active else ""),
                font=font(SIZE_SMALL, "bold"),
                bg=p.accent if is_active else p.sidebar_item,
                fg=p.text_on_accent if is_active else p.text_primary,
                relief=tk.FLAT, bd=0, anchor="w", padx=10, pady=8, cursor="hand2",
                command=lambda pal=palette, w=win: self._select_palette(pal, w),
            )
            btn.pack(side=tk.LEFT, fill=tk.X, expand=True)

        tk.Frame(win, bg=p.border, height=1).pack(fill=tk.X, padx=18, pady=12)

        tk.Button(
            win, text="🎨  Custom Background Color…", font=font(SIZE_SMALL, "bold"),
            bg=p.sidebar_item, fg=p.accent, relief=tk.FLAT, bd=0,
            padx=10, pady=8, cursor="hand2",
            command=lambda w=win: self._pick_custom_bg(w),
        ).pack(fill=tk.X, padx=18, pady=(0, 18))

    def _select_palette(self, palette: Palette, win: Optional[tk.Toplevel] = None) -> None:
        self.palette = palette
        self.settings.palette_name = palette.name
        self.settings.custom_bg = None
        self.settings.save()
        self._apply_theme()
        if win is not None:
            win.destroy()

    def _pick_custom_bg(self, win: Optional[tk.Toplevel] = None) -> None:
        result = colorchooser.askcolor(title="Choose background color", initialcolor=self.palette.bg,
                                        parent=win or self.root)
        if not result or not result[1]:
            return
        self.palette = replace(self.palette, bg=result[1])
        self.settings.custom_bg = result[1]
        self.settings.save()
        self._apply_theme()
        if win is not None:
            win.destroy()

    # ---------------------------- chat display ---------------------------- #

    def _on_canvas_resize(self, event) -> None:
        self.canvas.itemconfig(self.canvas_window, width=event.width)
        if self._resize_job is not None:
            self.root.after_cancel(self._resize_job)
        self._resize_job = self.root.after(120, self._render_chat)

    def _on_mousewheel(self, event) -> None:
        delta = -1 if event.delta > 0 else 1
        self._scroll_units(delta * 2)

    def _scroll_units(self, units: int) -> None:
        self.canvas.yview_scroll(units, "units")
        self._update_near_bottom()

    def _on_scrollbar_move(self, *args) -> None:
        self.canvas.yview(*args)
        self._update_near_bottom()

    def _update_near_bottom(self) -> None:
        _, bottom = self.canvas.yview()
        self._near_bottom = bottom >= 0.98
        if self._near_bottom:
            self._hide_jump_pill()

    def _show_jump_pill(self) -> None:
        self.jump_pill.place(relx=0.5, rely=0.95, anchor="s")

    def _hide_jump_pill(self) -> None:
        self.jump_pill.place_forget()

    def _jump_to_bottom(self) -> None:
        self.canvas.yview_moveto(1.0)
        self._near_bottom = True
        self._hide_jump_pill()

    def _wrap_width(self) -> int:
        available = self.canvas.winfo_width() or 700
        return max(self.MIN_WRAP, int(available * 0.62))

    def _render_chat(self) -> None:
        """Renders the chat interface efficiently without causing layout lag or breaking headers."""
        messages = self.chat_store.chats.get(self.current_chat, [])
        existing_widgets = self.scroll_frame.winfo_children()
        num_existing = len(existing_widgets)

        # Helper logic to determine if a header should be shown (same as your original code)
        def should_show_header(idx: int) -> bool:
            if idx == 0:
                return True
            return messages[idx].sender != messages[idx - 1].sender

        # Case A: If the screen was cleared, switched, or emptied, perform a fresh draw
        if num_existing == 0 or num_existing > len(messages):
            for w in existing_widgets:
                w.destroy()
            for idx, msg in enumerate(messages):
                show_header = should_show_header(idx)
                self._render_bubble(msg, idx, show_header)
        
        # Case B: Smart incremental update (Only draw the absolute newest messages)
        else:
            for idx in range(num_existing, len(messages)):
                show_header = should_show_header(idx)
                self._render_bubble(messages[idx], idx, show_header)

        # Gently update scroll window placement metrics smoothly
        self.root.update_idletasks()
        
        # Only bind the wheel to newly appended items if required by your script setup
        if hasattr(self, '_bind_wheel'):
            self._bind_wheel(self.scroll_frame)
            
        # Smoothly snap down to the newest message block
        self.canvas.yview_moveto(1.0)

    def _render_bubble(self, message: Message, index: int, show_header: bool) -> None:
        p = self.palette
        is_user = message.is_user
        bubble_color = p.bubble_user if is_user else p.bubble_bot
        text_color = "#ffffff" if is_user else p.text_bot
        avatar = "🧑" if is_user else "🤖"
        align_side = tk.RIGHT if is_user else tk.LEFT
        anchor_pos = "ne" if is_user else "nw"

        row = tk.Frame(self.scroll_frame, bg=p.bg)
        row.pack(fill=tk.X, expand=True, pady=(6 if show_header else 1, 0))

        wrapper = tk.Frame(row, bg=p.bg)
        wrapper.pack(side=align_side, anchor=anchor_pos, padx=6)

        if show_header:
            header = tk.Frame(wrapper, bg=p.bg)
            header.pack(fill=tk.X, pady=(0, 3))
            tk.Label(
                header, text=f"{avatar} {message.sender}  ·  {message.timestamp}",
                fg=p.text_muted, bg=p.bg, font=font(SIZE_TINY, "bold"),
            ).pack(side=align_side)

        content = tk.Frame(wrapper, bg=p.bg)
        content.pack(fill=tk.X)

        bubble = self._make_bubble_canvas(content, message.text, bubble_color, text_color)
        bubble.pack(side=align_side, anchor=anchor_pos)

        copy_btn = tk.Button(
            content, text="📋", font=font(SIZE_TINY, "bold"), bg=p.sidebar_item,
            fg=p.text_muted, activebackground=p.accent, activeforeground=p.text_on_accent,
            relief=tk.FLAT, bd=0, padx=6, pady=4, cursor="hand2",
            command=lambda t=message.text: self._copy(t),
        )

        def show_copy(_e=None):
            if is_user:
                copy_btn.pack(side=tk.LEFT, padx=(0, 6), anchor="s")
            else:
                copy_btn.pack(side=tk.RIGHT, padx=(6, 0), anchor="s")

        def hide_copy(_e=None):
            copy_btn.pack_forget()

        def show_menu(event, msg=message, idx=index):
            self._show_message_menu(event, msg, idx)

        for widget in (wrapper, bubble):
            widget.bind("<Enter>", show_copy)
            widget.bind("<Leave>", hide_copy)
            widget.bind("<Button-3>", show_menu)
            widget.bind("<Button-2>", show_menu)

    def _make_bubble_canvas(self, parent, text, bg_color, fg_color) -> tk.Canvas:
        p = self.palette
        wrap = self._wrap_width()
        f = font(SIZE_BODY)

        probe = tk.Label(parent, text=text, font=f, wraplength=wrap, justify=tk.LEFT)
        probe.update_idletasks()
        text_w = probe.winfo_reqwidth()
        text_h = probe.winfo_reqheight()
        probe.destroy()

        width = text_w + 2 * self.BUBBLE_PAD_X
        height = text_h + 2 * self.BUBBLE_PAD_Y

        canvas = tk.Canvas(parent, width=width, height=height, bg=p.bg, bd=0, highlightthickness=0)
        radius = max(4, min(16, (width - 1) / 2, (height - 1) / 2))
        rounded_rect(canvas, 0, 0, width - 1, height - 1, radius=radius,
                     fill=bg_color, outline=p.border, width=1)
        canvas.create_text(
            self.BUBBLE_PAD_X, self.BUBBLE_PAD_Y, text=text, fill=fg_color, font=f,
            anchor="nw", width=wrap, justify=tk.LEFT,
        )
        return canvas

    def _show_message_menu(self, event, message: Message, index: int) -> None:
        menu = self.message_menu
        menu.delete(0, tk.END)
        menu.add_command(label="📋 Copy", command=lambda: self._copy(message.text))
        menu.add_command(label="🗑 Delete message", command=lambda: self._delete_message(index))
        menu.tk_popup(event.x_root, event.y_root)

    def _delete_message(self, index: int) -> None:
        if not self.chat_store.delete_message(self.current_chat, index):
            self._flash_status("Can't delete the last message in a chat.")
            return
        self._render_chat()

    def _copy(self, text: str) -> None:
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self._flash_status("Copied to clipboard ✓")

    def _flash_status(self, text: str, ms: int = 1800) -> None:
        self._flash_active = True
        self.status_label.configure(text=text)
        self.root.after(ms, self._end_flash)

    def _end_flash(self) -> None:
        self._flash_active = False
        self._update_status_count()

    def _update_status_count(self) -> None:
        if self._flash_active:
            return
        count = len(self.chat_store.chats[self.current_chat])
        self.status_label.configure(text=f"{count} message{'s' if count != 1 else ''}")

    # ------------------------------ messaging ------------------------------ #

    def _append(self, sender: str, text: str, is_user: bool) -> None:
        self.chat_store.append(self.current_chat, Message(sender, text, is_user))
        if is_user:
            self._near_bottom = True
        self._render_chat()

    def reply(self, text: str) -> None:
        """Public entry point Skills use to send a PrimeRobo response."""
        self._append("PrimeRobo", text, is_user=False)

    def _cancel_teaching(self, _event=None) -> None:
        if self.teaching_mode:
            self.teaching_mode = False
            self.pending_question = ""
            self.reply("Learning phase cancelled.")

    # ------------------------------ input widget ---------------------------- #

    def _get_input_text(self) -> str:
        return self.entry.get("1.0", "end-1c").strip()

    def _clear_input(self) -> None:
        self.entry.delete("1.0", "end")
        self.entry.configure(height=1)

    def _on_return(self, event):
        if event.state & 0x0001:  # Shift held -> allow a newline
            return None
        self.handle_send()
        return "break"

    def _autogrow_input(self, _event=None) -> None:
        try:
            counts = self.entry.count("1.0", "end", "displaylines")
            lines = counts[0] if counts else 1
        except tk.TclError:
            lines = 1
        new_height = max(1, min(lines, self.MAX_INPUT_LINES))
        if int(self.entry.cget("height")) != new_height:
            self.entry.configure(height=new_height)

    # ------------------------------ routing ------------------------------ #

    def handle_send(self) -> None:
        text = self._get_input_text()
        if not text:
            return
        self._clear_input()
        self._append("You", text, is_user=True)

        if text.lower().strip() == "quit":
            self._on_close()
            return

        if self.teaching_mode:
            self._handle_teaching_reply(text)
            return

        lowered = text.lower().strip()
        for skill in self.skills:
            if skill.try_handle(self, text, lowered):
                return

        # KnowledgeBaseSkill always returns True, so this is unreachable —
        # kept only as a defensive fallback.
        self.reply("Sorry, something went wrong processing that.")

    def _handle_teaching_reply(self, text: str) -> None:
        if text.lower() != "skip":
            self.knowledge_base.teach(self.pending_question, text)
            self.reply("Got it — I'll remember that.")
        else:
            self.reply("Okay, skipped.")
        self.teaching_mode = False
        self.pending_question = ""

    # --------------------------- network lookups --------------------------- #

    def lookup_definition(self, word: str) -> None:
        self._begin_network_call(f"Looking up '{word}'")

        def done(result: Optional[str]):
            final = result or f"No definition found online for '{word}'."
            self._finish_network_call(final)

        self.network.run(lambda: NetworkService.fetch_definition(word), done)

    def lookup_wikipedia(self, subject: str) -> None:
        self._begin_network_call(f"Searching for '{subject}'")

        def done(result: Optional[str]):
            final = result or f"No page found for '{subject}'."
            self._finish_network_call(final)

        self.network.run(lambda: NetworkService.fetch_wikipedia_summary(subject), done)

    def _begin_network_call(self, base_text: str) -> None:
        self.send_button.configure(state="disabled")
        self._append("PrimeRobo", base_text, is_user=False)
        self._thinking_base_text = base_text
        self._thinking_chat = self.current_chat
        self._thinking_frame = 0
        self._tick_thinking()

    def _tick_thinking(self) -> None:
        dots = "." * (self._thinking_frame % 3 + 1)
        self._set_pending_text(self._thinking_chat, f"{self._thinking_base_text}{dots}")
        self._thinking_frame += 1
        self._thinking_job = self.root.after(450, self._tick_thinking)

    def _set_pending_text(self, chat_name: str, text: str) -> None:
        messages = self.chat_store.chats.get(chat_name)
        if not messages:
            return
        last = messages[-1]
        messages[-1] = Message(last.sender, text, last.is_user, last.timestamp)
        if chat_name == self.current_chat:
            self._render_chat()

    def _finish_network_call(self, final_text: str) -> None:
        if self._thinking_job is not None:
            self.root.after_cancel(self._thinking_job)
            self._thinking_job = None
        self.send_button.configure(state="normal")

        chat_name = self._thinking_chat
        messages = self.chat_store.chats.get(chat_name)
        if messages:
            last = messages[-1]
            messages[-1] = Message("PrimeRobo", final_text, False, last.timestamp)
            self.chat_store.save()
        if chat_name == self.current_chat:
            self._render_chat()

    # ------------------------------ lifecycle ------------------------------ #

    def _on_close(self, *_args) -> None:
        try:
            self.settings.geometry = self.root.geometry()
            self.settings.save()
        except tk.TclError:
            pass
        self.root.destroy()

    def _bind_wheel(self, widget: tk.Widget) -> None:
        """Recursively binds the mouse wheel event to a widget and all its children."""
        widget.bind("<MouseWheel>", self._on_wheel)
        widget.bind("<Button-4>", self._on_wheel)  # Linux scroll up
        widget.bind("<Button-5>", self._on_wheel)  # Linux scroll down
        
        for child in widget.winfo_children():
            self._bind_wheel(child)

    def _on_wheel(self, event: tk.Event) -> None:
        """Handles mouse wheel scrolling safely across Windows, macOS, and Linux platforms."""
        # Windows / macOS
        if event.delta != 0:
            self.canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        # Linux Support
        elif event.num == 4:
            self.canvas.yview_scroll(-1, "units")
        elif event.num == 5:
            self.canvas.yview_scroll(1, "units")


def main() -> None:
    root = tk.Tk()
    PrimeRoboApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
