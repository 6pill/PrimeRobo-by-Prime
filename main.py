"""
PrimeRobo AI Interface
=======================
A polished, self-contained desktop chat assistant built with Tkinter.

Features
--------
* Multiple chat sessions (create / rename / delete / clear), persisted to disk.
* A small local "brain": clock & calendar answers, a word-problem calculator,
  an online dictionary lookup, an online Wikipedia lookup, and a
  learn-as-you-go knowledge base for anything else.
* Network calls run on background threads so the UI never freezes.
* A dark, rounded-bubble chat theme with a customizable background color.

Only the Python standard library is required.
"""

from __future__ import annotations

import json
import re
import threading
import tkinter as tk
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import asdict, dataclass, field
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

    Accepts digits ("42", "3.5") as well as words ("two hundred and five").
    Raises ValueError if a token isn't recognized.
    """
    cleaned = text.lower().replace("-", " ").replace(" and ", " ").strip()

    if re.match(r"^\d+(?:\.\d+)?$", cleaned):
        return float(cleaned)

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

    return float(total + current)


# --------------------------------------------------------------------------- #
# Calculator
# --------------------------------------------------------------------------- #

def _divide(a: float, b: float) -> float:
    if b == 0:
        raise ValueError("Cannot divide by zero.")
    return a / b


_OPERATORS: list[tuple[str, str]] = [
    ("divided by", "/"), ("divide", "/"), ("plus", "+"), ("add", "+"),
    ("minus", "-"), ("subtract", "-"), ("times", "*"), ("multiply", "*"),
    ("+", "+"), ("-", "-"), ("*", "*"), ("/", "/"),
]
_OPS: dict[str, Callable[[float, float], float]] = {
    "+": lambda a, b: a + b,
    "-": lambda a, b: a - b,
    "*": lambda a, b: a * b,
    "/": _divide,
}


def parse_and_calculate(text: str) -> Optional[float]:
    """Try to parse `text` as a two-operand word/number expression and
    evaluate it. Returns None if no operator keyword is present at all
    (meaning: this probably isn't a math question). Raises ValueError for
    a recognized-but-invalid expression (e.g. division by zero, garbage
    operands), so the caller can show a helpful error instead of silently
    ignoring it.
    """
    lowered = text.lower()
    for keyword, symbol in _OPERATORS:
        if keyword in lowered:
            left, right = lowered.split(keyword, 1)
            left, right = left.strip(), right.strip()
            if not left or not right:
                continue
            num1 = words_to_number(left)
            num2 = words_to_number(right)
            return _OPS[symbol](num1, num2)
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
    """Wraps the dictionary/Wikipedia HTTP lookups and runs them on a
    background thread, delivering the result back on the Tk main thread.
    """

    def __init__(self, root: tk.Tk):
        self._root = root

    def run(self, worker: Callable[[], str], on_done: Callable[[str], None]) -> None:
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
        except (urllib.error.URLError, TimeoutError, ValueError):
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
        except (urllib.error.URLError, TimeoutError, ValueError):
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
        self.chats = {
            name: [Message(**m) for m in messages] for name, messages in chats.items()
        }
        self.order = raw.get("order", list(self.chats.keys()))
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

    def replace_last(self, name: str, message: Message) -> None:
        self.chats[name][-1] = message
        self.save()


# --------------------------------------------------------------------------- #
# Visual theme
# --------------------------------------------------------------------------- #

class Theme:
    SIDEBAR = "#1a1f29"
    SIDEBAR_ITEM = "#252c3b"
    ACCENT = "#ff9f43"
    ACCENT_HOVER = "#ffb56b"
    BUBBLE_USER = "#3457d5"
    BUBBLE_BOT = "#232b3a"
    TEXT_ON_ACCENT = "#161616"
    TEXT_PRIMARY = "#ffffff"
    TEXT_BOT = "#e7ecf5"
    TEXT_MUTED = "#8b96ab"
    DANGER = "#ff5d5d"
    DANGER_HOVER = "#ff7d7d"
    SUCCESS = "#37d67a"
    BORDER = "#3d495e"

    FAMILY = "Segoe UI"
    SIZE_TITLE = 11
    SIZE_BODY = 11
    SIZE_SMALL = 9
    SIZE_TINY = 8

    @classmethod
    def font(cls, size=None, weight="normal") -> tuple:
        return (cls.FAMILY, size or cls.SIZE_BODY, weight)


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
# Main application
# --------------------------------------------------------------------------- #

class PrimeRoboApp:
    BUBBLE_PAD_X = 16
    BUBBLE_PAD_Y = 12
    MIN_WRAP = 220

    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("PrimeRobo AI Interface")
        self.root.geometry("900x620")
        self.root.minsize(560, 480)

        self.bg = "#11141a"
        self.root.configure(bg=self.bg)

        self.knowledge_base = KnowledgeBase()
        self.chat_store = ChatStore()
        self.network = NetworkService(root)

        self.current_chat = self.chat_store.order[0]
        self.chat_counter = len(self.chat_store.order)
        self.teaching_mode = False
        self.pending_question = ""
        self._resize_job: Optional[str] = None

        self._build_layout()
        self._refresh_sidebar()
        self._render_chat()
        self.entry.focus_set()

    # ----------------------------- layout ------------------------------- #

    def _build_layout(self) -> None:
        self.root.grid_columnconfigure(1, weight=1)
        self.root.grid_rowconfigure(0, weight=1)

        self._build_sidebar()
        self._build_main_panel()

        self.context_menu = tk.Menu(
            self.root, tearoff=0, bg=Theme.SIDEBAR_ITEM, fg=Theme.TEXT_PRIMARY,
            activebackground=Theme.ACCENT, activeforeground=Theme.TEXT_ON_ACCENT,
            bd=0,
        )

    def _build_sidebar(self) -> None:
        self.sidebar = tk.Frame(self.root, bg=Theme.SIDEBAR, width=240)
        self.sidebar.grid(row=0, column=0, sticky="nsew")
        self.sidebar.grid_propagate(False)

        header = tk.Frame(self.sidebar, bg=Theme.SIDEBAR)
        header.pack(fill=tk.X, pady=15, padx=12)
        tk.Label(
            header, text="🤖 CHAT LOGS", fg=Theme.ACCENT, bg=Theme.SIDEBAR,
            font=Theme.font(10, "bold"),
        ).pack(side=tk.LEFT)
        self._pill_button(
            header, "+ NEW", self.create_chat, side=tk.RIGHT,
        )

        self.chat_list = tk.Frame(self.sidebar, bg=Theme.SIDEBAR)
        self.chat_list.pack(fill=tk.BOTH, expand=True)

        footer = tk.Frame(self.sidebar, bg=Theme.SIDEBAR, pady=10, padx=12)
        footer.pack(fill=tk.X, side=tk.BOTTOM)
        self._pill_button(
            footer, "🎨  Custom Background", self.pick_background_color, fill=tk.X,
        )

    def _build_main_panel(self) -> None:
        self.main = tk.Frame(self.root, bg=self.bg)
        self.main.grid(row=0, column=1, sticky="nsew", padx=12, pady=12)
        self.main.grid_columnconfigure(0, weight=1)
        self.main.grid_rowconfigure(1, weight=1)

        self.header_bar = tk.Frame(self.main, bg=self.bg)
        self.header_bar.grid(row=0, column=0, sticky="ew", pady=(0, 8))
        self.title_label = tk.Label(
            self.header_bar, text=self.current_chat, fg=Theme.TEXT_PRIMARY, bg=self.bg,
            font=Theme.font(13, "bold"), anchor="w",
        )
        self.title_label.pack(side=tk.LEFT)
        self.status_label = tk.Label(
            self.header_bar, text="", fg=Theme.TEXT_MUTED, bg=self.bg, font=Theme.font(Theme.SIZE_SMALL),
        )
        self.status_label.pack(side=tk.RIGHT)

        body = tk.Frame(self.main, bg=self.bg)
        body.grid(row=1, column=0, sticky="nsew")
        body.grid_columnconfigure(0, weight=1)
        body.grid_rowconfigure(0, weight=1)

        self.canvas = tk.Canvas(body, bg=self.bg, bd=0, highlightthickness=0)
        self.scrollbar = ttk.Scrollbar(body, orient="vertical", command=self.canvas.yview)
        self.scroll_frame = tk.Frame(self.canvas, bg=self.bg)

        self.scroll_frame.bind(
            "<Configure>", lambda e: self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        )
        self.canvas_window = self.canvas.create_window((0, 0), window=self.scroll_frame, anchor="nw")
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.canvas.bind("<Configure>", self._on_canvas_resize)

        self.canvas.grid(row=0, column=0, sticky="nsew")
        self.scrollbar.grid(row=0, column=1, sticky="ns")

        self.canvas.bind_all("<MouseWheel>", self._on_mousewheel)   # Windows/macOS
        self.canvas.bind_all("<Button-4>", lambda e: self.canvas.yview_scroll(-2, "units"))  # Linux
        self.canvas.bind_all("<Button-5>", lambda e: self.canvas.yview_scroll(2, "units"))

        input_bar = tk.Frame(self.main, bg=self.bg)
        input_bar.grid(row=2, column=0, sticky="ew", pady=(10, 0))
        input_bar.grid_columnconfigure(0, weight=1)

        self.entry = tk.Entry(
            input_bar, font=Theme.font(Theme.SIZE_BODY), bg="#1e2530", fg=Theme.TEXT_PRIMARY,
            insertbackground="white", bd=0, highlightthickness=1,
            highlightbackground=Theme.BORDER, highlightcolor=Theme.ACCENT,
        )
        self.entry.grid(row=0, column=0, sticky="ew", ipady=9, padx=(0, 8))
        self.entry.bind("<Return>", self.handle_send)
        self.entry.bind("<Escape>", self._cancel_teaching)

        self.send_button = tk.Button(
            input_bar, text="TRANSMIT", font=Theme.font(Theme.SIZE_SMALL, "bold"),
            bg=Theme.ACCENT, fg=Theme.TEXT_ON_ACCENT, activebackground=Theme.ACCENT_HOVER,
            command=self.handle_send, relief=tk.FLAT, bd=0, padx=16, pady=8, cursor="hand2",
        )
        self.send_button.grid(row=0, column=1, sticky="e")

        self.root.bind("<Control-n>", lambda e: self.create_chat())

    def _pill_button(self, parent, text, command, side=None, fill=None):
        btn = tk.Button(
            parent, text=text, font=Theme.font(Theme.SIZE_SMALL, "bold"),
            bg=Theme.SIDEBAR_ITEM, fg=Theme.ACCENT, activebackground=Theme.ACCENT,
            activeforeground=Theme.TEXT_ON_ACCENT, relief=tk.FLAT, bd=0,
            padx=10, pady=6, cursor="hand2", command=command,
        )
        if fill:
            btn.pack(fill=fill)
        else:
            btn.pack(side=side or tk.LEFT)
        return btn

    # --------------------------- sidebar logic --------------------------- #

    def _refresh_sidebar(self) -> None:
        for widget in self.chat_list.winfo_children():
            widget.destroy()

        for name in self.chat_store.order:
            row = tk.Frame(self.chat_list, bg=Theme.SIDEBAR)
            row.pack(fill=tk.X, padx=10, pady=3)

            active = name == self.current_chat
            btn = tk.Button(
                row, text=name, font=Theme.font(Theme.SIZE_SMALL, "bold" if active else "normal"),
                bg=Theme.ACCENT if active else Theme.SIDEBAR_ITEM,
                fg=Theme.TEXT_ON_ACCENT if active else Theme.TEXT_PRIMARY,
                relief=tk.FLAT, bd=0, pady=8, anchor="w", padx=10, cursor="hand2",
                command=lambda n=name: self.switch_chat(n),
            )
            btn.pack(side=tk.LEFT, fill=tk.X, expand=True)
            btn.bind("<Button-3>", lambda e, n=name: self._show_context_menu(e, n))
            btn.bind("<Button-2>", lambda e, n=name: self._show_context_menu(e, n))

            delete_btn = tk.Button(
                row, text="🗑", font=Theme.font(Theme.SIZE_SMALL), bg=Theme.DANGER, fg="white",
                activebackground=Theme.DANGER_HOVER, relief=tk.FLAT, bd=0, padx=8, pady=8,
                cursor="hand2", command=lambda n=name: self.delete_chat(n),
            )
            delete_btn.pack(side=tk.RIGHT, padx=(4, 0))

    def _show_context_menu(self, event, chat_name: str) -> None:
        self.context_menu.delete(0, tk.END)
        self.context_menu.add_command(label="📝 Rename", command=lambda: self.rename_chat(chat_name))
        self.context_menu.add_command(label="🧹 Clear messages", command=lambda: self.clear_chat(chat_name))
        self.context_menu.add_separator()
        self.context_menu.add_command(label="🗑 Delete", command=lambda: self.delete_chat(chat_name))
        self.context_menu.tk_popup(event.x_root, event.y_root)

    def create_chat(self) -> None:
        self.chat_counter += 1
        name = f"Chat Session {self.chat_counter}"
        self.chat_store.add_chat(name, f"New session online: {name}.")
        self.current_chat = name
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
            self._render_chat()

    def switch_chat(self, name: str) -> None:
        self.current_chat = name
        self._refresh_sidebar()
        self._render_chat()
        self.entry.focus_set()

    def pick_background_color(self) -> None:
        result = colorchooser.askcolor(title="Choose background color", initialcolor=self.bg)
        if not result or not result[1]:
            return
        self.bg = result[1]
        for widget in (self.root, self.main, self.canvas, self.scroll_frame, self.header_bar):
            widget.configure(bg=self.bg)
        self.title_label.configure(bg=self.bg)
        self.status_label.configure(bg=self.bg)
        self._render_chat()

    # ---------------------------- chat display ---------------------------- #

    def _on_canvas_resize(self, event) -> None:
        self.canvas.itemconfig(self.canvas_window, width=event.width)
        if self._resize_job is not None:
            self.root.after_cancel(self._resize_job)
        self._resize_job = self.root.after(120, self._render_chat)

    def _on_mousewheel(self, event) -> None:
        delta = -1 if event.delta > 0 else 1
        self.canvas.yview_scroll(delta * 2, "units")

    def _wrap_width(self) -> int:
        available = self.canvas.winfo_width() or 700
        return max(self.MIN_WRAP, int(available * 0.62))

    def _render_chat(self) -> None:
        for widget in self.scroll_frame.winfo_children():
            widget.destroy()
        self.title_label.configure(text=self.current_chat)
        for message in self.chat_store.chats[self.current_chat]:
            self._render_bubble(message)
        self.root.update_idletasks()
        self.canvas.configure(scrollregion=self.canvas.bbox("all"))
        self.canvas.yview_moveto(1.0)

    def _render_bubble(self, message: Message) -> None:
        is_user = message.is_user
        bubble_color = Theme.BUBBLE_USER if is_user else Theme.BUBBLE_BOT
        text_color = Theme.TEXT_PRIMARY if is_user else Theme.TEXT_BOT
        avatar = "🧑" if is_user else "🤖"
        align_side = tk.RIGHT if is_user else tk.LEFT
        anchor_pos = "ne" if is_user else "nw"

        row = tk.Frame(self.scroll_frame, bg=self.bg, pady=5)
        row.pack(fill=tk.X, expand=True)

        wrapper = tk.Frame(row, bg=self.bg)
        wrapper.pack(side=align_side, anchor=anchor_pos, padx=6)

        header = tk.Frame(wrapper, bg=self.bg)
        header.pack(fill=tk.X, pady=(0, 3))
        tk.Label(
            header, text=f"{avatar} {message.sender}  ·  {message.timestamp}",
            fg=Theme.TEXT_MUTED, bg=self.bg, font=Theme.font(Theme.SIZE_TINY, "bold"),
        ).pack(side=align_side)

        content = tk.Frame(wrapper, bg=self.bg)
        content.pack(fill=tk.X)

        bubble = self._make_bubble_canvas(content, message.text, bubble_color, text_color)
        bubble.pack(side=align_side, anchor=anchor_pos)

        copy_btn = tk.Button(
            content, text="📋", font=Theme.font(Theme.SIZE_TINY, "bold"), bg=Theme.SIDEBAR_ITEM,
            fg=Theme.TEXT_MUTED, activebackground=Theme.ACCENT, activeforeground=Theme.TEXT_ON_ACCENT,
            relief=tk.FLAT, bd=0, padx=6, pady=4, cursor="hand2",
            command=lambda t=message.text, b=None: self._copy(t),
        )

        def show_copy(_e=None):
            if is_user:
                copy_btn.pack(side=tk.LEFT, padx=(0, 6), anchor="s")
            else:
                copy_btn.pack(side=tk.RIGHT, padx=(6, 0), anchor="s")

        def hide_copy(_e=None):
            copy_btn.pack_forget()

        for widget in (wrapper, bubble):
            widget.bind("<Enter>", show_copy)
            widget.bind("<Leave>", hide_copy)

    def _make_bubble_canvas(self, parent, text, bg_color, fg_color) -> tk.Canvas:
        wrap = self._wrap_width()
        font = Theme.font(Theme.SIZE_BODY)

        probe = tk.Label(parent, text=text, font=font, wraplength=wrap, justify=tk.LEFT)
        probe.update_idletasks()
        text_w = probe.winfo_reqwidth()
        text_h = probe.winfo_reqheight()
        probe.destroy()

        width = text_w + 2 * self.BUBBLE_PAD_X
        height = text_h + 2 * self.BUBBLE_PAD_Y

        canvas = tk.Canvas(parent, width=width, height=height, bg=self.bg, bd=0, highlightthickness=0)
        rounded_rect(canvas, 0, 0, width, height, radius=16, fill=bg_color, outline=bg_color)
        canvas.create_text(
            self.BUBBLE_PAD_X, self.BUBBLE_PAD_Y, text=text, fill=fg_color, font=font,
            anchor="nw", width=wrap, justify=tk.LEFT,
        )
        return canvas

    def _copy(self, text: str) -> None:
        self.root.clipboard_clear()
        self.root.clipboard_append(text)
        self._flash_status("Copied to clipboard ✓")

    def _flash_status(self, text: str, ms: int = 1800) -> None:
        self.status_label.configure(text=text)
        self.root.after(ms, lambda: self.status_label.configure(text=""))

    # ------------------------------ messaging ------------------------------ #

    def _append(self, sender: str, text: str, is_user: bool) -> None:
        self.chat_store.append(self.current_chat, Message(sender, text, is_user))
        self._render_chat()

    def _append_bot(self, text: str) -> None:
        self._append("PrimeRobo", text, is_user=False)

    def _cancel_teaching(self, _event=None) -> None:
        if self.teaching_mode:
            self.teaching_mode = False
            self.pending_question = ""
            self._append_bot("Learning phase cancelled.")

    # ------------------------------ routing ------------------------------ #

    _TIME_QUERIES = {"what is the time", "what is time", "time", "current time"}
    _DATE_QUERIES = {
        "what is the date", "what is date", "date", "today's date",
        "what is today", "today", "day",
    }
    _DEFINE_RE = re.compile(r"^(?:define|meaning of|what is the meaning of)\s+([a-zA-Z0-9\s\-_]+)$")
    _WIKI_RE = re.compile(r"^(?:who is|who was|tell me about|search up)\s+([a-zA-Z0-9\s\-_]+)$")

    def handle_send(self, _event=None) -> None:
        text = self.entry.get().strip()
        if not text:
            return
        self.entry.delete(0, tk.END)
        self._append("You", text, is_user=True)

        if text.lower() == "quit":
            self.root.quit()
            return

        if self.teaching_mode:
            self._handle_teaching_reply(text)
            return

        lowered = text.lower().strip()

        if lowered in self._TIME_QUERIES:
            self._append_bot(f"Current time: {datetime.now().strftime('%I:%M %p')}")
            return

        if lowered in self._DATE_QUERIES:
            self._append_bot(f"Today is {datetime.now().strftime('%A, %B %d, %Y')}")
            return

        define_match = self._DEFINE_RE.match(lowered)
        if define_match:
            self._lookup_definition(define_match.group(1).strip())
            return

        wiki_match = self._WIKI_RE.match(lowered)
        if wiki_match:
            self._lookup_wikipedia(wiki_match.group(1).strip())
            return

        try:
            result = parse_and_calculate(text)
        except ValueError as exc:
            self._append_bot(f"⚠️ {exc}")
            return
        if result is not None:
            self._append_bot(f"Result: {result:g}")
            return

        answer = self.knowledge_base.find_answer(text)
        if answer:
            self._append_bot(answer)
            return

        self._append_bot(
            "I don't know that one yet. Reply with the answer to teach me, "
            "or type 'skip' to move on."
        )
        self.teaching_mode = True
        self.pending_question = text

    def _handle_teaching_reply(self, text: str) -> None:
        if text.lower() != "skip":
            self.knowledge_base.teach(self.pending_question, text)
            self._append_bot("Got it — I'll remember that.")
        else:
            self._append_bot("Okay, skipped.")
        self.teaching_mode = False
        self.pending_question = ""

    def _lookup_definition(self, word: str) -> None:
        self.send_button.configure(state="disabled", text="…")
        self._append_bot(f"Looking up '{word}'…")

        def done(result: Optional[str]):
            self.send_button.configure(state="normal", text="TRANSMIT")
            final = result or f"No definition found online for '{word}'."
            self.chat_store.replace_last(self.current_chat, Message("PrimeRobo", final, False))
            self._render_chat()

        self.network.run(lambda: NetworkService.fetch_definition(word), done)

    def _lookup_wikipedia(self, subject: str) -> None:
        self.send_button.configure(state="disabled", text="…")
        self._append_bot(f"Searching for '{subject}'…")

        def done(result: Optional[str]):
            self.send_button.configure(state="normal", text="TRANSMIT")
            final = result or f"No page found for '{subject}'."
            self.chat_store.replace_last(self.current_chat, Message("PrimeRobo", final, False))
            self._render_chat()

        self.network.run(lambda: NetworkService.fetch_wikipedia_summary(subject), done)


def main() -> None:
    root = tk.Tk()
    PrimeRoboApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()