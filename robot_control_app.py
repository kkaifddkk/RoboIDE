import gc
import json
import math
import os
import queue
import re
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import traceback
from contextlib import redirect_stderr, redirect_stdout
from datetime import datetime
from tkinter import filedialog

import customtkinter as ctk
import esptool
import serial
from serial.tools import list_ports


ctk.set_appearance_mode("Dark")
ctk.set_default_color_theme("blue")

UI_THEME = {
    "app_bg": "#05070E",
    "panel_bg": "#121826",
    "card_bg": "#1A2232",
    "card_border": "#4A5264",
    "input_bg": "#0B111D",
    "input_border": "#3B455B",
    "input_focus": "#7AA2F7",
    "text_primary": "#E9EEF8",
    "console_bg": "#060A12",
    "console_text": "#D9DEE8",
    "button_refresh": "#2C364B",
    "button_refresh_hover": "#3C4760",
    "gradient_start": "#5A5A5A",
    "gradient_end": "#0A0A0A",
}


DEFAULT_SCRIPT = """import time
import serial

# Variables provided by the app:
# COM_PORT / SELECTED_COM: selected COM port string
# ROBOT_IP: IP address from connection settings

print(f"Using COM port: {COM_PORT}")
print(f"Using robot IP: {ROBOT_IP}")

# Example: your robot control logic
for i in range(3):
    print(f"Heartbeat #{i + 1}")
    time.sleep(0.2)

print("Script completed.")
"""

BOARD_PROFILES = [
    {
        "label": "Авто (любая плата)",
        "keywords": [],
        "vid_pid": [],
    },
    {
        "label": "Arduino Uno",
        "keywords": ["uno", "arduino uno"],
        "vid_pid": [(0x2341, 0x0043), (0x2A03, 0x0043)],
    },
    {
        "label": "Arduino Nano",
        # ch340/wchusb is a generic USB-UART bridge used by many Arduino clones,
        # not a reliable Nano identifier.
        "keywords": ["nano", "arduino nano"],
        # Only keep Nano-specific IDs here. USB-UART bridges (CH340/FTDI) are not board IDs.
        "vid_pid": [(0x2341, 0x0015)],
    },
    {
        "label": "Arduino Mega 2560",
        "keywords": ["mega", "mega 2560", "arduino mega"],
        "vid_pid": [(0x2341, 0x0010), (0x2A03, 0x0010)],
    },
    {
        "label": "ESP32 DevKit",
        "keywords": ["esp32", "silicon labs", "cp210", "ch340"],
        # CH340 is a generic bridge; not a reliable ESP32 identifier.
        "vid_pid": [(0x10C4, 0xEA60)],
    },
    {
        "label": "ESP8266 (NodeMCU/Wemos)",
        "keywords": ["esp8266", "nodemcu", "wemos", "cp210", "ch340"],
        # CH340 is a generic bridge; not a reliable ESP8266 identifier.
        "vid_pid": [(0x10C4, 0xEA60)],
    },
]


class RobotControlApp(ctk.CTk):
    def __init__(self) -> None:
        super().__init__()

        self.title("IDE")
        self.geometry("1280x760")
        self.minsize(1040, 640)
        self.configure(fg_color=UI_THEME["app_bg"])
        self._gradient_image = None
        self._gradient_size = (0, 0)
        self._active_tab_gradient_image = None
        self._gradient_angle = -135.0
        self._gradient_resize_job = None
        self.gradient_bg_label = ctk.CTkLabel(self, text="")
        self.gradient_bg_label.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.gradient_bg_label.lower()

        self.grid_columnconfigure(0, weight=3, uniform="layout")
        self.grid_columnconfigure(1, weight=7, uniform="layout")
        self.grid_rowconfigure(0, weight=1)
        self.port_display_to_device = {}
        self.port_display_to_info = {}
        self.tracked_serial_connections = set()
        self.tracked_board_objects = set()
        self.script_thread = None
        self.device_task_thread = None
        self.stop_event = threading.Event()
        self.gui_queue = queue.Queue()
        self.selected_port = ""
        self.board_profiles = {item["label"]: item for item in BOARD_PROFILES}
        self.desktop_dir = os.path.join(os.path.expanduser("~"), "Desktop")
        self.projects_root_dir = ""
        self.projects_current_dir = ""
        self.project_aliases = {}
        self.project_file_buttons = {}
        self.selected_project_file = ""
        self.cmd_current_dir = self.desktop_dir
        self.cmd_thread = None
        self.bt_status_var = ctk.StringVar(value="Bluetooth: не проверено")

        self._build_tabs()
        self._build_left_panel()
        self._build_right_panel()
        self._build_projects_tab()
        self._build_cmd_tab()
        self._bind_layout_independent_shortcuts()

        self.refresh_ports()
        self._initialize_default_projects_folder()
        self.bind("<Configure>", self._handle_gradient_resize)
        self.after(80, self._refresh_gradient_background)
        self.log_to_console("IDE запущено.")
        self.after(100, self._process_gui_queue)

    def _bind_layout_independent_shortcuts(self) -> None:
        # Tk recognizes Ctrl+Latin shortcuts by keysym. On non-English layouts
        # (e.g. Cyrillic) we additionally map by physical keycode.
        targets = [
            getattr(self, "editor_text", None),
            getattr(self, "cmd_output", None),
            getattr(self, "cmd_entry", None),
        ]

        def _resolve_widget(w):
            if w is None:
                return None
            return getattr(w, "_textbox", w)

        def _on_ctrl_key(event):
            # Windows virtual keycodes for A/C/V/X/Z/Y.
            code = int(getattr(event, "keycode", 0))
            widget = event.widget
            try:
                if code == 65:  # A
                    widget.tag_add("sel", "1.0", "end-1c")
                    widget.mark_set("insert", "end-1c")
                    widget.see("insert")
                    return "break"
                if code == 67:  # C
                    widget.event_generate("<<Copy>>")
                    return "break"
                if code == 86:  # V
                    widget.event_generate("<<Paste>>")
                    return "break"
                if code == 88:  # X
                    widget.event_generate("<<Cut>>")
                    return "break"
                if code == 90:  # Z
                    widget.event_generate("<<Undo>>")
                    return "break"
                if code == 89:  # Y
                    widget.event_generate("<<Redo>>")
                    return "break"
            except Exception:
                return None
            return None

        for target in targets:
            tw = _resolve_widget(target)
            if tw is not None:
                tw.bind("<Control-KeyPress>", _on_ctrl_key, add="+")

    @staticmethod
    def _hex_to_rgb(hex_color: str) -> tuple[int, int, int]:
        color = hex_color.lstrip("#")
        return tuple(int(color[i : i + 2], 16) for i in (0, 2, 4))

    @staticmethod
    def _rgb_to_hex(rgb_color: tuple[int, int, int]) -> str:
        return "#{:02x}{:02x}{:02x}".format(*rgb_color)

    def _create_diagonal_gradient(
        self, width: int, height: int, angle_deg: float, step: int = 2
    ) -> tk.PhotoImage:
        start = self._hex_to_rgb(UI_THEME["gradient_start"])
        end = self._hex_to_rgb(UI_THEME["gradient_end"])
        image = tk.PhotoImage(width=width, height=height)
        angle_rad = math.radians(angle_deg)
        direction_x = math.cos(angle_rad)
        direction_y = math.sin(angle_rad)

        corners = [
            0 * direction_x + 0 * direction_y,
            (width - 1) * direction_x + 0 * direction_y,
            0 * direction_x + (height - 1) * direction_y,
            (width - 1) * direction_x + (height - 1) * direction_y,
        ]
        min_projection = min(corners)
        max_projection = max(corners)
        denominator = max(max_projection - min_projection, 1e-9)

        step = max(1, int(step))
        for y in range(0, height, step):
            for x in range(0, width, step):
                projection = x * direction_x + y * direction_y
                ratio = (projection - min_projection) / denominator
                color = (
                    int(start[0] + (end[0] - start[0]) * ratio),
                    int(start[1] + (end[1] - start[1]) * ratio),
                    int(start[2] + (end[2] - start[2]) * ratio),
                )
                image.put(
                    self._rgb_to_hex(color),
                    to=(x, y, min(x + step, width), min(y + step, height)),
                )
        return image

    def _refresh_gradient_background(self, force: bool = False) -> None:
        width = max(self.winfo_width(), 2)
        height = max(self.winfo_height(), 2)
        if self._gradient_size == (width, height) and not force:
            return
        max_dim = max(width, height)
        # Adaptive quality: large windows get bigger step to avoid UI freezes.
        step = 3 if max_dim <= 900 else 5 if max_dim <= 1400 else 7
        self._gradient_image = self._create_diagonal_gradient(
            width, height, self._gradient_angle, step=step
        )
        self._gradient_size = (width, height)
        self.gradient_bg_label.configure(image=self._gradient_image)
        self._update_active_tab_gradient_layer()
        self.tabview.lift()

    def _handle_gradient_resize(self, _event=None) -> None:
        # Debounce resize events (fullscreen/maximize triggers many Configure events).
        try:
            if self._gradient_resize_job is not None:
                self.after_cancel(self._gradient_resize_job)
        except Exception:
            pass
        self._gradient_resize_job = self.after(140, self._refresh_gradient_background)

    def _update_active_tab_gradient_layer(self) -> None:
        current_tab_name = self.tabview.get()
        if current_tab_name == "IDE":
            target_tab = self.ide_tab
            target_label = self.ide_tab_bg_label
        elif current_tab_name == "Проекты":
            target_tab = self.projects_tab
            target_label = self.projects_tab_bg_label
        else:
            target_tab = self.cmd_tab
            target_label = self.cmd_tab_bg_label

        width = max(target_tab.winfo_width(), 2)
        height = max(target_tab.winfo_height(), 2)
        max_dim = max(width, height)
        step = 4 if max_dim <= 900 else 6 if max_dim <= 1400 else 8
        self._active_tab_gradient_image = self._create_diagonal_gradient(
            width, height, self._gradient_angle, step=step
        )
        target_label.configure(image=self._active_tab_gradient_image)

    def _animate_gradient_background(self) -> None:
        self._gradient_angle = (self._gradient_angle + 4.0) % 360
        self._update_active_tab_gradient_layer()
        self.after(16, self._animate_gradient_background)

    def _build_tabs(self) -> None:
        self.tabview = ctk.CTkTabview(
            self,
            corner_radius=14,
            fg_color="#070A12",
            bg_color="#070A12",
            segmented_button_selected_color="#2563EB",
            segmented_button_selected_hover_color="#1D4ED8",
            segmented_button_unselected_color="#334155",
            segmented_button_unselected_hover_color="#475569",
            text_color=UI_THEME["text_primary"],
        )
        self.tabview.grid(row=0, column=0, columnspan=2, sticky="nsew", padx=12, pady=12)
        self.tabview.add("IDE")
        self.tabview.add("Проекты")
        self.tabview.add("CMD")
        self.ide_tab = self.tabview.tab("IDE")
        self.projects_tab = self.tabview.tab("Проекты")
        self.cmd_tab = self.tabview.tab("CMD")
        self.ide_tab.configure(fg_color="transparent", bg_color="transparent")
        self.projects_tab.configure(fg_color="transparent", bg_color="transparent")
        self.cmd_tab.configure(fg_color="transparent", bg_color="transparent")

        self.ide_tab_bg_label = ctk.CTkLabel(self.ide_tab, text="")
        self.ide_tab_bg_label.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.ide_tab_bg_label.lower()

        self.projects_tab_bg_label = ctk.CTkLabel(self.projects_tab, text="")
        self.projects_tab_bg_label.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.projects_tab_bg_label.lower()

        self.cmd_tab_bg_label = ctk.CTkLabel(self.cmd_tab, text="")
        self.cmd_tab_bg_label.place(relx=0, rely=0, relwidth=1, relheight=1)
        self.cmd_tab_bg_label.lower()
        self.ide_tab.grid_columnconfigure(0, weight=3, uniform="layout")
        self.ide_tab.grid_columnconfigure(1, weight=7, uniform="layout")
        self.ide_tab.grid_rowconfigure(0, weight=1)

    def _build_left_panel(self) -> None:
        self.left_panel = ctk.CTkFrame(
            self.ide_tab,
            corner_radius=16,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.left_panel.grid(row=0, column=0, sticky="nsew", padx=(16, 8), pady=16)
        self.left_panel.grid_columnconfigure(0, weight=1)
        self.left_panel.grid_rowconfigure(1, weight=1)

        self.connection_frame = ctk.CTkFrame(
            self.left_panel,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.connection_frame.grid(row=0, column=0, sticky="new", padx=12, pady=(12, 8))
        self.connection_frame.grid_columnconfigure(0, weight=1)
        self.connection_frame.grid_columnconfigure(1, weight=0)

        conn_label = ctk.CTkLabel(
            self.connection_frame,
            text="Connection Settings",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=18, weight="bold"),
        )
        conn_label.grid(row=0, column=0, columnspan=2, sticky="w", padx=12, pady=(10, 12))

        com_label = ctk.CTkLabel(
            self.connection_frame, text="COM Port", text_color=UI_THEME["text_primary"]
        )
        com_label.grid(row=3, column=0, columnspan=2, sticky="w", padx=12, pady=(0, 4))

        board_label = ctk.CTkLabel(
            self.connection_frame, text="Плата", text_color=UI_THEME["text_primary"]
        )
        board_label.grid(row=1, column=0, columnspan=2, sticky="w", padx=12, pady=(0, 4))

        default_board = BOARD_PROFILES[0]["label"]
        self.board_var = ctk.StringVar(value=default_board)
        self.board_menu = ctk.CTkOptionMenu(
            self.connection_frame,
            values=list(self.board_profiles.keys()),
            variable=self.board_var,
            dynamic_resizing=False,
            command=lambda _value: self.refresh_ports(),
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            button_color=UI_THEME["button_refresh"],
            button_hover_color=UI_THEME["button_refresh_hover"],
            dropdown_fg_color=UI_THEME["card_bg"],
            dropdown_hover_color=UI_THEME["button_refresh"],
            text_color=UI_THEME["text_primary"],
        )
        self.board_menu.grid(row=2, column=0, columnspan=2, sticky="ew", padx=12, pady=(0, 12))

        self.com_var = ctk.StringVar(value="No ports")
        self.com_menu = ctk.CTkOptionMenu(
            self.connection_frame,
            values=["No ports"],
            variable=self.com_var,
            dynamic_resizing=False,
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            button_color=UI_THEME["button_refresh"],
            button_hover_color=UI_THEME["button_refresh_hover"],
            dropdown_fg_color=UI_THEME["card_bg"],
            dropdown_hover_color=UI_THEME["button_refresh"],
            text_color=UI_THEME["text_primary"],
        )
        self.com_menu.grid(row=4, column=0, sticky="ew", padx=(12, 6), pady=(0, 12))

        self.refresh_button = ctk.CTkButton(
            self.connection_frame,
            text="🔄",
            width=40,
            command=self.refresh_ports,
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["button_refresh"],
            hover_color=UI_THEME["button_refresh_hover"],
        )
        self.refresh_button.grid(row=4, column=1, sticky="e", padx=(0, 12), pady=(0, 12))

        ip_label = ctk.CTkLabel(
            self.connection_frame, text="IP Address", text_color=UI_THEME["text_primary"]
        )
        ip_label.grid(row=5, column=0, columnspan=2, sticky="w", padx=12, pady=(0, 4))

        self.ip_entry = ctk.CTkEntry(
            self.connection_frame,
            placeholder_text="192.168.0.10",
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            border_color=UI_THEME["input_border"],
            text_color=UI_THEME["text_primary"],
        )
        self.ip_entry.insert(0, "192.168.0.10")
        self.ip_entry.grid(row=6, column=0, columnspan=2, sticky="ew", padx=12, pady=(0, 10))

        port_label = ctk.CTkLabel(
            self.connection_frame, text="Port", text_color=UI_THEME["text_primary"]
        )
        port_label.grid(row=7, column=0, columnspan=2, sticky="w", padx=12, pady=(0, 4))

        self.port_entry = ctk.CTkEntry(
            self.connection_frame,
            placeholder_text="5000",
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            border_color=UI_THEME["input_border"],
            text_color=UI_THEME["text_primary"],
        )
        self.port_entry.insert(0, "5000")
        self.port_entry.grid(row=8, column=0, columnspan=2, sticky="ew", padx=12, pady=(0, 12))

        self.bt_only_var = ctk.BooleanVar(value=False)
        bt_only_switch = ctk.CTkSwitch(
            self.connection_frame,
            text="Только Bluetooth COM",
            variable=self.bt_only_var,
            command=self.refresh_ports,
            text_color=UI_THEME["text_primary"],
            progress_color="#2563EB",
        )
        bt_only_switch.grid(row=9, column=0, columnspan=2, sticky="w", padx=12, pady=(0, 8))

        bt_status_label = ctk.CTkLabel(
            self.connection_frame,
            textvariable=self.bt_status_var,
            text_color=UI_THEME["text_primary"],
            anchor="w",
        )
        bt_status_label.grid(row=10, column=0, sticky="ew", padx=(12, 6), pady=(0, 10))

        self.bt_check_button = ctk.CTkButton(
            self.connection_frame,
            text="Проверить BT",
            width=110,
            height=32,
            corner_radius=10,
            fg_color="#0EA5E9",
            hover_color="#0284C7",
            command=self.check_bluetooth_connection,
        )
        self.bt_check_button.grid(row=10, column=1, sticky="e", padx=(0, 12), pady=(0, 10))

        self.console_frame = ctk.CTkFrame(
            self.left_panel,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.console_frame.grid(row=1, column=0, sticky="nsew", padx=12, pady=(8, 12))
        self.console_frame.grid_columnconfigure(0, weight=1)
        self.console_frame.grid_rowconfigure(1, weight=1)

        console_label = ctk.CTkLabel(
            self.console_frame,
            text="System Output",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=18, weight="bold"),
        )
        console_label.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 8))

        self.console_text = ctk.CTkTextbox(
            self.console_frame,
            corner_radius=10,
            fg_color=UI_THEME["console_bg"],
            text_color=UI_THEME["console_text"],
            font=ctk.CTkFont(family="Consolas", size=12),
            wrap="word",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.console_text.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 8))
        self.console_text.configure(state="disabled")

        clear_button = ctk.CTkButton(
            self.console_frame,
            text="Clear Console",
            height=34,
            corner_radius=10,
            fg_color="#475569",
            hover_color="#64748B",
            command=self.clear_console,
        )
        clear_button.grid(row=2, column=0, sticky="e", padx=12, pady=(0, 10))

    def _build_right_panel(self) -> None:
        self.right_panel = ctk.CTkFrame(
            self.ide_tab,
            corner_radius=16,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.right_panel.grid(row=0, column=1, sticky="nsew", padx=(8, 16), pady=16)
        self.right_panel.grid_columnconfigure(0, weight=1)
        self.right_panel.grid_rowconfigure(0, weight=1)

        self.editor_frame = ctk.CTkFrame(
            self.right_panel,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.editor_frame.grid(row=0, column=0, sticky="nsew", padx=12, pady=(12, 8))
        self.editor_frame.grid_columnconfigure(0, weight=1)
        self.editor_frame.grid_rowconfigure(1, weight=1)

        editor_label = ctk.CTkLabel(
            self.editor_frame,
            text="Скрипт редактор",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=18, weight="bold"),
        )
        editor_label.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 8))

        self.editor_text = ctk.CTkTextbox(
            self.editor_frame,
            corner_radius=10,
            fg_color=UI_THEME["input_bg"],
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(family="Consolas", size=13),
            wrap="none",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.editor_text.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 12))
        self.editor_text.insert("1.0", DEFAULT_SCRIPT)

        actions_frame = ctk.CTkFrame(
            self.right_panel,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        actions_frame.grid(row=1, column=0, sticky="ew", padx=12, pady=(8, 12))
        actions_frame.grid_columnconfigure((0, 1), weight=1)

        self.run_button = ctk.CTkButton(
            actions_frame,
            text="Запустить",
            height=46,
            corner_radius=12,
            fg_color="#1FAA59",
            hover_color="#168A46",
            font=ctk.CTkFont(size=14, weight="bold"),
            command=self.run_script,
        )
        self.run_button.grid(row=0, column=0, sticky="ew", padx=(10, 6), pady=10)

        stop_button = ctk.CTkButton(
            actions_frame,
            text="Экстренный стоп",
            height=46,
            corner_radius=12,
            fg_color="#C0392B",
            hover_color="#992D22",
            font=ctk.CTkFont(size=14, weight="bold"),
            command=self.emergency_stop,
        )
        stop_button.grid(row=0, column=1, sticky="ew", padx=(6, 10), pady=10)

        self.erase_button = ctk.CTkButton(
            actions_frame,
            text="Очистить память",
            height=40,
            corner_radius=12,
            fg_color="#3B82F6",
            hover_color="#2563EB",
            font=ctk.CTkFont(size=13, weight="bold"),
            command=self.erase_device_flash,
        )
        self.erase_button.grid(row=1, column=0, sticky="ew", padx=(10, 6), pady=(0, 10))

        self.flash_button = ctk.CTkButton(
            actions_frame,
            text="Прошить MicroPython",
            height=40,
            corner_radius=12,
            fg_color="#7C3AED",
            hover_color="#6D28D9",
            font=ctk.CTkFont(size=13, weight="bold"),
            command=self._select_and_flash_firmware,
        )
        self.flash_button.grid(row=1, column=1, sticky="ew", padx=(6, 10), pady=(0, 10))

    def _build_projects_tab(self) -> None:
        self.projects_tab.grid_columnconfigure(0, weight=1)
        self.projects_tab.grid_rowconfigure(1, weight=1)

        top_frame = ctk.CTkFrame(
            self.projects_tab,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        top_frame.grid(row=0, column=0, sticky="ew", padx=12, pady=(12, 8))
        top_frame.grid_columnconfigure(0, weight=1)

        title = ctk.CTkLabel(
            top_frame,
            text="Управление проектами",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=18, weight="bold"),
        )
        title.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 6))

        self.project_folder_entry = ctk.CTkEntry(
            top_frame,
            placeholder_text="Путь к корневой папке проектов (можно вставить вручную)",
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            border_color=UI_THEME["input_border"],
            text_color=UI_THEME["text_primary"],
        )
        self.project_folder_entry.insert(0, os.path.join(self.desktop_dir, "RobotProjects"))
        self.project_folder_entry.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 8))

        folder_buttons = ctk.CTkFrame(top_frame, fg_color="transparent")
        folder_buttons.grid(row=2, column=0, sticky="ew", padx=12, pady=(0, 10))
        folder_buttons.grid_columnconfigure((0, 1, 2, 3), weight=1)

        choose_root_button = ctk.CTkButton(
            folder_buttons,
            text="Выбрать корень…",
            command=self.choose_projects_root_folder,
            corner_radius=10,
            fg_color="#2563EB",
            hover_color="#1D4ED8",
        )
        choose_root_button.grid(row=0, column=0, sticky="ew", padx=(0, 6))

        refresh_files_button = ctk.CTkButton(
            folder_buttons,
            text="Обновить список файлов",
            command=self.load_project_files,
            corner_radius=10,
            fg_color="#334155",
            hover_color="#475569",
        )
        refresh_files_button.grid(row=0, column=1, sticky="ew", padx=6)

        open_in_explorer_button = ctk.CTkButton(
            folder_buttons,
            text="Открыть папку в проводнике",
            command=self.open_projects_folder_in_explorer,
            corner_radius=10,
            fg_color="#475569",
            hover_color="#64748B",
        )
        open_in_explorer_button.grid(row=0, column=2, sticky="ew", padx=(6, 0))

        self.projects_back_button = ctk.CTkButton(
            folder_buttons,
            text="Назад",
            command=self.go_back_projects_folder,
            corner_radius=10,
            fg_color="#334155",
            hover_color="#475569",
        )
        self.projects_back_button.grid(row=0, column=3, sticky="ew", padx=(6, 0))
        self.projects_back_button.grid_remove()

        files_card = ctk.CTkFrame(
            self.projects_tab,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        files_card.grid(row=1, column=0, sticky="nsew", padx=12, pady=(8, 12))
        files_card.grid_columnconfigure(0, weight=1)
        files_card.grid_columnconfigure(1, weight=0)
        files_card.grid_rowconfigure(1, weight=1)

        files_title = ctk.CTkLabel(
            files_card,
            text="Файлы проекта (.py, .ino, .cpp, .c, .cc, .cxx) и папки",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=15, weight="bold"),
        )
        files_title.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 8))

        self.projects_path_label = ctk.CTkLabel(
            files_card,
            text="Папка: (не выбрана)",
            text_color=UI_THEME["text_primary"],
            anchor="w",
        )
        self.projects_path_label.grid(row=0, column=1, sticky="e", padx=12, pady=(10, 8))

        self.project_files_frame = ctk.CTkScrollableFrame(
            files_card,
            corner_radius=10,
            fg_color=UI_THEME["input_bg"],
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        self.project_files_frame.grid(row=1, column=0, sticky="nsew", padx=12, pady=(0, 8))
        self.project_files_frame.grid_columnconfigure(0, weight=1)

        bottom_controls = ctk.CTkFrame(files_card, fg_color="transparent")
        bottom_controls.grid(row=2, column=0, sticky="ew", padx=12, pady=(0, 10))
        bottom_controls.grid_columnconfigure(0, weight=1)

        self.project_alias_entry = ctk.CTkEntry(
            bottom_controls,
            placeholder_text="Новое название файла",
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            border_color=UI_THEME["input_border"],
            text_color=UI_THEME["text_primary"],
        )
        self.project_alias_entry.grid(row=0, column=0, sticky="ew", pady=(0, 8))

        action_buttons = ctk.CTkFrame(bottom_controls, fg_color="transparent")
        action_buttons.grid(row=1, column=0, sticky="ew")
        action_buttons.grid_columnconfigure((0, 1), weight=1)

        alias_button = ctk.CTkButton(
            action_buttons,
            text="Переименовать файл",
            command=self.rename_project_button_alias,
            corner_radius=10,
            fg_color="#7C3AED",
            hover_color="#6D28D9",
        )
        alias_button.grid(row=0, column=0, sticky="ew", padx=(0, 6))

        import_button = ctk.CTkButton(
            action_buttons,
            text="Загрузить код в основной редактор",
            command=self.import_selected_project_file_to_editor,
            corner_radius=10,
            fg_color="#1FAA59",
            hover_color="#168A46",
        )
        import_button.grid(row=0, column=1, sticky="ew", padx=(6, 0))

    def _initialize_default_projects_folder(self) -> None:
        self._apply_projects_root_from_entry(log=False)

    def _projects_aliases_file_path(self) -> str:
        if not self.projects_root_dir:
            return ""
        return os.path.join(self.projects_root_dir, ".project_aliases.json")

    def _load_project_aliases(self) -> None:
        self.project_aliases = {}
        aliases_path = self._projects_aliases_file_path()
        if not aliases_path or not os.path.exists(aliases_path):
            return
        try:
            with open(aliases_path, "r", encoding="utf-8") as aliases_file:
                loaded = json.load(aliases_file)
            if isinstance(loaded, dict):
                # Keys are stored as relative paths from projects_root_dir (posix-style).
                # Backward-compatible: older versions stored only basenames.
                normalized: dict[str, str] = {}
                for k, v in loaded.items():
                    key = str(k).replace("\\", "/")
                    normalized[key] = str(v)
                self.project_aliases = normalized
        except Exception:
            self.project_aliases = {}

    def _save_project_aliases(self) -> None:
        aliases_path = self._projects_aliases_file_path()
        if not aliases_path:
            return
        try:
            with open(aliases_path, "w", encoding="utf-8") as aliases_file:
                json.dump(self.project_aliases, aliases_file, ensure_ascii=False, indent=2)
        except Exception as exc:
            self.log_to_console(f"Не удалось сохранить псевдонимы файлов: {exc}")

    def _clear_project_file_buttons(self) -> None:
        for widget in self.project_files_frame.winfo_children():
            widget.destroy()
        self.project_file_buttons = {}

    def _apply_projects_root_from_entry(self, log: bool = True) -> None:
        if not self.project_folder_entry:
            return
        root_path = self.project_folder_entry.get().strip()
        if not root_path:
            return
        root_path = os.path.abspath(os.path.expanduser(root_path))
        if not os.path.isdir(root_path):
            if log:
                self.log_to_console(
                    "Папка проектов не найдена. Укажите существующую папку (путь до папки проекта)"
                )
            self.projects_root_dir = root_path
            self.projects_current_dir = root_path
            self.load_project_files(log=False)
            return

        self.projects_root_dir = root_path
        if not self.projects_current_dir or not os.path.isdir(self.projects_current_dir):
            self.projects_current_dir = self.projects_root_dir
        if not os.path.abspath(self.projects_current_dir).startswith(os.path.abspath(self.projects_root_dir) + os.sep) and os.path.abspath(self.projects_current_dir) != os.path.abspath(self.projects_root_dir):
            self.projects_current_dir = self.projects_root_dir

        self._load_project_aliases()
        self.load_project_files(log=False)
        if log:
            self.log_to_console(f"Корень проектов: {self.projects_root_dir}")

    def choose_projects_root_folder(self) -> None:
        initial_dir = self.projects_root_dir or self.desktop_dir
        chosen = filedialog.askdirectory(title="Выберите корневую папку проектов", initialdir=initial_dir)
        if not chosen:
            return
        self.project_folder_entry.delete(0, "end")
        self.project_folder_entry.insert(0, chosen)
        self._apply_projects_root_from_entry(log=True)

    def open_projects_folder_in_explorer(self) -> None:
        if not self.projects_root_dir or not os.path.exists(self.projects_root_dir):
            self._apply_projects_root_from_entry(log=False)
        try:
            target_dir = self.projects_current_dir or self.projects_root_dir
            os.startfile(target_dir)
        except Exception as exc:
            self.log_to_console(f"Не удалось открыть папку проектов: {exc}")

    def load_project_files(self, log: bool = True) -> None:
        if not self.projects_root_dir:
            self._apply_projects_root_from_entry(log=False)
        if not self.projects_root_dir or not os.path.exists(self.projects_root_dir):
            return
        if not self.projects_current_dir:
            self.projects_current_dir = self.projects_root_dir
        if not os.path.exists(self.projects_current_dir):
            self.projects_current_dir = self.projects_root_dir

        allowed_extensions = {".py", ".ino", ".cpp", ".c", ".cc", ".cxx"}
        project_dirs: list[str] = []
        project_files: list[str] = []
        for name in sorted(os.listdir(self.projects_current_dir)):
            full_path = os.path.join(self.projects_current_dir, name)
            if os.path.isdir(full_path):
                project_dirs.append(full_path)
                continue
            _, ext = os.path.splitext(name.lower())
            if os.path.isfile(full_path) and ext in allowed_extensions:
                project_files.append(full_path)

        self._clear_project_file_buttons()
        self.selected_project_file = ""
        if hasattr(self, "projects_back_button"):
            try:
                root_abs = os.path.abspath(self.projects_root_dir)
                cur_abs = os.path.abspath(self.projects_current_dir)
                if cur_abs != root_abs:
                    self.projects_back_button.grid()
                else:
                    self.projects_back_button.grid_remove()
            except Exception:
                self.projects_back_button.grid_remove()
        if hasattr(self, "projects_path_label"):
            try:
                rel_dir = os.path.relpath(self.projects_current_dir, self.projects_root_dir)
            except Exception:
                rel_dir = "."
            rel_dir = "." if rel_dir in {".", ""} else rel_dir
            self.projects_path_label.configure(text=f"Папка: {rel_dir}")

        if not project_files and not project_dirs:
            empty_label = ctk.CTkLabel(
                self.project_files_frame,
                text="Файлы и папки не найдены. Добавьте код или создайте новую папку.",
                text_color=UI_THEME["text_primary"],
                anchor="w",
            )
            empty_label.grid(row=0, column=0, sticky="ew", padx=8, pady=8)
            if log:
                self.log_to_console("В папке проектов пока нет файлов кода.")
            return

        row = 0
        for dir_path in project_dirs:
            dir_name = os.path.basename(dir_path.rstrip("\\/")) + os.sep
            dir_button = ctk.CTkButton(
                self.project_files_frame,
                text=dir_name,
                anchor="w",
                command=lambda p=dir_path: self.enter_projects_folder(p),
                corner_radius=10,
                fg_color="#0F172A",
                hover_color="#1F2937",
            )
            dir_button.grid(row=row, column=0, sticky="ew", padx=8, pady=4)
            row += 1

        for file_path in project_files:
            rel_key = self._project_rel_key(file_path)
            file_name = os.path.basename(file_path)
            alias = self.project_aliases.get(rel_key, file_name)
            file_button = ctk.CTkButton(
                self.project_files_frame,
                text=alias,
                anchor="w",
                command=lambda path=file_path: self.select_project_file(path),
                corner_radius=10,
                fg_color="#334155",
                hover_color="#475569",
            )
            file_button.grid(row=row, column=0, sticky="ew", padx=8, pady=4)
            self.project_file_buttons[file_path] = file_button
            row += 1

        if log:
            self.log_to_console(
                f"Загружено элементов: папок {len(project_dirs)}, файлов {len(project_files)}"
            )

    def _project_rel_key(self, file_path: str) -> str:
        try:
            return os.path.relpath(file_path, self.projects_root_dir).replace("\\", "/")
        except Exception:
            return os.path.basename(file_path)

    def enter_projects_folder(self, folder_path: str) -> None:
        if not self.projects_root_dir:
            self._apply_projects_root_from_entry(log=False)
        try:
            root_abs = os.path.abspath(self.projects_root_dir)
            target_abs = os.path.abspath(folder_path)
            if not (target_abs == root_abs or target_abs.startswith(root_abs + os.sep)):
                self.log_to_console("ОШИБКА: нельзя выходить за пределы корневой папки проектов.")
                return
            if not os.path.isdir(target_abs):
                self.log_to_console("Папка не найдена.")
                return
            self.projects_current_dir = target_abs
            self.load_project_files(log=False)
            self.log_to_console(f"Открыта папка: {os.path.relpath(target_abs, root_abs)}")
        except Exception as exc:
            self.log_to_console(f"Не удалось открыть папку: {exc}")

    def go_back_projects_folder(self) -> None:
        if not self.projects_root_dir:
            self._apply_projects_root_from_entry(log=False)
        if not self.projects_current_dir:
            self.projects_current_dir = self.projects_root_dir
        try:
            root_abs = os.path.abspath(self.projects_root_dir)
            cur_abs = os.path.abspath(self.projects_current_dir)
            if cur_abs == root_abs:
                return
            parent = os.path.dirname(cur_abs)
            if not (parent == root_abs or parent.startswith(root_abs + os.sep)):
                parent = root_abs
            self.projects_current_dir = parent
            self.load_project_files(log=False)
        except Exception as exc:
            self.log_to_console(f"Не удалось перейти назад: {exc}")


    def select_project_file(self, file_path: str) -> None:
        self.selected_project_file = file_path
        for path, button in self.project_file_buttons.items():
            if path == file_path:
                button.configure(fg_color="#2563EB")
            else:
                button.configure(fg_color="#334155")
        selected_name = os.path.basename(file_path)
        self.project_alias_entry.delete(0, "end")
        rel_key = self._project_rel_key(file_path)
        self.project_alias_entry.insert(0, self.project_aliases.get(rel_key, selected_name))
        self.log_to_console(f"Выбран проектный файл: {selected_name}")

    def rename_project_button_alias(self) -> None:
        if not self.selected_project_file:
            self.log_to_console("Сначала выберите файл проекта.")
            return
        new_alias = self.project_alias_entry.get().strip()
        if not new_alias:
            self.log_to_console("Введите новое название файла.")
            return
        file_name = os.path.basename(self.selected_project_file)
        rel_key = self._project_rel_key(self.selected_project_file)
        self.project_aliases[rel_key] = new_alias
        self._save_project_aliases()
        selected_button = self.project_file_buttons.get(self.selected_project_file)
        if selected_button:
            selected_button.configure(text=new_alias)
        self.log_to_console(
            f"Кнопка файла '{file_name}' переименована в '{new_alias}'"
        )

    def import_selected_project_file_to_editor(self) -> None:
        if not self.selected_project_file:
            self.log_to_console("Сначала выберите файл проекта.")
            return
        try:
            with open(self.selected_project_file, "r", encoding="utf-8") as code_file:
                code_text = code_file.read()
        except UnicodeDecodeError:
            self.log_to_console("Файл не в UTF-8. Сохраните файл в UTF-8 и повторите.")
            return
        except Exception as exc:
            self.log_to_console(f"Не удалось прочитать файл: {exc}")
            return

        self.editor_text.delete("1.0", "end")
        self.editor_text.insert("1.0", code_text)
        self.tabview.set("IDE")
        self.log_to_console(
            f"Код из '{os.path.basename(self.selected_project_file)}' загружен в основной редактор."
        )

    def _build_cmd_tab(self) -> None:
        self.cmd_tab.grid_columnconfigure(0, weight=1)
        self.cmd_tab.grid_rowconfigure(1, weight=1)

        cmd_top = ctk.CTkFrame(
            self.cmd_tab,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        cmd_top.grid(row=0, column=0, sticky="ew", padx=12, pady=(12, 8))
        cmd_top.grid_columnconfigure(0, weight=1)

        cmd_title = ctk.CTkLabel(
            cmd_top,
            text="CMD (Windows Command Prompt)",
            text_color=UI_THEME["text_primary"],
            font=ctk.CTkFont(size=18, weight="bold"),
        )
        cmd_title.grid(row=0, column=0, sticky="w", padx=12, pady=(10, 4))

        self.cmd_dir_label = ctk.CTkLabel(
            cmd_top,
            text=f"Текущая папка: {self.cmd_current_dir}",
            text_color=UI_THEME["text_primary"],
            anchor="w",
        )
        self.cmd_dir_label.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 8))

        toolbar = ctk.CTkFrame(cmd_top, fg_color="transparent")
        toolbar.grid(row=2, column=0, sticky="ew", padx=12, pady=(0, 10))
        toolbar.grid_columnconfigure((0, 1), weight=1)

        self.cmd_run_button = ctk.CTkButton(
            toolbar,
            text="Выполнить",
            corner_radius=10,
            fg_color="#2563EB",
            hover_color="#1D4ED8",
            command=self.run_cmd_command,
        )
        self.cmd_run_button.grid(row=0, column=0, sticky="ew", padx=(0, 6))

        open_external_cmd_button = ctk.CTkButton(
            toolbar,
            text="Открыть отдельную CMD",
            corner_radius=10,
            fg_color="#334155",
            hover_color="#475569",
            command=self.open_external_cmd_window,
        )
        open_external_cmd_button.grid(row=0, column=1, sticky="ew", padx=(6, 0))

        cmd_body = ctk.CTkFrame(
            self.cmd_tab,
            corner_radius=14,
            fg_color="transparent",
            bg_color="transparent",
            border_width=1,
            border_color=UI_THEME["card_border"],
        )
        cmd_body.grid(row=1, column=0, sticky="nsew", padx=12, pady=(8, 12))
        cmd_body.grid_columnconfigure(0, weight=1)
        cmd_body.grid_rowconfigure(0, weight=1)

        self.cmd_output = ctk.CTkTextbox(
            cmd_body,
            corner_radius=10,
            fg_color=UI_THEME["console_bg"],
            text_color=UI_THEME["console_text"],
            font=ctk.CTkFont(family="Consolas", size=12),
            border_width=1,
            border_color=UI_THEME["card_border"],
            wrap="word",
        )
        self.cmd_output.grid(row=0, column=0, sticky="nsew", padx=12, pady=(12, 8))
        self.cmd_output.configure(state="disabled")

        self.cmd_entry = ctk.CTkEntry(
            cmd_body,
            placeholder_text="Введите команду CMD, например: dir",
            corner_radius=10,
            height=34,
            fg_color=UI_THEME["input_bg"],
            border_color=UI_THEME["input_border"],
            text_color=UI_THEME["text_primary"],
        )
        self.cmd_entry.grid(row=1, column=0, sticky="ew", padx=12, pady=(0, 12))
        self.cmd_entry.bind("<Return>", lambda _event: self.run_cmd_command())

        self._append_cmd_output("CMD вкладка готова. Введите команду и нажмите Enter.")

    def _append_cmd_output(self, text: str) -> None:
        self.cmd_output.configure(state="normal")
        self.cmd_output.insert("end", f"{text}\n")
        self.cmd_output.see("end")
        self.cmd_output.configure(state="disabled")

    def _queue_cmd_output(self, text: str) -> None:
        self.gui_queue.put(("cmd_output", text))

    def _update_cmd_dir_label(self) -> None:
        self.cmd_dir_label.configure(text=f"Текущая папка: {self.cmd_current_dir}")

    def open_external_cmd_window(self) -> None:
        try:
            subprocess.Popen(["cmd.exe"], cwd=self.cmd_current_dir)
        except Exception as exc:
            self._append_cmd_output(f"Ошибка запуска отдельной CMD: {exc}")

    def run_cmd_command(self) -> None:
        if self.cmd_thread and self.cmd_thread.is_alive():
            self._append_cmd_output("Подождите завершения предыдущей команды...")
            return

        command_text = self.cmd_entry.get().strip()
        if not command_text:
            self._append_cmd_output("Введите команду.")
            return

        self.cmd_entry.delete(0, "end")
        self._append_cmd_output(f"{self.cmd_current_dir}> {command_text}")
        self.cmd_run_button.configure(state="disabled")
        self.cmd_thread = threading.Thread(
            target=self._run_cmd_worker,
            args=(command_text,),
            daemon=True,
        )
        self.cmd_thread.start()

    def _run_cmd_worker(self, command_text: str) -> None:
        if command_text.lower().startswith("cd"):
            self._handle_cmd_cd(command_text)
            self.gui_queue.put(("cmd_done", None))
            return

        try:
            result = subprocess.run(
                ["cmd.exe", "/c", command_text],
                cwd=self.cmd_current_dir,
                capture_output=True,
                text=True,
                encoding="cp866",
                errors="replace",
            )
            stdout_text = (result.stdout or "").strip()
            stderr_text = (result.stderr or "").strip()
            if stdout_text:
                for line in stdout_text.splitlines():
                    self._queue_cmd_output(line)
            if stderr_text:
                for line in stderr_text.splitlines():
                    self._queue_cmd_output(line)
            self._queue_cmd_output(f"[exit code: {result.returncode}]")
        except Exception as exc:
            self._queue_cmd_output(f"Ошибка выполнения команды: {exc}")
        finally:
            self.gui_queue.put(("cmd_done", None))

    def _handle_cmd_cd(self, command_text: str) -> None:
        raw_target = command_text[2:].strip()
        if not raw_target:
            self._queue_cmd_output(self.cmd_current_dir)
            return

        target = raw_target.strip('"')
        if target == ".":
            self._queue_cmd_output(self.cmd_current_dir)
            return
        if target == "..":
            candidate = os.path.dirname(self.cmd_current_dir)
        elif os.path.isabs(target):
            candidate = target
        else:
            candidate = os.path.normpath(os.path.join(self.cmd_current_dir, target))

        if os.path.isdir(candidate):
            self.cmd_current_dir = candidate
            self._queue_cmd_output(f"Текущая папка изменена: {self.cmd_current_dir}")
            self.gui_queue.put(("log", f"CMD: рабочая папка изменена на {self.cmd_current_dir}"))
        else:
            self._queue_cmd_output(f"Системе не удается найти указанный путь: {candidate}")
        self.gui_queue.put(("cmd_output", "__UPDATE_DIR_LABEL__"))

    def _timestamp(self) -> str:
        return datetime.now().strftime("%H:%M:%S")

    def log_to_console(self, message: str) -> None:
        self.console_text.configure(state="normal")
        self.console_text.insert("end", f"[{self._timestamp()}] {message}\n")
        self.console_text.see("end")
        self.console_text.configure(state="disabled")

    def _queue_log(self, message: str) -> None:
        self.gui_queue.put(("log", message))

    def _process_gui_queue(self) -> None:
        while True:
            try:
                event_type, payload = self.gui_queue.get_nowait()
            except queue.Empty:
                break

            if event_type == "log":
                self.log_to_console(payload)
            elif event_type == "cmd_output":
                if payload == "__UPDATE_DIR_LABEL__":
                    self._update_cmd_dir_label()
                else:
                    self._append_cmd_output(payload)
            elif event_type == "cmd_done":
                self._on_cmd_done()
            elif event_type == "script_done":
                self._on_script_finished()
            elif event_type == "device_task_done":
                self._on_device_task_finished()

        self.after(100, self._process_gui_queue)

    def _on_script_finished(self) -> None:
        self._set_action_buttons_state("normal")
        self.script_thread = None
        self.stop_event.clear()
        self.tracked_board_objects.clear()
        self.tracked_serial_connections.clear()

    def _on_device_task_finished(self) -> None:
        self._set_action_buttons_state("normal")
        self.device_task_thread = None

    def _on_cmd_done(self) -> None:
        self.cmd_thread = None
        self.cmd_run_button.configure(state="normal")

    def _set_action_buttons_state(self, state: str) -> None:
        self.run_button.configure(state=state)
        self.erase_button.configure(state=state)
        self.flash_button.configure(state=state)

    def clear_console(self) -> None:
        self.console_text.configure(state="normal")
        self.console_text.delete("1.0", "end")
        self.console_text.configure(state="disabled")
        self.log_to_console("Console cleared.")

    def _selected_com_port_name(self) -> str:
        selected_display = self.com_var.get().strip()
        mapped_value = self.port_display_to_device.get(selected_display)
        if mapped_value:
            return mapped_value
        return selected_display.split(" ", 1)[0] if selected_display else ""

    def _sync_selected_port(self) -> str:
        self.selected_port = self._selected_com_port_name()
        return self.selected_port

    def _selected_board_profile(self) -> dict:
        return self.board_profiles.get(self.board_var.get(), BOARD_PROFILES[0])

    def _port_matches_selected_board(self, port_info) -> bool:
        profile = self._selected_board_profile()
        if not profile["keywords"] and not profile["vid_pid"]:
            return True

        port_vid = getattr(port_info, "vid", None)
        port_pid = getattr(port_info, "pid", None)
        ch340_vidpid = (0x1A86, 0x7523)
        ftdi_vidpid = (0x0403, 0x6001)
        if port_vid is not None and port_pid is not None:
            if (port_vid, port_pid) in profile["vid_pid"]:
                return True
            # USB-UART bridges (CH340/FTDI) cannot reliably identify a specific board model.
            # We only treat them as a match for UNO (common UNO clones) to avoid hiding the port.
            if profile.get("label") == "Arduino Uno":
                if (port_vid, port_pid) in {ch340_vidpid, ftdi_vidpid}:
                    return True

        searchable_text = " ".join(
            [
                str(getattr(port_info, "description", "") or ""),
                str(getattr(port_info, "manufacturer", "") or ""),
                str(getattr(port_info, "product", "") or ""),
                str(getattr(port_info, "hwid", "") or ""),
            ]
        ).lower()
        return any(keyword in searchable_text for keyword in profile["keywords"])

    def _detect_board_label_for_port(self, port_info) -> str:
        searchable_text = " ".join(
            [
                str(getattr(port_info, "description", "") or ""),
                str(getattr(port_info, "manufacturer", "") or ""),
                str(getattr(port_info, "product", "") or ""),
                str(getattr(port_info, "hwid", "") or ""),
            ]
        ).lower()
        port_vid = getattr(port_info, "vid", None)
        port_pid = getattr(port_info, "pid", None)

        ch340_vidpid = (0x1A86, 0x7523)
        ftdi_vidpid = (0x0403, 0x6001)

        if "arduino" in searchable_text and "uno" in searchable_text:
            return "Arduino Uno"
        if "arduino" in searchable_text and "nano" in searchable_text:
            return "Arduino Nano"
        if "arduino" in searchable_text and "mega" in searchable_text:
            return "Arduino Mega 2560"

        for profile in BOARD_PROFILES[1:]:
            if port_vid is not None and port_pid is not None:
                if (port_vid, port_pid) in profile["vid_pid"]:
                    return profile["label"]
            if any(keyword in searchable_text for keyword in profile["keywords"]):
                return profile["label"]

        if port_vid is not None and port_pid is not None:
            if (port_vid, port_pid) == ch340_vidpid:
                return "Arduino Uno"
            if (port_vid, port_pid) == ftdi_vidpid:
                return "Arduino Uno"

        return "Не определена"

    @staticmethod
    def _is_bluetooth_port(port_info) -> bool:
        searchable_text = " ".join(
            [
                str(getattr(port_info, "description", "") or ""),
                str(getattr(port_info, "manufacturer", "") or ""),
                str(getattr(port_info, "product", "") or ""),
                str(getattr(port_info, "hwid", "") or ""),
            ]
        ).lower()
        bt_keywords = ("bluetooth", "bth", "rfcomm", "wireless")
        return any(keyword in searchable_text for keyword in bt_keywords)

    def check_bluetooth_connection(self) -> None:
        if not self._validate_selected_port():
            return
        selected_display = self.com_var.get().strip()
        port_info = self.port_display_to_info.get(selected_display)
        if port_info and not self._is_bluetooth_port(port_info):
            self.bt_status_var.set("Bluetooth: выбранный порт не похож на BT")
            self.log_to_console("Выбранный порт не определяется как Bluetooth COM.")
            return
        self._test_serial_port_for_bt(self.selected_port)

    def _test_serial_port_for_bt(self, port_name: str) -> None:
        self.bt_check_button.configure(state="disabled")
        self.bt_status_var.set(f"Bluetooth: проверка {port_name}...")
        try:
            with serial.Serial(port=port_name, baudrate=9600, timeout=1):
                pass
            self.bt_status_var.set(f"Bluetooth: подключено ({port_name})")
            self.log_to_console(f"Bluetooth COM-порт доступен: {port_name}")
        except Exception as exc:
            self.bt_status_var.set(f"Bluetooth: нет связи ({port_name})")
            self.log_to_console(f"Bluetooth проверка не прошла для {port_name}: {exc}")
        finally:
            self.bt_check_button.configure(state="normal")

    def _validate_selected_port(self) -> bool:
        selected_display = self.com_var.get().strip()
        self._sync_selected_port()
        if not self.selected_port or selected_display.startswith("Порты не найдены"):
            self.log_to_console("ОШИБКА: Выберите корректный COM-порт перед запуском!")
            return False
        return True

    def _is_any_task_running(self) -> bool:
        script_running = self.script_thread and self.script_thread.is_alive()
        device_running = self.device_task_thread and self.device_task_thread.is_alive()
        return bool(script_running or device_running)

    def refresh_ports(self) -> None:
        detected_ports = list(list_ports.comports())
        self.port_display_to_device = {}
        self.port_display_to_info = {}
        port_labels = []
        selected_board = self._selected_board_profile()["label"]
        bluetooth_only = bool(self.bt_only_var.get()) if hasattr(self, "bt_only_var") else False

        def _safe_ui_text(text: str) -> str:
            # Remove control/unprintable characters that sometimes appear in Windows device strings.
            return "".join(ch if ch.isprintable() else " " for ch in (text or "")).strip()

        for port_info in detected_ports:
            if bluetooth_only and not self._is_bluetooth_port(port_info):
                continue
            if not self._port_matches_selected_board(port_info):
                continue
            short_name = (port_info.device or "").strip()
            description = _safe_ui_text((port_info.description or "").strip())
            board_name = self._detect_board_label_for_port(port_info)
            if description and description != "n/a":
                display_name = f"{short_name} - {description} [{board_name}]"
            else:
                display_name = f"{short_name} [{board_name}]"
            if display_name:
                self.port_display_to_device[display_name] = short_name
                self.port_display_to_info[display_name] = port_info
                port_labels.append(display_name)

        if port_labels:
            self.com_menu.configure(values=port_labels)
            self.com_var.set(port_labels[0])
            self._sync_selected_port()
            self.log_to_console(f"Обнаружены COM-порты: {', '.join(port_labels)}")
            if bluetooth_only:
                self.bt_status_var.set("Bluetooth: выберите порт и нажмите Проверить BT")
        else:
            not_found_label = f"Порты не найдены ({selected_board})"
            self.com_menu.configure(values=[not_found_label])
            self.com_var.set(not_found_label)
            self.selected_port = ""
            self.log_to_console(
                f"COM-порты не найдены для выбранной платы: {selected_board}."
            )
            if bluetooth_only:
                self.bt_status_var.set("Bluetooth: BT COM-порты не найдены")

    def run_script(self) -> None:
        if self._is_any_task_running():
            if self.stop_event.is_set():
                self.log_to_console("Ожидание полной остановки текущего скрипта...")
            else:
                self.log_to_console("Операция уже выполняется.")
            return

        script = self.editor_text.get("1.0", "end-1c")
        if not self._validate_selected_port():
            return

        com_port = self.selected_port
        robot_ip = self.ip_entry.get().strip()
        robot_port = self.port_entry.get().strip()

        self.log_to_console(f"--- Попытка запуска на {com_port} ---")
        self._set_action_buttons_state("disabled")
        self.stop_event.clear()

        self.script_thread = threading.Thread(
            target=self._execute_script_thread,
            args=(script, com_port, robot_ip, robot_port),
            daemon=True,
        )
        self.script_thread.start()

    def _execute_script_thread(
        self,
        script: str,
        com_port: str,
        robot_ip: str,
        robot_port: str,
    ) -> None:
        class ScriptStopRequested(Exception):
            pass

        class QueueWriter:
            def __init__(self, logger_callback):
                self.logger_callback = logger_callback
                self.buffer = ""

            def write(self, text):
                if not text:
                    return
                self.buffer += text
                while "\n" in self.buffer:
                    line, self.buffer = self.buffer.split("\n", 1)
                    if line.strip():
                        self.logger_callback(line)

            def flush(self):
                if self.buffer.strip():
                    self.logger_callback(self.buffer)
                self.buffer = ""

        def thread_trace(frame, event, arg):
            if self.stop_event.is_set():
                raise ScriptStopRequested("STOP requested by user")
            return thread_trace

        # Ensure the latest UI values are always injected into exec globals.
        execution_globals = {
            "__builtins__": __builtins__,
            "serial": serial,
            "COM_PORT": com_port,
            "SELECTED_COM": com_port,
            "ROBOT_IP": robot_ip,
            "ROBOT_PORT": robot_port,
            "STOP_EVENT": self.stop_event,
        }

        writer = QueueWriter(self._queue_log)
        self._queue_log("RUN SCRIPT started.")
        original_serial_class = serial.Serial

        app_self = self

        class TrackedSerial(original_serial_class):
            def __init__(self, *args, **kwargs):
                super().__init__(*args, **kwargs)
                app_self.tracked_serial_connections.add(self)

        try:
            serial.Serial = TrackedSerial
            sys.settrace(thread_trace)
            with redirect_stdout(writer), redirect_stderr(writer):
                def _is_arduino_source(source: str) -> bool:
                    return bool(re.search(r"\bvoid\s+setup\s*\(\s*\)", source))

                # Arduino emulation / hardware bridge via TrackedSerial.
                _arduino_serial_holder: dict[str, object] = {"sp": None}

                def _get_arduino_serial():
                    sp = _arduino_serial_holder.get("sp")
                    if sp is not None and getattr(sp, "is_open", False):
                        return sp
                    # COM_PORT is injected into execution_globals, but inside this closure
                    # we read it from the injected globals to satisfy type checkers.
                    port_name = execution_globals.get("COM_PORT") or execution_globals.get("SELECTED_COM")
                    sp = serial.Serial(port_name, baudrate=115200, timeout=1)
                    _arduino_serial_holder["sp"] = sp
                    return sp

                def _send_arduino_command(line: str) -> None:
                    sp = _get_arduino_serial()
                    payload = (line.rstrip("\n") + "\n").encode("utf-8", errors="replace")
                    sp.write(payload)
                    # Helpful visibility for users running Arduino-like scripts.
                    writer.write(f"[UART] {line}\n")

                def pinMode(pin, mode):
                    _send_arduino_command(f"PINMODE {pin} {mode}")

                def digitalWrite(pin, value):
                    _send_arduino_command(f"DW {pin} {value}")

                def digitalRead(pin):
                    _send_arduino_command(f"DR {pin}")
                    sp = _get_arduino_serial()
                    try:
                        resp = sp.readline().decode("utf-8", errors="replace").strip()
                        return int(resp) if resp else 0
                    except Exception:
                        return 0

                def delay(ms):
                    # Arduino delay is milliseconds.
                    time.sleep(float(ms) / 1000.0)

                class _SerialEmu:
                    def println(self, *args, sep=" ", end="\n"):
                        text = sep.join(str(a) for a in args) + end
                        writer.write(text)

                # Required globals for Arduino-like scripts.
                execution_globals.update(
                    {
                        "pinMode": pinMode,
                        "digitalRead": digitalRead,
                        "digitalWrite": digitalWrite,
                        "delay": delay,
                        "Serial": _SerialEmu(),
                        "INPUT_PULLUP": "INPUT_PULLUP",
                        "OUTPUT": "OUTPUT",
                        "HIGH": 1,
                        "LOW": 0,
                        "KY031_PIN": 2,
                        "BUZZER_PIN": 8,
                    }
                )

                if _is_arduino_source(script):
                    selected_label = str(self.board_var.get()) if hasattr(self, "board_var") else ""
                    fqbn_map = {
                        "Arduino Uno": "arduino:avr:uno",
                        "Arduino Nano": "arduino:avr:nano",
                        "Arduino Mega 2560": "arduino:avr:mega",
                    }
                    fqbn = fqbn_map.get(selected_label, "arduino:avr:uno")

                    if not shutil.which("arduino-cli"):
                        raise RuntimeError(
                            "Не найден arduino-cli. Установите Arduino CLI и добавьте в PATH, "
                            "затем повторите. (Например: winget install ArduinoSA.CLI)"
                        )

                    base_dir = os.path.dirname(os.path.abspath(__file__))
                    build_cache_dir = os.path.join(base_dir, "build_cache")
                    os.makedirs(build_cache_dir, exist_ok=True)

                    sketch_name = f"sketch_{int(time.time())}"
                    sketch_dir = os.path.join(build_cache_dir, sketch_name)
                    os.makedirs(sketch_dir, exist_ok=True)
                    sketch_path = os.path.join(sketch_dir, f"{sketch_name}.ino")
                    with open(sketch_path, "w", encoding="utf-8") as f:
                        f.write(script.replace("\r\n", "\n").replace("\r", "\n") + "\n")

                    writer.write(f"[ARDUINO] Компиляция: {fqbn}\n")
                    compile_cmd = ["arduino-cli", "compile", "--fqbn", fqbn, sketch_dir]
                    writer.write("[ARDUINO] " + " ".join(compile_cmd) + "\n")

                    def _run_cli(cmd: list[str]) -> subprocess.CompletedProcess:
                        env = os.environ.copy()
                        # Force UTF-8 output from arduino-cli to avoid mojibake on Windows.
                        env["LANG"] = "C.UTF-8"
                        env["LC_ALL"] = "C.UTF-8"
                        return subprocess.run(
                            cmd,
                            capture_output=True,
                            text=True,
                            encoding="utf-8",
                            errors="replace",
                            env=env,
                        )

                    compile_res = _run_cli(compile_cmd)
                    if compile_res.stdout:
                        writer.write(compile_res.stdout + "\n")
                    if compile_res.stderr:
                        for line in compile_res.stderr.rstrip().splitlines():
                            self._queue_log(line)
                    if compile_res.returncode != 0:
                        core_list_res = _run_cli(["arduino-cli", "core", "list"])
                        core_list_text = f"{core_list_res.stdout}\n{core_list_res.stderr}".lower()
                        if "arduino:avr" not in core_list_text:
                            self._queue_log("Платформа arduino:avr не установлена. Устанавливаю автоматически...")
                            install_cmd = ["arduino-cli", "core", "install", "arduino:avr"]
                            writer.write("[ARDUINO] " + " ".join(install_cmd) + "\n")
                            install_res = _run_cli(install_cmd)
                            if install_res.stdout:
                                writer.write(install_res.stdout + "\n")
                            if install_res.stderr:
                                for line in install_res.stderr.rstrip().splitlines():
                                    self._queue_log(line)
                            if install_res.returncode == 0:
                                self._queue_log("arduino:avr установлен. Повторяю компиляцию...")
                                compile_res = _run_cli(compile_cmd)
                                if compile_res.stdout:
                                    writer.write(compile_res.stdout + "\n")
                                if compile_res.stderr:
                                    for line in compile_res.stderr.rstrip().splitlines():
                                        self._queue_log(line)
                    if compile_res.returncode != 0:
                        raise RuntimeError(f"Компиляция не удалась (code={compile_res.returncode}).")

                    writer.write(f"[ARDUINO] Загрузка в {com_port}\n")
                    upload_cmd = ["arduino-cli", "upload", "-p", com_port, "--fqbn", fqbn, sketch_dir]
                    writer.write("[ARDUINO] " + " ".join(upload_cmd) + "\n")
                    upload_res = _run_cli(upload_cmd)
                    if upload_res.stdout:
                        writer.write(upload_res.stdout + "\n")
                    if upload_res.stderr:
                        for line in upload_res.stderr.rstrip().splitlines():
                            self._queue_log(line)
                    if upload_res.returncode != 0:
                        raise RuntimeError(f"Загрузка не удалась (code={upload_res.returncode}).")

                    writer.write("[ARDUINO] Готово. Скетч запущен на плате.\n")
                    return
                exec(script, execution_globals)
        except ScriptStopRequested:
            writer.flush()
            self._queue_log("Скрипт остановлен пользователем.")
        except Exception:
            error_text = traceback.format_exc()
            writer.flush()
            self._queue_log("Execution failed with traceback:")
            for line in error_text.rstrip().splitlines():
                self._queue_log(line)
        finally:
            sys.settrace(None)
            self._track_board_like_objects(execution_globals)
            serial.Serial = original_serial_class
            writer.flush()
            self._queue_log("RUN SCRIPT finished.")
            self.gui_queue.put(("script_done", None))

    def erase_device_flash(self) -> None:
        if self._is_any_task_running():
            self.log_to_console("Операция уже выполняется.")
            return
        if not self._validate_selected_port():
            return

        self._set_action_buttons_state("disabled")
        self.log_to_console(f"--- Очистка памяти ESP32 на {self.selected_port} ---")
        self.device_task_thread = threading.Thread(
            target=self._erase_flash_worker,
            daemon=True,
        )
        self.device_task_thread.start()

    def _erase_flash_worker(self) -> None:
        writer = self._build_queue_writer()
        try:
            with redirect_stdout(writer), redirect_stderr(writer):
                esptool.main(["--chip", "esp32", "--port", self.selected_port, "erase_flash"])
            writer.flush()
            self._queue_log("Очистка памяти завершена.")
        except SystemExit as exc:
            writer.flush()
            self._queue_log(f"esptool завершен с кодом: {exc}")
        except Exception as exc:
            writer.flush()
            self._queue_log(f"ОШИБКА erase_flash: {exc}")
            self._queue_log("Проверьте порт, кабель и режим загрузчика ESP32.")
        finally:
            self.gui_queue.put(("device_task_done", None))

    def flash_device_firmware(self, firmware_path: str) -> None:
        if self._is_any_task_running():
            self.log_to_console("Операция уже выполняется.")
            return
        if not self._validate_selected_port():
            return
        if not firmware_path:
            self.log_to_console("ОШИБКА: Не выбран файл прошивки .bin")
            return

        self._set_action_buttons_state("disabled")
        self.log_to_console(f"--- Прошивка ESP32 на {self.selected_port} ---")
        self.log_to_console(f"Файл: {firmware_path}")
        self.device_task_thread = threading.Thread(
            target=self._flash_firmware_worker,
            args=(firmware_path,),
            daemon=True,
        )
        self.device_task_thread.start()

    def _flash_firmware_worker(self, firmware_path: str) -> None:
        writer = self._build_queue_writer()
        try:
            with redirect_stdout(writer), redirect_stderr(writer):
                esptool.main(
                    [
                        "--chip",
                        "esp32",
                        "--port",
                        self.selected_port,
                        "--baud",
                        "460800",
                        "write_flash",
                        "--flash_mode",
                        "dio",
                        "0x1000",
                        firmware_path,
                    ]
                )
            writer.flush()
            self._queue_log("Прошивка завершена.")
        except SystemExit as exc:
            writer.flush()
            self._queue_log(f"esptool завершен с кодом: {exc}")
        except Exception as exc:
            writer.flush()
            self._queue_log(f"ОШИБКА прошивки: {exc}")
            self._queue_log("Проверьте, что порт свободен и ESP32 в bootloader mode.")
        finally:
            self.gui_queue.put(("device_task_done", None))

    def _select_and_flash_firmware(self) -> None:
        firmware_path = filedialog.askopenfilename(
            title="Выберите .bin файл прошивки",
            filetypes=[("BIN files", "*.bin"), ("All files", "*.*")],
        )
        if firmware_path:
            self.flash_device_firmware(firmware_path)
        else:
            self.log_to_console("Выбор файла прошивки отменен.")

    def _build_queue_writer(self):
        class QueueWriter:
            def __init__(self, logger_callback):
                self.logger_callback = logger_callback
                self.buffer = ""

            def write(self, text):
                if not text:
                    return
                self.buffer += text
                while "\n" in self.buffer:
                    line, self.buffer = self.buffer.split("\n", 1)
                    if line.strip():
                        self.logger_callback(line)

            def flush(self):
                if self.buffer.strip():
                    self.logger_callback(self.buffer.strip())
                self.buffer = ""

        return QueueWriter(self._queue_log)

    def _track_board_like_objects(self, namespace: dict) -> None:
        for value in namespace.values():
            if self._is_board_like_object(value):
                self.tracked_board_objects.add(value)

    @staticmethod
    def _is_board_like_object(obj) -> bool:
        if obj is None:
            return False
        return hasattr(obj, "exit") and hasattr(obj, "sp")

    def _close_board_like_objects(self) -> int:
        closed_boards = 0

        for board in list(self.tracked_board_objects):
            try:
                board.exit()
                closed_boards += 1
            except Exception:
                continue

        # Fallback: scan GC for board-like objects that were not tracked.
        try:
            for obj in gc.get_objects():
                if self._is_board_like_object(obj):
                    try:
                        obj.exit()
                        closed_boards += 1
                    except Exception:
                        continue
        except Exception:
            pass

        self.tracked_board_objects.clear()
        return closed_boards

    def emergency_stop(self) -> None:
        self.log_to_console("STOP COMMAND SENT")
        self.stop_event.set()
        # Keep action buttons in stable state while stop cleanup is in progress.
        closed_boards = self._close_board_like_objects()
        closed_connections = 0

        for connection in list(self.tracked_serial_connections):
            try:
                if getattr(connection, "is_open", False):
                    connection.close()
                    closed_connections += 1
            except Exception:
                continue

        self.tracked_serial_connections.clear()

        try:
            for obj in gc.get_objects():
                if isinstance(obj, serial.Serial):
                    try:
                        if getattr(obj, "is_open", False):
                            obj.close()
                            closed_connections += 1
                    except Exception:
                        continue
        except Exception:
            pass

        self.log_to_console(f"Закрыто board-соединений: {closed_boards}")
        self.log_to_console(f"Закрыто serial-соединений: {closed_connections}")
        if self.script_thread and self.script_thread.is_alive():
            self.log_to_console("Ожидание остановки скрипта после закрытия соединений...")
        else:
            self.script_thread = None
            self.stop_event.clear()
            self._set_action_buttons_state("normal")


if __name__ == "__main__":
    app = RobotControlApp()
    app.mainloop()
