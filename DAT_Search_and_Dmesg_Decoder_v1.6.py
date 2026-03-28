import os
import re
import time
import queue
import bisect
import threading
import traceback
import tkinter as tk
import tkinter.font as tkfont
from datetime import datetime
from screeninfo import get_monitors
from tkinter import filedialog, messagebox, ttk


class ListboxTooltip:
    # Lightweight tooltip helper for a Listbox (shows full path).

    def __init__(self, widget, get_text_callback, delay: int = 500):
        self.widget = widget
        self.get_text_callback = get_text_callback
        self.delay = delay
        self.tooltip = None
        self.after_id = None

        # Bind motion/leave to schedule and hide tooltips
        self.widget.bind("<Motion>", self.schedule_tooltip)
        self.widget.bind("<Leave>", self.hide_tooltip)

    def schedule_tooltip(self, event):
        # Schedule the tooltip after the configured delay.
        self.hide_tooltip()
        index = self.widget.nearest(event.y)
        if index >= 0:
            text = self.get_text_callback(index)
            self.after_id = self.widget.after(self.delay, lambda: self.show_tooltip(event.x_root, event.y_root, text))

    def show_tooltip(self, x, y, text):
        # Show a small top-level window near the cursor with the text.
        self.hide_tooltip()
        self.tooltip = tk.Toplevel(self.widget)
        self.tooltip.wm_overrideredirect(True)
        self.tooltip.wm_geometry(f"+{x+10}+{y+10}")
        label = tk.Label(
            self.tooltip,
            text=text,
            background="#ffffe0",
            relief="solid",
            borderwidth=1,
            font=("Lucida Console", 9)
        )
        label.pack()

    def hide_tooltip(self, event=None):
        # Hide tooltip and cancel scheduled display.
        if self.after_id:
            self.widget.after_cancel(self.after_id)
            self.after_id = None
        if self.tooltip:
            self.tooltip.destroy()
            self.tooltip = None

class TextSearchApp:
    # Main application class encapsulating UI, search, and theming.
    # ------------ Initialization & UI thread coordination ------------
    # -------------------- Initialization --------------------
    def __init__(self, root):
        self.ui_queue = queue.Queue()
        # Tracks whether a background operation has programmatically modified the Results tab.
        # Used to reset the undo stack after the operation completes (so Ctrl+Z will not erase bulk output).
        self._results_bulk_dirty = False
        self._results_bulk_widget = None

        self._ui_poller_id = None
        self._progress_target = 0
        self._progress_anim_id = None

        self.root = root
        self.root.title("DAT File Search Tool")

        # --- Runtime state (selection, matches, debouncer, versioning) ---
        self.file_paths = []                 # Full paths of selected files
        # Cache file sizes to keep UI updates fast
        self._file_size_cache = {}  # path -> size_bytes
        self._last_print_total_bytes = 0  # last printed selection size
        # Safety limits for loading content into the Text widget (bytes)
        self.SOFT_LIMIT_BYTES = 800 * 1024 * 1024   # 800 MiB
        self.HARD_LIMIT_BYTES = 1100 * 1024 * 1024  # 1.1 GiB
        # Listbox visible rows (UI preference)
        self.LISTBOX_VISIBLE_ROWS = 10
        # Shared tooltip delay (ms) for listbox rows and workspace tabs
        self.TOOLTIP_DELAY_MS = 500
        # Listbox Width ratio (percentage)
        self.LISTBOX_WITDH_RATIO = 0.33
        # Occurrence highlight window for double-click token selection (lines before/after caret)
        self.OCCURRENCE_WINDOW_LINES = 2000  # tune as needed
        # When True, only whole-token matches are highlighted (no substring matches)
        self.OCCURRENCE_WHOLE_TOKEN_ONLY = False
        # Occurrence highlighting from selection: max selection length to consider (prevents heavy scans)
        self.OCCURRENCE_SUBSTRING_MAX_CHARS = 128
        # Debounce for selection-change-driven occurrence highlights (ms)
        self._occ_sel_debounce_ms = 80
        self._occ_sel_after_id = None
        self.matches = []                    # Aggregated matches for export / display

        # Unified search cancellation token (thread-safe)
        self.search_active = threading.Event()
        self.search_thread = None            # Worker for file/Results tab searches

        # Debouncer / highlight batch state
        self._debounce_id = None
        self._debounce_delay = 100           # Standardized to 100 ms
        self._highlight_running = False
        self._highlight_gen = 0

        # Content versioning for highlight validity
        self._content_version = 0            # Increments on any content replacement
        self._matches_version = None         # Version tag for precomputed matches

        # Developer flag for console logging (instrumentation)
        # Set environment variable DAT_SEARCH_TOOL_DEBUG=1 to enable.
        self.DEBUG_HIGHLIGHT = bool(os.getenv('DAT_SEARCH_TOOL_DEBUG'))

        # Theme flag and palette
        self.dark_mode = False
        self.THEMES = {
            "light": {
                "bg": "SystemButtonFace",
                "fg": "black",
                "text_bg": "white",
                "text_fg": "black",
                "log_bg": "#6d6891",
                "log_fg": "white",
                "insert": "black",
                "listbox_select_bg": "#6d6891",
                "listbox_select_fg": "white",
                "findall_bg": "#fffd7a",
                "findnext_bg": "#b7f7b0",
                "occurrence_bg": "#083fa6",
                "occurrence_fg": "white",
                "file_header_bg": "#008080",
                "file_header_fg": "white",
                "text_header_bg": "#6f8faf",
                "text_header_fg": "white",
                "progress_bg": "green",
                "progress_trough": "lightgray",
            },
            "dark": {
                "bg": "#2e2e2e",
                "fg": "#e6e6e6",
                "text_bg": "#1f1f1f",
                "text_fg": "#f2f2f2",
                "log_bg": "#3b3b3b",
                "log_fg": "#e6e6e6",
                "insert": "#f2f2f2",
                "listbox_select_bg": "#4a4a7a",
                "listbox_select_fg": "#ffffff",
                "findall_bg": "#464000",
                "findnext_bg": "#2b5f2b",
                "occurrence_bg": "#083fa6",
                "occurrence_fg": "white",
                "file_header_bg": "#005f5f",
                "file_header_fg": "#ffffff",
                "text_header_bg": "#335a80",
                "text_header_fg": "#ffffff",
                "progress_bg": "#3cb371",
                "progress_trough": "#555555",
            },
        }

        # Max non-Results tabs; total = 1 (Results) + MAX_WORK_TABS
        self.MAX_WORK_TABS = 12  # configurable
        self._tab_counter = 0
        self._tabs = {}          # tab_id -> state dict
        self._file_to_tab = {}   # normpath -> tab_id
        self._results_tab_id = None
        # ---- Build UI, configure tags, apply theme, add menus/shortcuts ----
        self.create_widgets()
        try:
            self.root.after(0, lambda: self._update_clear_results_button_state(force=True))
        except Exception as e:
            self._swallow(e)
        try:
            self.root.after(0, self._update_tabs_open_label)
        except Exception as e:
            self._swallow(e)
        try:
            self._workspace_select_results()
            self._on_workspace_tab_changed()
        except Exception as e:
            self._swallow(e)
        self._configure_tags()
        self._apply_theme()
        self.create_menu()
        self._install_workspace_tab_context_menu()
        self.bind_shortcuts()
        self.bind_highlight_events_once()
        # Custom double-click token selection + triple-click line selection
        self._install_custom_word_selection()
        # Re-bind occurrence clear events after installing all key bindings (prevents later binds from overriding)
        try:
            self._bind_occurrence_clear_events()
        except Exception as e:
            self._swallow(e)
        # Text-area context menu (Cut/Copy/Paste + Undo/Redo + Highlight tools)
        self._install_text_area_context_menu()
        # Ctrl+Z undo and Ctrl+Shift+Z redo (keep last 10 edits)
        self._install_undo_redo_bindings()
        # Status bar + line-number gutter updates
        self._install_status_and_linenum_bindings()

        # Close protocol
        self.root.protocol("WM_DELETE_WINDOW", self.on_close)


    def _ui_poller(self):
        # Process queued UI actions from worker threads (runs in main thread).
        try:
            results_text = None
            try:
                if getattr(self, "_results_tab_id", None):
                    results_text = self._tabs.get(self._results_tab_id, {}).get("text")
            except Exception:
                results_text = None
            needs_clear_results_state_refresh = False
            while True:
                action = self.ui_queue.get_nowait()
                kind = action[0]

                if kind == "log":
                    _, msg = action
                    self.log_message(msg)

                elif kind == "progress":
                    _, value = action
                    try:
                        self._set_progress_target(value)
                    except Exception:
                        try:
                            self.progress['value'] = value
                            self.progress.update_idletasks()
                        except Exception as e:
                            self._swallow(e)
                elif kind == "progress_instant":
                    _, value = action
                    try:
                        self._snap_progress(value)
                    except Exception as e:
                        self._swallow(e)
                elif kind == "progress_delay":
                    # Schedule an instant progress snap after a small delay (avoids rollback animation and allows UI paint before modal dialogs).
                    # Action: ("progress_delay", delay_ms, value)
                    _, delay_ms, value = action
                    try:
                        d = int(delay_ms)
                    except Exception:
                        d = 0
                    try:
                        self.root.after(max(0, d), lambda v=value: self._snap_progress(v))
                    except Exception as e:
                        self._swallow(e)
                elif kind == "msgbox_info_delay":
                    # Show an info messagebox after a delay (prevents blocking the UI poller before progress/cursor updates are applied).
                    # Action: ("msgbox_info_delay", delay_ms, title, msg)
                    _, delay_ms, title, msg = action
                    try:
                        d = int(delay_ms)
                    except Exception:
                        d = 0
                    try:
                        self.root.after(max(0, d), lambda t=title, m=msg: self._mb_showinfo(t, m))
                    except Exception as e:
                        self._swallow(e)

                elif kind == "cursor":
                    _, cur = action
                    try:
                        self.root.configure(cursor=cur)
                        self.root.update_idletasks()
                    except Exception as e:
                        self._swallow(e)
                elif kind == "rcv_btn":
                    _, state = action
                    try:
                        if hasattr(self, 'rcv_search_btn') and self.rcv_search_btn:
                            self.rcv_search_btn.config(state=state)
                            self.root.update_idletasks()
                    except Exception as e:
                        self._swallow(e)
                elif kind == "msgbox_error":
                    _, title, msg = action
                    self._mb_showerror(title, msg)

                elif kind == "msgbox_warning":
                    _, title, msg = action
                    self._mb_showwarning(title, msg)

                elif kind == "msgbox_info":
                    _, title, msg = action
                    self._mb_showinfo(title, msg)

                elif kind == "highlight_request":
                    _, search_term, use_regex, flags = action
                    # This runs on UI thread, so it's safe:
                    all_text = self.result_box.get("1.0", "end")
                    self.highlight_all_matches(search_term, all_text, use_regex, flags)

                elif kind == "clear_results":

                    needs_clear_results_state_refresh = True
                    # Safe lifecycle if you are replacing content
                    _w_clear = (results_text if isinstance(results_text, tk.Text) else self.result_box)
                    self.begin_content_update(widget=_w_clear)
                    try:
                        (results_text if isinstance(results_text, tk.Text) else self.result_box).delete("1.0", "end")
                    except Exception as e:
                        self._swallow(e)
                    self.end_content_update(widget=_w_clear)                    # Baseline undo after bulk clear via UI queue
                    self._reset_undo_baseline(widget=_w_clear, modified=False)


                    # Mark Results as modified by a bulk/background operation; baseline undo on completion.
                    try:
                        self._results_bulk_dirty = True
                        self._results_bulk_widget = _w_clear
                    except Exception as e:
                        self._swallow(e)
                elif kind == "focus_results":
                    # Switch UI to Results tab and focus the Results text widget
                    try:
                        self._workspace_select_results()
                        try:
                            self._on_workspace_tab_changed()
                        except Exception as e:
                            self._swallow(e)
                        try:
                            if results_text is not None:
                                results_text.focus_set()
                        except Exception as e:
                            self._swallow(e)
                    except Exception as e:
                        self._swallow(e)
                elif kind == "append_text":
                    needs_clear_results_state_refresh = True
                    _, text, tag = action
                    if tag:
                        (results_text if isinstance(results_text, tk.Text) else self.result_box).insert("end", text, (tag,))
                    else:
                        (results_text if isinstance(results_text, tk.Text) else self.result_box).insert("end", text)

                    # Mark Results as modified by a bulk/background operation; baseline undo on completion.
                    try:
                        self._results_bulk_dirty = True
                        self._results_bulk_widget = (results_text if isinstance(results_text, tk.Text) else self.result_box)
                    except Exception as e:
                        self._swallow(e)
                elif kind == "set_match_count":
                    _, count = action
                    self._update_match_count(count)

                elif kind == "add_file":
                    _, file_path = action
                    try:
                        norm = os.path.normpath(file_path)
                        existing = [os.path.normpath(p) for p in self.file_paths]
                        if norm not in existing:
                            self.file_paths.append(file_path)
                            self.file_listbox.insert(tk.END, self._format_listbox_item(file_path))
                            self.file_listbox.selection_clear(0, tk.END)
                            last = self.file_listbox.size() - 1
                            if last >= 0:
                                self.file_listbox.selection_set(last)
                                self.file_listbox.see(last)
                            self.update_selection_label()
                    except Exception as e:
                        self.log_message(f"Failed to add output file to list: {type(e).__name__}: {e}")

                elif kind == "decode_done":
                    # Decode worker indicates completion.
                    # Action may be: ("decode_done", total_seconds, total_files, ok_files)
                    dt_total = None
                    total_files = None
                    ok_files = None

                    try:
                        if len(action) >= 2:
                            dt_total = float(action[1])

                        if len(action) >= 3:
                            total_files = int(action[2])

                        if len(action) >= 4:
                            ok_files = int(action[3])

                    except Exception:
                        dt_total = None
                        total_files = None
                        ok_files = None

                    if dt_total is not None and total_files is not None and ok_files is not None:
                        self.log_message(f"Decode completed. Files: {ok_files}/{total_files}. Total time: {dt_total:,.2f} s")

                    elif dt_total is not None:
                        self.log_message(f"Decode completed in {dt_total:,.2f} s")

                    else:
                        self.log_message("Decode completed.")

                    # Progress-bar UX: avoid animated rollback.
                    # Snap to 100% (in case last update was <100) then quickly reset to 0%.

                    try:
                        self._snap_progress(100)

                    except Exception as e:
                        self._swallow(e)
                    try:
                        # Small delay so the UI can paint the 100% state.
                        self.root.after(25, lambda: self._snap_progress(0))

                    except Exception:
                        try:
                            self._snap_progress(0)

                        except Exception as e:
                            self._swallow(e)
                elif kind == "done":
                    # Worker indicates normal completion
                    self.log_message("Search completed.")
                    # If this operation wrote to Results (Find in Files / Filter Matches / RCV / etc.),
                    # treat that bulk output as baseline so Ctrl+Z only affects subsequent user edits.
                    try:
                        if getattr(self, "_results_bulk_dirty", False):
                            w_bulk = getattr(self, "_results_bulk_widget", None)
                            if w_bulk is None:
                                w_bulk = (results_text if isinstance(results_text, tk.Text) else self.result_box)
                            self._reset_undo_baseline(widget=w_bulk, modified=False)
                            self._results_bulk_dirty = False
                            self._results_bulk_widget = None
                    except Exception as e:
                        self._swallow(e)
                    try:
                        self.root.configure(cursor="")
                    except Exception as e:
                        self._swallow(e) # Delay progress reset so the user can see the final value
                    try:
                        self.root.after(600, lambda: self._snap_progress(0))
                    except Exception:
                        try:
                            self._snap_progress(0)
                        except Exception as e:
                            self._swallow(e)
                elif kind == "cancelled":
                    # If partial Results output was produced before cancellation, baseline undo now.
                    try:
                        if getattr(self, "_results_bulk_dirty", False):
                            w_bulk = getattr(self, "_results_bulk_widget", None)
                            if w_bulk is None:
                                w_bulk = (results_text if isinstance(results_text, tk.Text) else self.result_box)
                            self._reset_undo_baseline(widget=w_bulk, modified=False)
                            self._results_bulk_dirty = False
                            self._results_bulk_widget = None
                    except Exception as e:
                        self._swallow(e)
                    # action can be ("cancelled",) or ("cancelled", detailed_already_logged)
                    detailed_already_logged = False
                    if len(action) >= 2:
                        detailed_already_logged = bool(action[1])
                    try:
                        self.root.configure(cursor="")
                    except Exception as e:
                        self._swallow(e)
                    if not detailed_already_logged:
                        self.log_message("Search cancelled.")
                    # Delay progress reset a bit so any recent progress is visible

                    try:
                        self.root.after(200, lambda: self._snap_progress(0))
                    except Exception:
                        try:
                            self._snap_progress(0)
                        except Exception as e:
                            self._swallow(e)
        except queue.Empty:
            pass


            # Update Clear Results UI state once per UI-drain (cheap)
            try:
                if needs_clear_results_state_refresh:
                    self._update_clear_results_button_state()
            except Exception as e:
                self._swallow(e)
        # Keep polling while a thread is alive OR there is still queued UI work
        rcv_alive = bool(getattr(self, "_rcv_thread", None) and self._rcv_thread.is_alive())
        search_alive = bool(self.search_thread and self.search_thread.is_alive())
        decode_alive = bool(getattr(self, '_decode_thread', None) and self._decode_thread.is_alive())

        if search_alive or rcv_alive or decode_alive or (not self.ui_queue.empty()):
            self._ui_poller_id = self.root.after(50, self._ui_poller)
        else:
            self._ui_poller_id = None
    def _set_progress_target(self, value):
        """Set a progress target (0..100).

        The UI animates smoothly toward this target so progress doesn't appear to jump
        when worker threads enqueue updates faster than the UI can repaint.
        """
        try:
            v = float(value)
        except Exception:
            v = 0.0
        v = 0.0 if v < 0 else (100.0 if v > 100 else v)
        self._progress_target = v
        if self._progress_anim_id is None:
            try:
                self._progress_anim_id = self.root.after(15, self._progress_anim_tick)
            except Exception:
                self._progress_anim_id = None

    def _progress_anim_tick(self):
        """Animate progress bar toward _progress_target in small steps."""
        # Mark as not scheduled; we will reschedule if needed
        self._progress_anim_id = None
        try:
            cur = float(self.progress['value'])
        except Exception:
            cur = 0.0
        try:
            tgt = float(getattr(self, '_progress_target', 0.0) or 0.0)
        except Exception:
            tgt = 0.0
        gap = tgt - cur
        if abs(gap) < 0.1:
            try:
                self.progress['value'] = tgt
                self.progress.update_idletasks()
            except Exception as e:
                self._swallow(e)
            return
        step = max(0.5, min(2.5, abs(gap) * 0.25))
        new_val = cur + step if gap > 0 else cur - step
        if (gap > 0 and new_val > tgt) or (gap < 0 and new_val < tgt):
            new_val = tgt
        try:
            self.progress['value'] = new_val
            self.progress.update_idletasks()
        except Exception as e:
            self._swallow(e)
        try:
            self._progress_anim_id = self.root.after(15, self._progress_anim_tick)
        except Exception:
            self._progress_anim_id = None

    # ------------ UI setup & theming ------------
    def _snap_progress(self, value: float):
        """Snap progress bar to value immediately (no animation rollback). UI-thread only."""
        try:
            v = float(value)
        except Exception:
            v = 0.0
        v = 0.0 if v < 0 else (100.0 if v > 100 else v)
        try:
            if getattr(self, '_progress_anim_id', None) is not None:
                try:
                    self.root.after_cancel(self._progress_anim_id)
                except Exception as e:
                    self._swallow(e)
                self._progress_anim_id = None
        except Exception as e:
            self._swallow(e)
        try:
            self._progress_target = v
        except Exception as e:
            self._swallow(e)
        try:
            self.progress['value'] = v
            self.progress.update_idletasks()
        except Exception as e:
            self._swallow(e)

    def create_widgets(self):
        # Create all widgets and set geometry.
        # This method is only about layout; styling goes to _configure_tags() / _apply_theme().
        # Master container frame
        self.main_frame = tk.Frame(self.root)
        self.main_frame.pack(fill="both", expand=True)

        # Top frame (listbox + controls)
        self.top_frame = tk.Frame(self.main_frame)
        self.top_frame.pack(fill=tk.X, padx=10, pady=10)
        # Fix listbox area to ~1/4 of the current window width (keeps UI stable)
        try:
            self.root.update_idletasks()
        except Exception as e:
            self._swallow(e)
        try:
            _win_w = int(self.root.winfo_width() or 0)
        except Exception:
            _win_w = 0
        if _win_w <= 0:
            try:
                _win_w = int(self.root.winfo_screenwidth())
            except Exception:
                _win_w = 1200
        self._lb_fixed_px = int(max(260, _win_w * self.LISTBOX_WITDH_RATIO))

        # Left: listbox + scrollbar
        self.lb_frame = tk.Frame(self.top_frame)
        self.lb_frame.configure(width=getattr(self, "_lb_fixed_px", 320))
        self.lb_frame.pack_propagate(False)
        self.lb_frame.pack(side='left', fill='y')

        self.file_listbox = tk.Listbox(
            self.lb_frame,
            selectmode='extended',
            height= self.LISTBOX_VISIBLE_ROWS,
            width=40,
            exportselection=False,
        )
        self.file_listbox.pack(side='left', fill='both', expand=True, padx=(0, 5), pady=5)
        # Use monospace font so the name/size columns align nicely
        self._lb_font = ('Lucida Console', 10)
        try:
            self.file_listbox.configure(font=self._lb_font)
        except Exception as e:
            self._swallow(e)
        # Ensure listbox shows the requested number of rows even when lb_frame uses pack_propagate(False)
        try:
            fnt = tkfont.Font(font=self._lb_font)
            row_height = int(fnt.metrics('linespace') or 14)
            desired = int(getattr(self, 'LISTBOX_VISIBLE_ROWS', 10) or 10)
            # padding from pack(pady=5) plus a little slack for borders
            pad_y = 10
            extra = 10
            frame_height = int(row_height * desired + pad_y + extra)
            self.lb_frame.configure(height=frame_height)
        except Exception as e:
            self._swallow(e)
        # Bind selection changes to keep labels fresh
        self.file_listbox.bind('<<ListboxSelect>>', self.update_selection_label)
        # Extra multi-select shortcuts (Shift+PgUp/PgDn/Home/End)
        self.file_listbox.bind('<Shift-Prior>', self._on_lb_shift_pageup)
        self.file_listbox.bind('<Shift-Next>', self._on_lb_shift_pagedown)
        self.file_listbox.bind('<Shift-Home>', self._on_lb_shift_home)
        self.file_listbox.bind('<Shift-End>', self._on_lb_shift_end)
        # Double-click to print selected file(s)
        self.file_listbox.bind('<Double-Button-1>', self._on_file_listbox_double_click)

        # Tooltip to show full path when hovering over a row
        self.file_tooltip = ListboxTooltip(
            self.file_listbox,
            lambda i: self.file_paths[i],
            delay=500,
        )

        # Context menu (right-click on listbox)
        self.create_context_menu()

        lb_scroll = tk.Scrollbar(self.lb_frame, orient='vertical', command=self.file_listbox.yview, width=25)
        lb_scroll.pack(side='left', fill='y', pady=5)
        self.file_listbox.config(yscrollcommand=lb_scroll.set)

        # Right: controls (buttons + counters)
        self.ctrl_frame = tk.Frame(self.top_frame)
        self.ctrl_frame.pack(side='left', fill='y', padx=(10, 0), pady=5)
        # Spacer to keep controls near the listbox (prevents them from sticking to the far-right)
        self._top_spacer = tk.Frame(self.top_frame)
        self._top_spacer.pack(side='left', fill='both', expand=True)

        # Layout: 3 rows x 2 cols (buttons | counters)
        self.ctrl_frame.grid_columnconfigure(0, weight=0)
        self.ctrl_frame.grid_columnconfigure(1, weight=0)

        # Buttons (left column)
        self.toggle_button = tk.Button(self.ctrl_frame, text='Select All', command=self.toggle_selection)
        self.toggle_button.grid(row=0, column=0, sticky='ew', padx=6, pady=4)

        self.contents_button = tk.Button(self.ctrl_frame, text='Print Contents', command=self.print_file_contents)
        self.contents_button.grid(row=1, column=0, sticky='ew', padx=6, pady=4)

        self.clear_button = tk.Button(self.ctrl_frame, text='Clear Results Tab', command=self.clear_text_area, state='disabled')
        self.clear_button.grid(row=2, column=0, sticky='ew', padx=6, pady=4)

        # Phase 6: Close all Tabs button (below Clear Results Tab)
        self.close_all_tabs_btn = tk.Button(self.ctrl_frame, text='Close all Tabs', command=self._close_all_tabs_button_clicked)
        self.close_all_tabs_btn.grid(row=3, column=0, sticky='ew', padx=6, pady=4)
        # Tabs open counter (non-Results tabs; pinned tabs included)
        self.tabs_open_var = tk.StringVar(value='Tabs open: 0')
        self.tabs_open_label = tk.Label(self.ctrl_frame, textvariable=self.tabs_open_var, anchor='w')
        self.tabs_open_label.grid(row=3, column=1, sticky='w', padx=6, pady=4)


        # Counters (right column)
        self.selection_label = tk.Label(self.ctrl_frame, text='Selected files: 0', anchor='w')
        self.selection_label.grid(row=0, column=1, sticky='w', padx=6, pady=4)

        self.size_label = tk.Label(self.ctrl_frame, text='File(s) Size: 0 B', anchor='w')
        self.size_label.grid(row=1, column=1, sticky='w', padx=6, pady=4)

        self.count_label = tk.Label(self.ctrl_frame, text='Matches: 0', anchor='w')
        self.count_label.grid(row=2, column=1, sticky='w', padx=6, pady=4)

        # Progress bar (thin style)
        style = ttk.Style()
        style.theme_use('default')
        style.configure(
            "Thin.Horizontal.TProgressbar",
            troughcolor=self.THEMES['light']['progress_trough'],
            background=self.THEMES['light']['progress_bg'],
            thickness=6
        )
        progress_frame = tk.Frame(self.main_frame)
        progress_frame.pack(fill="x", padx=10, pady=(0, 0))
        self.progress = ttk.Progressbar(
            progress_frame,
            orient="horizontal",
            mode="determinate",
            style="Thin.Horizontal.TProgressbar"
        )
        self.progress.pack(fill="x", expand=True)

        # Paned container (results + log)
        paned = tk.PanedWindow(self.main_frame, orient=tk.VERTICAL)
        paned.pack(fill="both", expand=True)

        # Results pane

        # Results pane (tabbed workspace)
        self.result_frame = tk.Frame(paned)

        # Workspace notebook (Results tab is fixed)
        self.workspace = ttk.Notebook(self.result_frame)
        self.workspace.pack(fill='both', expand=True)

        # Phase 6: enable closable tabs (X)
        try:
            self._init_workspace_notebook_close_style()
            self._bind_workspace_notebook_close_events()
        except Exception as e:
            self._swallow(e)
        # Create fixed Results tab
        results_frame = tk.Frame(self.workspace)
        self.workspace.add(results_frame, text='Results')
        self._results_tab_id = self.workspace.tabs()[-1]
        try:
            self.workspace.tab(self._results_tab_id, image='', compound='none')
        except Exception as e:
            self._swallow(e)
        try:
            self._ensure_closable_tab_styles()
        except Exception as e:
            self._swallow(e)
        try:
            self.workspace.tab(self._results_tab_id, style='TNotebook.Tab')
        except Exception as e:
            self._swallow(e)
        # Build the Results editor widgets inside results_frame
        self.result_inner = tk.Frame(results_frame)
        self.result_inner.pack(fill='both', expand=True)

        self.line_numbers = tk.Text(self.result_inner, width=4, padx=4, takefocus=0, borderwidth=0, relief='flat', wrap='none')
        self.line_numbers.pack(side='left', fill='y')
        self.line_numbers.config(state='disabled')

        self.result_box = tk.Text(self.result_inner, wrap='none', undo=True, maxundo=10, autoseparators=True)
        # Use a consistent monospace font for the Text area and the line-number gutter
        self._mono_font = ("Lucida Console", 10)
        try:
            self.result_box.configure(font=self._mono_font)
        except Exception as e:
            self._swallow(e)
        try:
            self.line_numbers.configure(font=self._mono_font)
        except Exception as e:
            self._swallow(e)
        self.result_box.pack(side='left', fill='both', expand=True)

        try:
            self._install_results_clear_button_monitoring()
        except Exception as e:
            self._swallow(e)
        # Bind Notepad++-style clearing of token occurrence highlights
        try:
            self._bind_occurrence_clear_events()
        except Exception as e:
            self._swallow(e)
        # Vertical scrollbar for Text
        self.v_scroll = tk.Scrollbar(self.result_inner, orient='vertical', width=30)
        self.v_scroll.pack(side='right', fill='y')
        self.v_scroll.config(command=self._on_vscroll)
        self.result_box.config(yscrollcommand=self._on_yscroll)

        # Horizontal scrollbar for Text
        self.h_scroll = tk.Scrollbar(results_frame, orient='horizontal', command=self.result_box.xview, width=30)
        self.h_scroll.pack(fill='x')
        self.result_box.config(xscrollcommand=self.h_scroll.set)

        # Track Results tab state
        self._tabs[self._results_tab_id] = {
            'is_results': True,
        'pinned': False,
            'file_path': None,
            'display_name': 'Results',
            'base_title': 'Results',
            'modified': False,
            'frame': results_frame,
            'text': self.result_box,
            'gutter': self.line_numbers,
        }

        # Tab switching: update active editor pointers + refresh gutter/status
        self.workspace.bind('<<NotebookTabChanged>>', self._on_workspace_tab_changed, add='+')

        paned.add(self.result_frame)
        paned.paneconfig(self.result_frame, minsize=30, height=900)
        # Logging pane
        log_frame = tk.Frame(paned)
        log_inner = tk.Frame(log_frame)
        log_inner.pack(fill="both", expand=True)

        self.log_box = tk.Text(log_inner, wrap="none", height=7)
        self.log_box.pack(side="left", fill="both", expand=True)

        log_scroll_y = tk.Scrollbar(log_inner, orient="vertical", command=self.log_box.yview, width=30)
        log_scroll_y.pack(side="right", fill="y")
        self.log_box.config(yscrollcommand=log_scroll_y.set)

        log_scroll_x = tk.Scrollbar(log_frame, orient="horizontal", command=self.log_box.xview, width=30)
        log_scroll_x.pack(fill="x")
        self.log_box.config(xscrollcommand=log_scroll_x.set)

        # Seed logger header
        self.log_box.insert(tk.END, "Events logger:\n")
        self.log_box.config(state=tk.DISABLED)

        paned.add(log_frame)
        paned.paneconfig(log_frame, minsize=140, height=50)


        # Status bar (cursor Ln/Col, selection length, total lines)
        self.status_var = tk.StringVar(value='Lines 1   |   Ln 1, Col 0   |   Sel 0')
        status_frame = tk.Frame(self.main_frame)
        status_frame.pack(fill='x', padx=10, pady=(4, 6))
        self.status_label = tk.Label(status_frame, textvariable=self.status_var, anchor='w')
        self.status_label.pack(fill='x')
        self._install_text_shortcut_overrides()


    # -------------------- Workspace tabs --------------------
    def _on_workspace_tab_changed(self, event=None):
        tab_id = self._try(self.workspace.select, prefix='workspace.select', default=None)
        if not tab_id:
            return
        st = self._tabs.get(tab_id)
        if not st:
            return

        self.result_box = st.get('text')
        self.line_numbers = st.get('gutter')

        self._try(self._configure_tags_for_widget, self.result_box, prefix='tab_changed.tags')
        self._try(self._bind_highlight_events_for_widget, self.result_box, prefix='tab_changed.hl_bind')
        self._try(self._bind_occurrence_clear_events_for_widget, self.result_box, prefix='tab_changed.occ_clear')

        theme = self.THEMES['dark'] if self.dark_mode else self.THEMES['light']
        if isinstance(self.result_box, tk.Text):
            self._try(self.result_box.configure, bg=theme['text_bg'], fg=theme['text_fg'], insertbackground=theme['insert'], prefix='tab_changed.text_theme')
        if isinstance(self.line_numbers, tk.Text):
            self._try(self.line_numbers.configure, bg=theme['log_bg'], fg=theme['log_fg'], prefix='tab_changed.gutter_theme')

        self._try(self._update_status_bar, prefix='_update_status_bar')
        self._try(self._refresh_line_numbers, prefix='_refresh_line_numbers')
        self._try(self._update_menu_states_for_tab, prefix='_update_menu_states_for_tab')
        self._try(self._update_close_all_button_state, prefix='_update_close_all_button_state')

        # Focus-follows-tab for editors: if the user was typing in a tab editor,
        # keep the caret in the newly selected tab to prevent accidental edits in the previous tab.
        try:
            cur_focus = self.root.focus_get()
            if isinstance(cur_focus, tk.Text):
                editors = set()
                try:
                    tabs_map = getattr(self, '_tabs', None)
                    if not isinstance(tabs_map, dict):
                        tabs_map = dict()
                    for _st in tabs_map.values():
                        _tw = _st.get('text')
                        if isinstance(_tw, tk.Text):
                            editors.add(_tw)
                except Exception as e:
                    self._swallow(e)
                if cur_focus in editors and isinstance(self.result_box, tk.Text):
                    self.root.after_idle(lambda w=self.result_box: w.focus_set())
        except Exception as e:
            self._swallow(e)

    def _workspace_tab_ids(self):
        try:
            return list(self.workspace.tabs())
        except Exception:
            return []

    def _tab_id_at_xy(self, notebook: ttk.Notebook, x: int, y: int):
        """Return the tab_id (string from notebook.tabs()) under widget coords (x,y), else None.
        Uses notebook.index('@x,y') which is stable across Tk 8.6 builds.
        """
        try:
            idx = notebook.index(f"@{x},{y}")
            tabs = list(notebook.tabs())
            idx_i = int(idx)
            return tabs[idx_i] if 0 <= idx_i < len(tabs) else None
        except Exception:
            return None

    def _ensure_closable_tab_styles(self):
        """Ensure Results tab has NO close image; other tabs show close image.
        Uses per-tab images because per-tab styles are not reliable across themes.
        """
        try:
            res_id = getattr(self, '_results_tab_id', None)
            for tid in list(self.workspace.tabs()):
                st = self._tabs.get(tid, {})
                is_results = (tid == res_id) or bool(st.get('is_results'))
                if is_results:
                    try:
                        self.workspace.tab(tid, image='', compound='none')
                    except Exception as e:
                        self._swallow(e)
                else:
                    try:
                        self.workspace.tab(tid, image=self._img_tab_close, compound='right')
                    except Exception as e:
                        self._swallow(e)
        except Exception as e:
            self._swallow(e)

    def _workspace_select_results(self):
        try:
            if self._results_tab_id:
                self.workspace.select(self._results_tab_id)
        except Exception as e:
            self._swallow(e)

    def _bind_tab_editor(self, text_widget: tk.Text):
        if not isinstance(text_widget, tk.Text):
            return

        for seq in ('<KeyRelease>', '<ButtonRelease-1>', '<B1-Motion>', '<FocusIn>'):
            text_widget.bind(seq, self._update_status_bar, add='+')
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>', '<Configure>'):
            text_widget.bind(seq, self._update_linenumbers_debounced, add='+')
        for seq in ('<KeyRelease>', '<Return>', '<BackSpace>', '<Delete>', '<<Paste>>', '<<Cut>>', '<<Undo>>', '<<Redo>>'):
            text_widget.bind(seq, self._update_linenumbers_debounced, add='+')

        for seq in ('<KeyRelease>', '<ButtonRelease-1>', '<B1-Motion>'):
            text_widget.bind(seq, self._on_occurrence_selection_change_debounced, add='+')

        self._try(text_widget.bind, '<Control-s>', self._shortcut_save, prefix='bind.ctrl-s')
        self._try(text_widget.bind, '<Control-e>', self._shortcut_export, prefix='bind.ctrl-e')
        self._try(text_widget.bind, '<Control-o>', self._shortcut_open_files, prefix='bind.ctrl-o')
        self._try(text_widget.bind, '<Control-O>', self._shortcut_open_files, prefix='bind.ctrl-O')
        self._try(text_widget.bind, '<Control-Shift-p>', self._shortcut_open_in_tabs, prefix='bind.ctrl-shift-p')
        self._try(text_widget.bind, '<Control-Shift-P>', self._shortcut_open_in_tabs, prefix='bind.ctrl-shift-P')
        self._try(text_widget.bind, '<Control-w>', self._shortcut_close_tab, prefix='bind.ctrl-w')
        self._try(text_widget.bind, '<Control-Shift-W>', self._shortcut_close_all_tabs, prefix='bind.ctrl-shift-w')
        self._try(text_widget.bind, '<Control-Shift-w>', self._shortcut_close_all_tabs, prefix='bind.ctrl-shift-w.lower')

        self._try(self._configure_tags_for_widget, text_widget, prefix='tab_editor.tags')

        self._try(text_widget.bind, '<Button-3>', self._show_text_context_menu, prefix='bind.ctx.right')
        self._try(text_widget.bind, '<Control-Button-1>', self._show_text_context_menu, prefix='bind.ctx.ctrlclick')
        self._try(text_widget.bind, '<App>', lambda e, w=text_widget: self._show_text_context_menu_keyboard(e, w), prefix='bind.ctx.app')
        self._try(text_widget.bind, '<Menu>', lambda e, w=text_widget: self._show_text_context_menu_keyboard(e, w), prefix='bind.ctx.menu')

        self._try(self._bind_highlight_events_for_widget, text_widget, prefix='tab_editor.hl_bind')

        self._try(text_widget.bind, '<Double-Button-1>', lambda e, widget=text_widget: self._select_token_on_double_click(e, widget), prefix='bind.dblclick')
        self._try(text_widget.bind, '<Triple-Button-1>', lambda e, widget=text_widget: self._select_line_on_triple_click(e, widget), prefix='bind.tripleclick')
        self._try(text_widget.bind, '<Control-Shift-Left>', lambda e, widget=text_widget: self._kbd_token_select_left(e, widget), prefix='bind.ctrlshift.left')
        self._try(text_widget.bind, '<Control-Shift-Right>', lambda e, widget=text_widget: self._kbd_token_select_right(e, widget), prefix='bind.ctrlshift.right')
        self._try(text_widget.bind, '<Control-Left>', lambda e, widget=text_widget: self._kbd_token_move_left(e, widget), prefix='bind.ctrl.left')
        self._try(text_widget.bind, '<Control-Right>', lambda e, widget=text_widget: self._kbd_token_move_right(e, widget), prefix='bind.ctrl.right')

        self._try(self._bind_occurrence_clear_events_for_widget, text_widget, prefix='tab_editor.occ_clear')

    def new_tab(self, event=None):
        """Create a new blank workspace tab."""
        open_non_results = [tid for tid, st in self._tabs.items() if not st.get('is_results')]
        if len(open_non_results) >= int(getattr(self, 'MAX_WORK_TABS', 14) or 14):
            self._mb_showwarning('Tabs', f'Tab limit reached ({self.MAX_WORK_TABS}). Close a tab before opening another.')
            return 'break'

        self._tab_counter += 1
        title = f'Untitled {self._tab_counter}'

        tab_frame = tk.Frame(self.workspace)
        inner = tk.Frame(tab_frame)
        inner.pack(fill='both', expand=True)

        gutter = tk.Text(inner, width=4, padx=4, takefocus=0, borderwidth=0, relief='flat', wrap='none')
        gutter.pack(side='left', fill='y')
        gutter.config(state='disabled')

        textw = tk.Text(inner, wrap='none', undo=True, maxundo=10, autoseparators=True)
        mono = getattr(self, '_mono_font', ("Lucida Console", 10))
        try:
            textw.configure(font=mono)
            gutter.configure(font=mono)
        except Exception as e:
            self._swallow(e)
        textw.pack(side='left', fill='both', expand=True)

        self._bind_tab_editor(textw)

        v_scroll = tk.Scrollbar(inner, orient='vertical', width=30)
        v_scroll.pack(side='right', fill='y')
        h_scroll = tk.Scrollbar(tab_frame, orient='horizontal', command=textw.xview, width=30)
        h_scroll.pack(fill='x')

        def on_vscroll(*args):
            textw.yview(*args)
            self._update_linenumbers_debounced()
            try:
                if not getattr(textw, '_suppress_scroll_cb', False):
                    self._debounced_update(widget=textw)
            except Exception as e:
                self._swallow(e)

        def on_yscroll(*args):
            v_scroll.set(*args)
            self._update_linenumbers_debounced()
            try:
                if not getattr(textw, '_suppress_scroll_cb', False):
                    self._debounced_update(widget=textw)
            except Exception as e:
                self._swallow(e)

        v_scroll.config(command=on_vscroll)
        textw.config(yscrollcommand=on_yscroll, xscrollcommand=h_scroll.set)

        self.workspace.add(tab_frame, text=title)
        tab_id = self.workspace.tabs()[-1]

        try:
            self.workspace.tab(tab_id, image=self._img_tab_close, compound='right')
        except Exception as e:
            self._swallow(e)
        try:
            self._ensure_closable_tab_styles()
        except Exception as e:
            self._swallow(e)
        self._tabs[tab_id] = {
            'is_results': False,
        'pinned': False,
            'file_path': None,
            'display_name': title,
            'base_title': title,
            'modified': False,
            'frame': tab_frame,
            'text': textw,
            'gutter': gutter,
        }

        self._install_modified_tracking_for_tab(tab_id)
        self.workspace.select(tab_id)
        # New tab: ensure caret/focus moves to the new editor to avoid editing the previous tab
        try:
            if isinstance(textw, tk.Text):
                textw.mark_set('insert', '1.0')
                textw.tag_remove('sel', '1.0', 'end')
                self.root.after_idle(lambda w=textw: (w.focus_set(), w.see('insert')))
        except Exception as e:
            self._swallow(e)
        return 'break'

    def open_file_in_tab(self, file_path: str, focus: bool = True):
        """Open a file in its own workspace tab (focus existing if already open)."""
        if not file_path:
            return

        norm = os.path.normpath(file_path)
        if norm in self._file_to_tab:
            tab_id = self._file_to_tab.get(norm)
            if tab_id and focus:
                try:
                    self.workspace.select(tab_id)
                except Exception as e:
                    self._swallow(e)
            return

        open_non_results = [tid for tid, st in self._tabs.items() if not st.get('is_results')]
        if len(open_non_results) >= int(getattr(self, 'MAX_WORK_TABS', 14) or 14):
            self._mb_showwarning('Tabs', f'Tab limit reached ({self.MAX_WORK_TABS}). Close a tab before opening another.')
            return

        title = os.path.basename(file_path)

        tab_frame = tk.Frame(self.workspace)
        inner = tk.Frame(tab_frame)
        inner.pack(fill='both', expand=True)

        gutter = tk.Text(inner, width=4, padx=4, takefocus=0, borderwidth=0, relief='flat', wrap='none')
        gutter.pack(side='left', fill='y')
        gutter.config(state='disabled')

        textw = tk.Text(inner, wrap='none', undo=True, maxundo=10, autoseparators=True)
        mono = getattr(self, '_mono_font', ("Lucida Console", 10))
        try:
            textw.configure(font=mono)
            gutter.configure(font=mono)
        except Exception as e:
            self._swallow(e)
        textw.pack(side='left', fill='both', expand=True)

        self._bind_tab_editor(textw)

        v_scroll = tk.Scrollbar(inner, orient='vertical', width=30)
        v_scroll.pack(side='right', fill='y')
        h_scroll = tk.Scrollbar(tab_frame, orient='horizontal', command=textw.xview, width=30)
        h_scroll.pack(fill='x')

        def on_vscroll(*args):
            textw.yview(*args)
            self._update_linenumbers_debounced()
            try:
                if not getattr(textw, '_suppress_scroll_cb', False):
                    self._debounced_update(widget=textw)
            except Exception as e:
                self._swallow(e)

        def on_yscroll(*args):
            v_scroll.set(*args)
            self._update_linenumbers_debounced()
            try:
                if not getattr(textw, '_suppress_scroll_cb', False):
                    self._debounced_update(widget=textw)
            except Exception as e:
                self._swallow(e)

        v_scroll.config(command=on_vscroll)
        textw.config(yscrollcommand=on_yscroll, xscrollcommand=h_scroll.set)

        try:
            with open(file_path, 'rb') as f:
                data = f.read()
            if data.startswith(b"\xef\xbb\xbf"):
                content = data.decode('utf-8-sig', errors='ignore')
            else:
                content = data.decode('utf-8', errors='ignore')
        except Exception as e:
            self._mb_showerror('Open in Tab', f"Failed to open file:\n{file_path}\n\n{type(e).__name__}: {e}")
            return

        try:
            textw.insert('1.0', content)
            # Reset undo stack after programmatic file load
            self._reset_undo_baseline(textw, modified=False)
            textw.edit_modified(False)
            # Normalize initial caret for newly opened file tabs (start at top, not EOF)
            # This prevents the tab from appearing scrolled-down immediately after opening.
            try:
                textw.mark_set('insert', '1.0')
                textw.tag_remove('sel', '1.0', 'end')
                textw.see('1.0')
                try:
                    textw.xview_moveto(0.0)
                    textw.yview_moveto(0.0)
                except Exception:
                    pass
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            self._swallow(e)
        self.workspace.add(tab_frame, text=title)
        tab_id = self.workspace.tabs()[-1]

        try:
            self.workspace.tab(tab_id, image=self._img_tab_close, compound='right')
        except Exception as e:
            self._swallow(e)
        try:
            self._ensure_closable_tab_styles()
        except Exception as e:
            self._swallow(e)
        self._tabs[tab_id] = {
            'is_results': False,
            'file_path': file_path,
        'pinned': False,
            'display_name': title,
            'base_title': title,
            'modified': False,
            'frame': tab_frame,
            'text': textw,
            'gutter': gutter,
        }
        self._file_to_tab[norm] = tab_id

        self._install_modified_tracking_for_tab(tab_id)
        self._install_workspace_tab_tooltip()

        if focus:
            try:
                self.workspace.select(tab_id)
                # Open in tab: ensure caret/focus moves to the opened editor
                try:
                    if isinstance(textw, tk.Text):
                        # caret already normalized to 1.0 above; keep view consistent
                        self.root.after_idle(lambda w=textw: (w.focus_set(), w.see('insert')))
                except Exception as e:
                    self._swallow(e)
            except Exception as e:
                self._swallow(e)

        try:
            self._update_tabs_open_label()
            self._update_close_all_button_state()

        except Exception as e:
            self._swallow(e)

    def _install_workspace_tab_tooltip(self):
        """Tooltip over workspace notebook tabs.

        Behavior mirrors ListboxTooltip:
        - Uses the same delay (TOOLTIP_DELAY_MS, default 500 ms).
        - Shows full file path for file-backed tabs.
        - For unsaved tabs (Untitled #), shows: "Unsaved file — no path yet".
        - Results tab shows no tooltip.
        """
        if getattr(self, '_ws_tt_installed', False):
            return
        self._ws_tt_installed = True

        self._ws_tt_win = None
        self._ws_tt_after = None
        self._ws_tt_last_tab = None
        delay = int(getattr(self, 'TOOLTIP_DELAY_MS', 500) or 500)

        def hide(_=None):
            try:
                if self._ws_tt_after:
                    self.workspace.after_cancel(self._ws_tt_after)
            except Exception as e:
                self._swallow(e)
            self._ws_tt_after = None
            self._ws_tt_last_tab = None
            try:
                if self._ws_tt_win:
                    self._ws_tt_win.destroy()
            except Exception as e:
                self._swallow(e)
            self._ws_tt_win = None

        def show(x, y, txt):
            hide()
            if not txt:
                return
            self._ws_tt_win = tk.Toplevel(self.workspace)
            self._ws_tt_win.wm_overrideredirect(True)
            self._ws_tt_win.wm_geometry(f'+{x+10}+{y+10}')
            tk.Label(
                self._ws_tt_win,
                text=txt,
                background='#ffffe0',
                relief='solid',
                borderwidth=1,
                font=('Lucida Console', 9)
            ).pack()

        def tooltip_text_for_tab(tab_id: str) -> str:
            st = self._tabs.get(tab_id) if tab_id else None
            if not st:
                return ''
            if st.get('is_results') or tab_id == getattr(self, '_results_tab_id', None):
                return ''
            fp = st.get('file_path')
            if fp:
                return str(fp)
            return 'Unsaved file — no path yet'

        def on_motion(event):
            try:
                tab_id = self._tab_id_at_xy(self.workspace, event.x, event.y)
            except Exception:
                tab_id = None

            if not tab_id:
                hide()
                return

            txt = tooltip_text_for_tab(tab_id)
            if not txt:
                hide()
                return

            # reschedule on motion (ListboxTooltip behavior)
            try:
                if self._ws_tt_after:
                    self.workspace.after_cancel(self._ws_tt_after)
            except Exception as e:
                self._swallow(e)
            self._ws_tt_after = None

            if self._ws_tt_last_tab is not None and self._ws_tt_last_tab != tab_id:
                hide()
            self._ws_tt_last_tab = tab_id

            self._ws_tt_after = self.workspace.after(
                delay,
                lambda x=event.x_root, y=event.y_root, t=txt: show(x, y, t)
            )

        try:
            self.workspace.bind('<Motion>', on_motion, add='+')
            self.workspace.bind('<Leave>', hide, add='+')
            self.workspace.bind('<ButtonPress-1>', hide, add='+')
            self.workspace.bind('<<NotebookTabChanged>>', hide, add='+')
        except Exception as e:
            self._swallow(e)

    def _workspace_cycle(self, delta: int):
        try:
            tabs = self._workspace_tab_ids()
            if not tabs:
                return
            cur = self.workspace.select()
            i = tabs.index(cur) if cur in tabs else 0
            self.workspace.select(tabs[(i + delta) % len(tabs)])
        except Exception as e:
            self._swallow(e)
    def _shortcut_tab_left(self, event=None):
        self._workspace_cycle(-1)
        return 'break'

    def _shortcut_tab_right(self, event=None):
        self._workspace_cycle(+1)
        return 'break'

    def _count_open_non_results_tabs(self) -> int:
        """Return the number of currently open *non-Results* tabs.
        Pinned tabs still count toward the MAX_WORK_TABS capacity.
        """
        try:
            return sum(1 for st in (getattr(self, '_tabs', {}) or {}).values() if not st.get('is_results'))
        except Exception:
            return 0

    def _available_work_tab_slots(self) -> int:
        """How many additional work tabs can be opened right now."""
        try:
            max_tabs = int(getattr(self, 'MAX_WORK_TABS', 0) or 0)
        except Exception:
            max_tabs = 0
        cur = self._count_open_non_results_tabs()

        return max(0, max_tabs - cur)

    def _open_selected_in_tabs(self, event=None):
        """Open *all* selected listbox files in separate tabs (subject to MAX_WORK_TABS).
        Behavior:
          - If a selected file is already open in a tab, it is focused (does not consume a slot).
          - If selection requires more new tabs than available slots, show a warning and do nothing.
        """
        paths = self.get_selected_file_paths()
        if not paths:
            self._mb_showwarning('Open in Tabs', 'No file selected.')
            return 'break'

        # Compute how many *new* tabs would be needed (exclude already-open files).
        new_needed = []
        try:
            ft = getattr(self, '_file_to_tab', {}) or {}
        except Exception:
            ft = {}

        for p in paths:
            try:
                norm = os.path.normpath(p)
            except Exception:
                norm = p

            if norm not in ft:
                new_needed.append(p)

        available = self._available_work_tab_slots()
        current_open = self._count_open_non_results_tabs()
        selected_files = len(self.file_listbox.curselection())

        if len(new_needed) > available:
            msg = (
                f"Too many files selected to open in tabs.\n\n"
                f"Total No. of files selected: {selected_files}\n"
                f"Max allowed work tabs: {self.MAX_WORK_TABS}\n"
                f"Currently open tabs: {current_open}\n"
                f"Available slots: {available}\n\n"
                f"Please select fewer file(s) and try again."
            )

            self._mb_showwarning('Open in Tabs', msg)
            return 'break'

        # Open each selected file; focus the last one to avoid rapid focus flipping.

        for i, p in enumerate(paths):
            focus = (i == (len(paths) - 1))
            try:
                self.open_file_in_tab(p, focus=focus)
            except Exception as e:
                self._swallow(e)
        return 'break'

    def _shortcut_open_in_tabs(self, event=None):
        self._open_selected_in_tabs(event)
        return 'break'

    def _open_selected_in_tab(self):
        """Context-menu command: Open selected file(s) in tab(s)."""
        paths = self.get_selected_file_paths()
        if not paths:
            self._mb_showwarning('Open in Tab', 'No file selected.')
            return

        if len(paths) == 1:
            self.open_file_in_tab(paths[0], focus=True)
            return

        # Multi-selection -> open in separate tabs
        self._open_selected_in_tabs()

    def _refresh_tab_title(self, tab_id: str):
        """Refresh a tab title to reflect pinned + modified state.

        Title composition rules:
        - Base title comes from st['base_title'] (or display_name fallback).
        - If pinned: prefix with a pin glyph.
        - If modified: suffix with ' *'.
        """
        st = self._tabs.get(tab_id)
        if not st or st.get('is_results'):
            return
        base = st.get('base_title') or st.get('display_name') or 'Untitled'
        pin_glyph = '📌'
        pinned = bool(st.get('pinned', False))
        modified = bool(st.get('modified', False))
        label = f"{pin_glyph} {base}" if pinned else str(base)
        if modified:
            label += ' *'
        try:
            self.workspace.tab(tab_id, text=label)
        except Exception as e:
            self._swallow(e)

    def _set_tab_modified(self, tab_id: str, modified: bool):
        """Set modified flag for a tab and update its title (pin-aware)."""
        st = self._tabs.get(tab_id)
        if not st or st.get('is_results'):
            return
        st['modified'] = bool(modified)
        self._refresh_tab_title(tab_id)

    def _set_tab_pinned(self, tab_id: str, pinned: bool):
        """Set pinned flag for a tab and update its title."""
        st = self._tabs.get(tab_id)
        if not st or st.get('is_results') or tab_id == getattr(self, '_results_tab_id', None):
            return
        st['pinned'] = bool(pinned)
        self._refresh_tab_title(tab_id)
        try:
            self._update_menu_states_for_tab()
        except Exception as e:
            self._swallow(e)
        try:
            self._update_close_all_button_state()
        except Exception as e:
            self._swallow(e)

    def toggle_pin_tab(self, tab_id: str = None):
        """Toggle pinned/unpinned state for the given tab (defaults to current tab)."""
        try:
            if tab_id is None:
                tab_id = self.workspace.select()
        except Exception:
            return
        st = self._tabs.get(tab_id)
        if not st or st.get('is_results') or tab_id == getattr(self, '_results_tab_id', None):
            return
        self._set_tab_pinned(tab_id, not bool(st.get('pinned', False)))

    def _install_modified_tracking_for_tab(self, tab_id: str):
        """Attach a <<Modified>> listener to mark a tab dirty when user edits."""
        st = self._tabs.get(tab_id)
        if not st or st.get('is_results'):
            return
        w = st.get('text')
        if not isinstance(w, tk.Text):
            return
        if st.get('_modified_bound'):
            return
        st['_modified_bound'] = True

        def _on_modified(event=None, _tid=tab_id, _w=w):
            try:
                if _w.edit_modified():
                    _w.edit_modified(False)
                    self._set_tab_modified(_tid, True)
            except Exception as e:
                self._swallow(e)
        try:
            w.bind('<<Modified>>', _on_modified, add='+')
            w.edit_modified(False)
        except Exception as e:
            self._swallow(e)

    def _save_tab_as(self, tab_id: str, content: str = None) -> bool:
        """Save a non-file-backed (Untitled) tab via Save As and convert it into a file-backed tab.
        After a successful save, the tab title is updated to the filename and the path is appended
        to the file listbox (end), mirroring the 'load new file' UX.
        """
        st = self._tabs.get(tab_id) if tab_id else None

        if not st or st.get('is_results'):
            return False

        w = st.get('text')

        if content is None:
            try:
                content = w.get('1.0', 'end-1c') if isinstance(w, tk.Text) else ''
            except Exception:
                content = ''

        save_path = filedialog.asksaveasfilename(
            defaultextension='.txt',
            filetypes=[('Log files', '*.log'), ('Text files', '*.txt'), ('All files', '*.*')],
        )

        if not save_path:
            return False

        try:
            norm = os.path.normpath(save_path)
        except Exception:
            norm = save_path

        try:
            other_tid = self._file_to_tab.get(norm)
        except Exception:
            other_tid = None

        if other_tid and other_tid != tab_id:
            try:
                self._mb_showwarning('Save', 'That file is already open in another tab. Choose a different name.')
            except Exception as e:
                self._swallow(e)
            return False

        try:
            with open(save_path, 'w', encoding='utf-8', newline='\n') as f:
                f.write(content or '')
        except Exception as e:
            try:
                self._mb_showerror('Save', 'Save failed:\n%s\n\n%s: %s' % (save_path, type(e).__name__, e))
            except Exception as ee:
                self._swallow(ee)
            return False

        st['file_path'] = save_path
        base = os.path.basename(save_path)
        st['base_title'] = base
        st['display_name'] = base
        st['modified'] = False

        try:
            self._file_to_tab[norm] = tab_id
        except Exception as e:
            self._swallow(e)

        try:
            self._refresh_tab_title(tab_id)
        except Exception as e:
            self._swallow(e)

        try:
            if isinstance(w, tk.Text):
                w.edit_modified(False)
        except Exception as e:
            self._swallow(e)

        try:
            self._append_file_to_listbox_if_missing(save_path, select=True)
        except Exception as e:
            self._swallow(e)

        try:
            self.log_message('Saved: %s' % save_path)
        except Exception as e:
            self._swallow(e)

        try:
            self._update_menu_states_for_tab()
        except Exception as e:
            self._swallow(e)

        return True

    def save_current_tab(self, event=None):
        """Save current tab back to disk if it's a file-backed tab. Untitled/Results cannot be saved."""
        try:
            tab_id = self.workspace.select()
        except Exception:
            return 'break'

        st = self._tabs.get(tab_id)

        # Untitled (non-file-backed) tabs: use Save As then convert tab to file-backed

        if st and (not st.get('is_results')) and (not st.get('file_path')):
            try:
                self._save_tab_as(tab_id)
            except Exception as e:
                self._swallow(e)
            return 'break'

        if not st:
            return 'break'

        if st.get('is_results') or (not st.get('file_path')):
            try:
                self._mb_showinfo('Save', 'Save is not available for this tab. Use Export instead.')
            except Exception as e:
                self._swallow(e)
            return 'break'

        path = st.get('file_path')
        w = st.get('text')

        try:
            content = w.get('1.0', 'end-1c') if isinstance(w, tk.Text) else ''
        except Exception:
            content = ''

        try:
            with open(path, 'w', encoding='utf-8', newline='\n') as f:
                f.write(content)
            self._set_tab_modified(tab_id, False)
            try:
                if isinstance(w, tk.Text):
                    w.edit_modified(False)
            except Exception as e:
                self._swallow(e)
            try:
                self.log_message(f"Saved: {path}")
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            try:
                self._mb_showerror('Save', f"Save failed:\n{path}\n\n{type(e).__name__}: {e}")
            except Exception as e:
                self._swallow(e)
        return 'break'

    def _shortcut_save(self, event=None):
        return self.save_current_tab(event)

    def _update_menu_states_for_tab(self):
        """Enable/disable menu items based on current tab and workspace state."""
        try:
            file_menu = getattr(self, '_file_menu', None)
            if file_menu is None:
                return
            tab_id = None
            try:
                tab_id = self.workspace.select()
            except Exception:
                tab_id = None
            st = self._tabs.get(tab_id) if tab_id else None

            # Save enabled only for file-backed tabs
            save_idx = getattr(self, '_file_menu_save_index', None)
            if save_idx is not None:
                enable_save = bool(st and (not st.get('is_results')))
                try:
                    file_menu.entryconfig(save_idx, state=('normal' if enable_save else 'disabled'))
                except Exception as e:
                    self._swallow(e)
            # Close Tab enabled when current tab is not Results
            close_idx = getattr(self, '_file_menu_close_index', None)
            if close_idx is not None:
                enable_close = bool(st and (not st.get('is_results')))
                try:
                    file_menu.entryconfig(close_idx, state=('normal' if enable_close else 'disabled'))
                except Exception as e:
                    self._swallow(e)
            # Close All enabled when there is at least one non-Results tab
            closeall_idx = getattr(self, '_file_menu_closeall_index', None)
            if closeall_idx is not None:
                any_non_results = any((not s.get('is_results')) and (not s.get('pinned', False)) for s in self._tabs.values())
                try:
                    file_menu.entryconfig(closeall_idx, state=('normal' if any_non_results else 'disabled'))
                except Exception as e:
                    self._swallow(e)
        except Exception as e:
            self._swallow(e)

    # -------------------- Workspace tab close management --------------------
        try:
            self._update_close_all_button_state()
        except Exception as e:
            self._swallow(e)

    def _ask_modified_tab_action(self, tab_id: str):
        """Ask what to do with unsaved changes.

        Returns one of: 'save', 'export', 'discard', 'cancel'
        - File-backed tabs: Save / Discard / Cancel
        - Untitled tabs: Export / Discard / Cancel
        """
        st = self._tabs.get(tab_id)
        if not st:
            return 'cancel'
        if st.get('is_results'):
            return 'cancel'

        file_backed = bool(st.get('file_path'))
        base = st.get('base_title') or st.get('display_name') or 'Untitled'

        # Build a small custom dialog so button labels are explicit.
        dlg = tk.Toplevel(self.root)
        dlg.title('Unsaved changes')
        try:
            dlg.transient(self.root)
        except Exception as e:
            self._swallow(e)
        result = {'choice': 'cancel'}

        # Body
        frm = tk.Frame(dlg)
        frm.pack(fill='both', expand=True, padx=14, pady=12)

        msg = f"Tab '{base}' has unsaved changes.\n\nWhat would you like to do?"
        tk.Label(frm, text=msg, justify='left', anchor='w').pack(fill='x')

        btns = tk.Frame(frm)
        btns.pack(fill='x', pady=(12, 0))

        def set_choice(ch):
            result['choice'] = ch
            try:
                dlg.destroy()
            except Exception as e:
                self._swallow(e)
        # Buttons
        primary_label = 'Save' if file_backed else 'Export'
        primary_choice = 'save' if file_backed else 'export'

        b1 = tk.Button(btns, text=primary_label, width=10, command=lambda: set_choice(primary_choice))
        b2 = tk.Button(btns, text='Discard', width=10, command=lambda: set_choice('discard'))
        b3 = tk.Button(btns, text='Cancel', width=10, command=lambda: set_choice('cancel'))

        b3.pack(side='right', padx=(8, 0))
        b2.pack(side='right', padx=(8, 0))
        b1.pack(side='right')

        # Default focus/keys
        try:
            dlg.bind('<Escape>', lambda e: set_choice('cancel'))
            dlg.bind('<Return>', lambda e: set_choice(primary_choice))
        except Exception as e:
            self._swallow(e)
        try:
            dlg.grab_set()
        except Exception as e:
            self._swallow(e)
        # Center relative to root
        try:
            dlg.update_idletasks()
            x = self.root.winfo_rootx() + int(self.root.winfo_width() * 0.35)
            y = self.root.winfo_rooty() + int(self.root.winfo_height() * 0.35)
            dlg.geometry(f'+{x}+{y}')
        except Exception as e:
            self._swallow(e)
        self.root.wait_window(dlg)
        return result.get('choice', 'cancel')

    def _export_current_tab_for_close(self):
        """Export active tab content for close-flow. Returns True if exported, False if cancelled/failed."""
        try:
            text_now = self.result_box.get('1.0', 'end-1c')
        except Exception:
            text_now = ''

        if not text_now.strip():
            try:
                self._mb_showwarning('Export', 'Current Tab is empty.')
            except Exception as e:
                self._swallow(e)
            return False

        export_path = filedialog.asksaveasfilename(
            defaultextension='.txt',
            filetypes=[('Log files', '*.log'), ('Text files', '*.txt'), ('All files', '*.*')],
        )
        if not export_path:
            return False

        try:
            lines = text_now.splitlines()
            with open(export_path, 'w', encoding='utf-8-sig', newline='\n') as f:
                for line in lines:
                    f.write(line + '\n')
            try:
                self._mb_showinfo('Export Successful', f'Results exported to {export_path}')
            except Exception as e:
                self._swallow(e)
            try:
                self.log_message(f'Results exported to {export_path}')
            except Exception as e:
                self._swallow(e)
            return True
        except Exception as e:
            try:
                self._mb_showerror('Export Error', f'Failed to export results: {e}')
            except Exception as e:
                self._swallow(e)
            try:
                self.log_message(f'Export error: {e}')
            except Exception as e:
                self._swallow(e)
            return False

    def close_tab(self, tab_id: str = None):
        """Close a specific workspace tab. Returns True if closed, False otherwise."""
        try:
            if tab_id is None:
                tab_id = self.workspace.select()
        except Exception:
            return False

        st = self._tabs.get(tab_id)
        if not st:
            return False

        # Do not close Results
        if st.get('is_results') or tab_id == getattr(self, '_results_tab_id', None):
            try:
                self._mb_showinfo('Tabs', 'The Results tab cannot be closed.')
            except Exception as e:
                self._swallow(e)
            return False

        # Ensure this tab is active (so Save/Export operate on it)
        try:
            if self.workspace.select() != tab_id:
                self.workspace.select(tab_id)
                try:
                    self._on_workspace_tab_changed()
                except Exception as e:
                    self._swallow(e)
        except Exception as e:
            self._swallow(e)
        # Unsaved changes prompt
        if bool(st.get('modified')):
            choice = self._ask_modified_tab_action(tab_id)
            if choice == 'cancel':
                return False
            if choice == 'save':
                self.save_current_tab()
                st2 = self._tabs.get(tab_id)
                if st2 and st2.get('modified'):
                    return False
            elif choice == 'export':
                ok = self._export_current_tab_for_close()
                if not ok:
                    return False
            elif choice == 'discard':
                pass

        # Remove file->tab mapping if needed
        fp = st.get('file_path')
        if fp:
            try:
                norm = os.path.normpath(fp)
                if self._file_to_tab.get(norm) == tab_id:
                    del self._file_to_tab[norm]
            except Exception as e:
                self._swallow(e)
        # Forget + destroy
        try:
            self.workspace.forget(tab_id)
        except Exception as e:
            self._swallow(e)
        try:
            fr = st.get('frame')
            if fr is not None:
                fr.destroy()
        except Exception as e:
            self._swallow(e)
        try:
            if tab_id in self._tabs:
                del self._tabs[tab_id]
        except Exception as e:
            self._swallow(e)
        # Select something sensible
        try:
            tabs = list(self.workspace.tabs())
            if tabs:
                if getattr(self, '_results_tab_id', None) in tabs:
                    self._on_workspace_tab_changed()
                else:
                    self.workspace.select(tabs[0])
                    self._on_workspace_tab_changed()
            else:
                self._workspace_select_results()
                self._on_workspace_tab_changed()
        except Exception as e:
            self._swallow(e)
        try:
            self._update_menu_states_for_tab()
            self._update_close_all_button_state()
            try:
                self._update_tabs_open_label()
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            self._swallow(e)
        return True

    def close_current_tab(self, event=None):
        """Close the currently selected tab (Ctrl+W)."""
        self.close_tab(None)
        return 'break'

    def close_all_tabs(self, event=None, confirm=True):
        """Close all non-Results, non-pinned tabs.
        Entry points:
          - Close All Tabs button
          - File menu: Close All Tabs
          - Ctrl+Shift+W shortcut
        Pinned tabs remain open.
        """
        # Standard confirmation for any Close-All entry point
        try:
            any_non_results = any((not s.get('is_results')) and (not s.get('pinned', False)) for s in self._tabs.values())
        except Exception:
            any_non_results = False

        if confirm and any_non_results:
            if not self._mb_askyesno('Closing Tabs confirmation', 'Close all tabs?'):
                return 'break'

        try:
            tab_ids = list(self.workspace.tabs())
        except Exception:
            tab_ids = list(self._tabs.keys())

        res_id = getattr(self, '_results_tab_id', None)

        targets = [
            tid for tid in tab_ids
            if tid != res_id
            and (not self._tabs.get(tid, {}).get('is_results'))
            and (not self._tabs.get(tid, {}).get('pinned', False))
        ]

        for tid in reversed(targets):
            ok = self.close_tab(tid)

            if not ok:
                break

        try:
            self._update_tabs_open_label()
        except Exception as e:
            self._swallow(e)

        return 'break'

    def close_other_tabs(self, keep_tab_id: str):
        """Close all non-Results tabs except the specified one."""
        res_id = getattr(self, '_results_tab_id', None)
        try:
            tab_ids = list(self.workspace.tabs())
        except Exception:
            tab_ids = list(self._tabs.keys())

        targets = [tid for tid in tab_ids if tid not in (res_id, keep_tab_id) and (not self._tabs.get(tid, {}).get('is_results')) and (not self._tabs.get(tid, {}).get('pinned', False))]
        for tid in reversed(targets):
            ok = self.close_tab(tid)
            if not ok:
                break

    def _shortcut_close_tab(self, event=None):
        return self.close_current_tab(event)

    def _shortcut_close_all_tabs(self, event=None):
        return self.close_all_tabs(event)

    def _install_workspace_tab_context_menu(self):
        """Right-click context menu on workspace notebook tabs.

        - For any tab except Results: show "Pin Tab"/"Unpin Tab" toggle and "Close tab".
        - "Pin Tab" is placed above "Close tab".
        - For Results tab: do not show a menu.
        """
        if getattr(self, '_ws_ctx_installed', False):
            return
        self._ws_ctx_installed = True

        self._ws_ctx_tab_id = None
        self._ws_ctx_menu = tk.Menu(self.root, tearoff=0)

        # Entry 0: Pin/Unpin (label updated dynamically)
        self._ws_ctx_menu.add_command(
            label='Pin Tab',
            command=lambda: self.toggle_pin_tab(getattr(self, '_ws_ctx_tab_id', None))
        )
        # Entry 1: Close tab
        self._ws_ctx_menu.add_command(
            label='Close tab',
            command=lambda: self.close_tab(getattr(self, '_ws_ctx_tab_id', None))
        )

        def _show(event):
            try:
                tab_id = self._tab_id_at_xy(self.workspace, event.x, event.y)
            except Exception:
                tab_id = None
            if not tab_id:
                return

            # Do not show menu for Results
            if tab_id == getattr(self, '_results_tab_id', None) or self._tabs.get(tab_id, {}).get('is_results'):
                return

            self._ws_ctx_tab_id = tab_id

            # Update Pin/Unpin label based on tab state
            st = self._tabs.get(tab_id, {})
            pin_label = 'Unpin Tab' if bool(st.get('pinned', False)) else 'Pin Tab'
            try:
                self._ws_ctx_menu.entryconfig(0, label=pin_label)
            except Exception as e:
                self._swallow(e)
            try:
                self._ws_ctx_menu.tk_popup(event.x_root, event.y_root)
            finally:
                try:
                    self._ws_ctx_menu.grab_release()
                except Exception as e:
                    self._swallow(e)
        try:
            self.workspace.bind('<Button-3>', _show, add='+')
        except Exception as e:
            self._swallow(e)

    # -------------------- Tab close button (X) + Close All Tabs button (layout) --------------------
    # Close icon PNGs (base64, transparent background)
    _CLOSE_ICON_PNG_NORMAL = "iVBORw0KGgoAAAANSUhEUgAAAAwAAAAMCAYAAABWdVznAAAA30lEQVR4nF3RvS5EURQF4O+OO5UEI3F1KoVMQYEHUHhfP2+gmA5DFCJCIX4SJGSiw1XMupMTJznZK3uvs/fa61SosJT4gTZXcrCIHj5hgCu8YDOEOoSOfFvWlzFJ11M0IfbQx2ExdVeSOxgneZYmcJTcM/YxX+pscB7CCAfBpdTZqRNXcFJIuMGw5HSL/Qa/4b1oNMFjcOfcTFK/0HxfyLsojKi6Uas4DuEJG1goHo2xnqYGuEvh4d+CjalrLb6wxdTCV3xjr1hwLnjN9IdbbFcpDjPuEj8xodPcZmqN6z8hKj07+dPclwAAAABJRU5ErkJggg=="
    _CLOSE_ICON_PNG_ACTIVE = "iVBORw0KGgoAAAANSUhEUgAAAAwAAAAMCAYAAABWdVznAAABR0lEQVR4nE3Rz2oTYRQF8N83mYBULGnAiPsuSpW6UPdu3PsEPqOtDxBQcJU2MUJJJ5NJjNgWiaUYY/zXfC5mgjmLu7nnHs49RyT02ZnSjCSRoEIkREKXRrWvJR9obPG2zukZDwOxTRpJAvGY7Qadv5wWPDClmTOfE8cc57Qq9aRDfcThFfGcOOCpDvWcJxm9JXHCyZQmFBwtiCMuMp73uG3tOadV0P1DzHiX8epnKXA54sAm2qSQcXfMm0viRUnOMvYriynVeMYqkmA24mssCVbMa3z+H1oVHda/HC2JQ8ZDuktiwfuNIII26Yh7Z7z+QZxyPmBvxvakOsrpDdntUPeRnZziqiR/Gmw8mNOacDIrjxYFj5JQtnnnNze/eLlHP5bF1Xb58p0XC77V2FqRhjbpffZT6tf0H3MTWK09h7Kwg1ukMwb/AORWm35607JFAAAAAElFTkSuQmCC"
    _CLOSE_ICON_PNG_PRESSED = "iVBORw0KGgoAAAANSUhEUgAAAAwAAAAMCAYAAABWdVznAAABfElEQVR4nDXRO2sUYQCF4eeb7GXiZt1LLmBAiQj+AUtB1EZiJCKKpZb+gAgp11RaKIhdsLLWIgg2iggRtVEDiiBIGhEvhcnOJmuyu5kZi9UDp3s5xXtCTrhFvUTo0L5BHsgNE3LcpZYRHSQJN2kUeVliqsvFXV5NM/KddImsRb3O24xqxqWoNFyZ2WNyjOcxJ64xQOEe5f08KHMkYipiJRpja4T5lCymWOLJbY4u0e/zqMb8Dr0YRZoBYZnCNqcyVpqMJnRTVseZ3aRXo5zwM+dKhPwdFniacqxNt0klYnaDboNyh197nL3OswgOkLYoLfI5ZbWN8rCVhPWU04f50KIQISyRjRPu8HiC2QF/ckO3GdM5/cukAaFFocIE7jc5l7DbIP7N18Bkg9E2uzknq7wvxFQj3uxjZvMf3OFH4ExgkPCxzugGr7c5//+H6g7GiLf41mPuEF8WWB9wPCGtEOU8jDp0cCGjnZL2ubrI2ifCCwqLrA2Y69GNiP8CeXWF3i7w0tQAAAAASUVORK5CYII="

    def _init_workspace_notebook_close_style(self):
        """Create a closable Notebook tab style with an X element."""
        if getattr(self, '_close_style_initialized', False):
            return
        self._close_style_initialized = True

        style = ttk.Style()

        # Keep image references on self to prevent garbage collection
        try:
            self._img_tab_close = tk.PhotoImage(data=self._CLOSE_ICON_PNG_NORMAL)
            self._img_tab_close_active = tk.PhotoImage(data=self._CLOSE_ICON_PNG_ACTIVE)
            self._img_tab_close_pressed = tk.PhotoImage(data=self._CLOSE_ICON_PNG_PRESSED)
        except Exception:
            return

        try:
            style.element_create(
                'close',
                'image',
                self._img_tab_close,
                ('active', self._img_tab_close_active),
                ('pressed', self._img_tab_close_pressed),
                border=0,
                sticky=''
            )
        except Exception as e:
            self._swallow(e)
        # Layout: label + close button
        try:
            style.layout('Closable.TNotebook.Tab', [
                ('Notebook.tab', {
                    'sticky': 'nswe',
                    'children': [
                        ('Notebook.padding', {
                            'side': 'top',
                            'sticky': 'nswe',
                            'children': [
                                ('Notebook.focus', {
                                    'side': 'top',
                                    'sticky': 'nswe',
                                    'children': [
                                        ('Notebook.label', {'side': 'left', 'sticky': ''}),
                                        ('close', {'side': 'right', 'sticky': ''}),
                                    ]
                                })
                            ]
                        })
                    ]
                })
            ])
        except Exception as e:
            self._swallow(e)

    def _bind_workspace_notebook_close_events(self):
        """Bind close behavior using per-tab images.

        - Hover swaps to active (red) image.
        - Press swaps to pressed image.
        - Release inside close region closes the tab.

        Uses root.bind_all so it works even if ttk doesn't provide tab bboxes.
        Close-region detection:
          (1) Prefer workspace.identify(x,y,'element') when it reports 'image'/'close'
          (2) Fallback to a computed right-edge slice using measured tab widths with visible-strip calibration.
        """
        if getattr(self, '_close_bind_installed', False):
            return
        self._close_bind_installed = True
        self._hover_tab_id = None
        self._pressed_tab_id = None

        # Ensure close images exist
        try:
            if not hasattr(self, '_img_tab_close'):
                self._init_workspace_notebook_close_style()
        except Exception as e:
            self._swallow(e)
        # Apply initial images
        try:
            self.root.after(0, self._ensure_closable_tab_styles)
            self.root.after(150, self._ensure_closable_tab_styles)
        except Exception as e:
            self._swallow(e)
        def _ws_contains(x_root, y_root):
            try:
                w = self.workspace.winfo_containing(int(x_root), int(y_root))
                return (w == self.workspace) or (w is not None and str(w).startswith(str(self.workspace)))
            except Exception:
                return False

        def _to_ws_xy(x_root, y_root):
            try:
                return (int(x_root - self.workspace.winfo_rootx()), int(y_root - self.workspace.winfo_rooty()))
            except Exception:
                return (None, None)

        def _tab_at_xy(x, y):
            try:
                return self._tab_id_at_xy(self.workspace, x, y)
            except Exception:
                return None

        def _set_img(tid, state='normal'):
            st = self._tabs.get(tid, {})
            if tid == getattr(self, '_results_tab_id', None) or st.get('is_results'):
                try:
                    self.workspace.tab(tid, image='', compound='none')
                except Exception as e:
                    self._swallow(e)
                return
            img = getattr(self, '_img_tab_close', None)
            if state == 'active':
                img = getattr(self, '_img_tab_close_active', img)
            elif state == 'pressed':
                img = getattr(self, '_img_tab_close_pressed', img)
            try:
                self.workspace.tab(tid, image=img, compound='right')
            except Exception as e:
                self._swallow(e)

        def _pick_tabstrip_y():
            # Pick a y coordinate that lies within the tab strip.
            for yy in (6, 10, 14, 18, 22):
                try:
                    # Will raise if not in tab strip
                    _ = self.workspace.index(f"@0,{yy}")
                    return yy
                except Exception:
                    continue
            return 10

        def _compute_visible_tab_bounds(y=None, step=2):
            """Compute exact (x0,x1) bounds for *visible* tabs by scanning pixels.

            Uses notebook.index('@x,y') to detect tab index changes, avoiding bbox() and font guesses.
            Returns dict: tab_id -> (x0,x1)
            """
            try:
                tabs = list(self.workspace.tabs())
            except Exception:
                return {}
            if not tabs:
                return {}
            try:
                w = int(self.workspace.winfo_width() or 0)
            except Exception:
                w = 0
            if w <= 0:
                w = 800
            if y is None:
                y = _pick_tabstrip_y()

            bounds = {}
            cur_i = None
            seg_start = None

            def _idx_at(xx):
                try:
                    return int(self.workspace.index(f"@{xx},{y}"))
                except Exception:
                    return None

            # Scan left->right
            x = 0
            last = _idx_at(0)
            cur_i = last
            seg_start = 0
            for x in range(0, w + step, step):
                ii = _idx_at(min(x, w-1))
                if ii != cur_i:
                    # close previous segment
                    if cur_i is not None and 0 <= cur_i < len(tabs):
                        tid = tabs[cur_i]
                        # x is first pixel of new segment; end at x
                        bounds[tid] = (seg_start, x)
                    seg_start = x
                    cur_i = ii

            # Close tail segment
            if cur_i is not None and 0 <= cur_i < len(tabs):
                tid = tabs[cur_i]
                bounds[tid] = (seg_start, w)

            return bounds

        def _get_tab_bounds_cached():
            # Cache bounds to avoid scanning on every mouse move
            try:
                w = int(self.workspace.winfo_width() or 0)
            except Exception:
                w = 0
            if w <= 0:
                w = 800
            y = _pick_tabstrip_y()
            key = (w, y, tuple(self.workspace.tabs()))
            cache = getattr(self, '_ws_tab_bounds_cache', None)
            if cache and cache.get('key') == key:
                return cache.get('bounds', {})
            b = _compute_visible_tab_bounds(y=y, step=2)
            self._ws_tab_bounds_cache = {'key': key, 'bounds': b}
            return b

        def _invalidate_tab_bounds_cache(*_):
            try:
                self._ws_tab_bounds_cache = None
            except Exception as e:
                self._swallow(e)
        # Recompute cache when notebook layout or tabs change
        try:
            self.workspace.bind('<Configure>', _invalidate_tab_bounds_cache, add='+')
            self.workspace.bind('<Map>', _invalidate_tab_bounds_cache, add='+')
            self.workspace.bind('<<NotebookTabChanged>>', _invalidate_tab_bounds_cache, add='+')
        except Exception as e:
            self._swallow(e)

        def _in_close_region(tid, x, y):
            try:
                st = self._tabs.get(tid, {})
                if tid == getattr(self, '_results_tab_id', None) or st.get('is_results'):
                    return False

                # 1) Prefer identify(element) if the theme reports it
                try:
                    elem = self.workspace.identify(x, y, 'element')
                except Exception:
                    elem = ''
                if elem:
                    low = str(elem).lower()
                    if ('image' in low) or ('close' in low):
                        return True

                # 2) Fallback: exact scanned bounds + image width
                bounds = _get_tab_bounds_cached()
                bb = bounds.get(tid)
                if not bb:
                    return False
                _x0, x1 = bb
                try:
                    iw = int(getattr(self, '_img_tab_close', None).width())
                except Exception:
                    iw = 12
                margin = 12
                hit_w = max(18, iw + margin)
                return (x >= (x1 - hit_w))
            except Exception:
                return False

        def _on_motion_all(event):

            try:
                xr, yr = event.x_root, event.y_root
            except Exception:
                return
            prev = getattr(self, '_hover_tab_id', None)
            if not _ws_contains(xr, yr):
                if prev:
                    _set_img(prev, 'normal')
                self._hover_tab_id = None
                return
            x, y = _to_ws_xy(xr, yr)
            if x is None:
                return
            tid = _tab_at_xy(x, y)
            if prev and prev != tid:
                _set_img(prev, 'normal')
            if not tid:
                self._hover_tab_id = None
                return
            st = self._tabs.get(tid, {})
            if tid == getattr(self, '_results_tab_id', None) or st.get('is_results'):
                self._hover_tab_id = None
                return
            if _in_close_region(tid, x, y):
                _set_img(tid, 'active')
                self._hover_tab_id = tid
            else:
                _set_img(tid, 'normal')
                self._hover_tab_id = None

        def _on_press_all(event):
            try:
                xr, yr = event.x_root, event.y_root
            except Exception:
                return
            if not _ws_contains(xr, yr):
                return
            x, y = _to_ws_xy(xr, yr)
            if x is None:
                return
            tid = _tab_at_xy(x, y)
            if not tid:
                return
            st = self._tabs.get(tid, {})
            if tid == getattr(self, '_results_tab_id', None) or st.get('is_results'):
                return
            if _in_close_region(tid, x, y):
                _set_img(tid, 'pressed')
                self._pressed_tab_id = tid
                return 'break'

        def _on_release_all(event):
            tid = getattr(self, '_pressed_tab_id', None)
            self._pressed_tab_id = None
            if not tid:
                return
            try:
                xr, yr = event.x_root, event.y_root
            except Exception:
                _set_img(tid, 'normal')
                return
            x, y = _to_ws_xy(xr, yr)
            if x is None:
                _set_img(tid, 'normal')
                return
            if _in_close_region(tid, x, y):
                _set_img(tid, 'active')
                try:
                    self.close_tab(tid)
                except Exception as e:
                    self._swallow(e)
                return 'break'
            else:
                _set_img(tid, 'normal')

        try:
            self.root.bind_all('<Motion>', _on_motion_all, add='+')
            self.root.bind_all('<ButtonPress-1>', _on_press_all, add='+')
            self.root.bind_all('<ButtonRelease-1>', _on_release_all, add='+')
        except Exception as e:
            self._swallow(e)

    def _close_all_tabs_button_clicked(self):
        """Close All Tabs button handler (standardized confirm)."""
        try:
            return self.close_all_tabs(confirm=True)

        except Exception as e:
            self._swallow(e)
            return

    def _results_is_nonempty(self) -> bool:
        """Fast check: True if Results tab Text widget has any content."""

        try:
            w = self._get_results_text_widget()
        except Exception:
            w = getattr(self, 'result_box', None)

        if not isinstance(w, tk.Text):
            return False

        # O(1) emptiness check
        try:
            return bool(w.compare('end-1c', '>', '1.0'))
        except Exception:
            return False

    def _update_clear_results_button_state(self, force: bool = False):
        """Enable Clear Results UI (button + Edit menu item) only when Results tab is non-empty.
        Uses O(1) Tk index compare and only updates on transitions.
        """
        nonempty = False

        try:
            nonempty = self._results_is_nonempty()
        except Exception:
            nonempty = False

        prev = getattr(self, '_clear_results_enabled', None)

        if (not force) and (prev is not None) and (bool(prev) == bool(nonempty)):
            return

        self._clear_results_enabled = bool(nonempty)

        # Button
        btn = getattr(self, 'clear_button', None)

        if btn is not None:
            try:
                btn.config(state=('normal' if nonempty else 'disabled'))
            except Exception as e:
                self._swallow(e)

        # Edit menu item
        try:
            mnu = getattr(self, '_edit_menu', None)
            idx = getattr(self, '_edit_menu_clear_results_index', None)

            if isinstance(mnu, tk.Menu) and (idx is not None):
                mnu.entryconfig(idx, state=('normal' if nonempty else 'disabled'))

        except Exception as e:
            self._swallow(e)

    def _on_results_modified_for_clear_button(self, event=None):
        """<<Modified>> handler for Results tab to keep Clear UI in sync."""
        try:
            w_evt = getattr(event, 'widget', None)
        except Exception:
            w_evt = None

        try:
            w_res = self._get_results_text_widget()
        except Exception:
            w_res = getattr(self, 'result_box', None)

        if (w_evt is None) or (w_res is None) or (w_evt is not w_res):
            return

        try:
            w_evt.edit_modified(False)
        except Exception:
            pass

        try:
            self._update_clear_results_button_state()
        except Exception as e:
            self._swallow(e)

    def _install_results_clear_button_monitoring(self):
        """Bind Results Text widget so Clear UI reflects non-empty state."""

        try:
            w = self._get_results_text_widget()
        except Exception:
            w = getattr(self, 'result_box', None)

        if not isinstance(w, tk.Text):
            return

        if getattr(self, '_results_clear_btn_widget', None) is w:
            return

        self._results_clear_btn_widget = w

        try:
            w.bind('<<Modified>>', self._on_results_modified_for_clear_button, add='+')
            w.edit_modified(False)
        except Exception as e:
            self._swallow(e)

        try:
            self._update_clear_results_button_state(force=True)
        except Exception as e:
            self._swallow(e)

    def _update_tabs_open_label(self):
        """Update the 'Tabs open' label.
        Counts currently open workspace tabs excluding the fixed Results tab.
        Pinned tabs are included because they remain open on Close all Tabs.
        """
        try:
            var = getattr(self, 'tabs_open_var', None)
            lbl = getattr(self, 'tabs_open_label', None)

            if var is None and lbl is None:
                return

            try:
                n = int(self._count_open_non_results_tabs())

            except Exception:
                try:
                    n = sum(1 for st in (getattr(self, '_tabs', {}) or {}).values() if not st.get('is_results'))

                except Exception:
                    n = 0

            txt = 'Tabs open: %d' % int(n)

            if var is not None:
                try:
                    var.set(txt)
                    return

                except Exception:
                    pass

            if lbl is not None:
                try:
                    lbl.config(text=txt)

                except Exception:
                    pass

        except Exception as e:
            try:
                self._swallow(e)

            except Exception:
                pass

    def _update_close_all_button_state(self):
        """Enable/disable the Close All Tabs button depending on open non-Results tabs."""
        btn = getattr(self, 'close_all_tabs_btn', None)
        if btn is None:
            return
        try:
            any_non_results = any((not s.get('is_results')) and (not s.get('pinned', False)) for s in self._tabs.values())
        except Exception:
            any_non_results = False
        try:
            btn.config(state=('normal' if any_non_results else 'disabled'))
        except Exception as e:
            self._swallow(e)

    # -------------------- Tag configuration --------------------
    def _configure_tags_for_widget(self, w: tk.Text):
        """Configure highlight/header tags on a specific Text widget (tab-aware)."""
        if not isinstance(w, tk.Text):
            return

        # Per-widget defaults
        if not hasattr(w, '_content_version'):
            w._content_version = 0
        if not hasattr(w, '_matches_version'):
            w._matches_version = None

        theme = self.THEMES['dark'] if self.dark_mode else self.THEMES['light']

        # Core highlights
        self._try(w.tag_config, 'highlight', background=theme['findall_bg'], prefix='tag_config.highlight')
        self._try(w.tag_config, 'search_highlight', background=theme['findnext_bg'], prefix='tag_config.search_highlight')
        self._try(w.tag_config, 'occurrence_highlight',
                  background=theme.get('occurrence_bg', '#083fa6'),
                  foreground=theme.get('occurrence_fg', 'white'),
                  prefix='tag_config.occurrence_highlight')

        # Headers
        self._try(w.tag_config, 'file_header',
                  font=('Lucida Console', 10, 'bold'),
                  foreground=theme['file_header_fg'],
                  background=theme['file_header_bg'],
                  prefix='tag_config.file_header')
        self._try(w.tag_config, 'text_header',
                  font=('Lucida Console', 10, 'bold'),
                  foreground=theme['text_header_fg'],
                  background=theme['text_header_bg'],
                  prefix='tag_config.text_header')

        # Custom highlight colors
        colors = getattr(self, 'CUSTOM_HL_COLORS', None)
        if not colors:
            self.CUSTOM_HL_COLORS = [
                ('Coral', '#ff8a80'),
                ('Lilac', '#f3b0ff'),
                ('Pink', '#ffb3c7'),
                ('Peach', '#ffbf8a'),
                ('Orange', '#ffd180'),
                ('Sand', '#f5e6c8'),
                ('Lime', '#e6f56a'),
                ('Mint', '#95e6a4'),
                ('Cyan', '#9fffe0'),
                ('Aqua', '#bff7f0'),
                ('Sky Blue', '#b3d9ff'),
                ('Lavender', '#d0d6ff'),
                ('Light Gray', '#d9d9d9'),
            ]
            colors = self.CUSTOM_HL_COLORS

        for i, (_name, _color) in enumerate(colors, start=1):
            self._try(w.tag_config, f'hl{i}', background=_color, prefix=f'tag_config.hl{i}')

        # Layering
        self._try(w.tag_raise, 'highlight', prefix='tag_raise.highlight')
        self._try(w.tag_raise, 'search_highlight', prefix='tag_raise.search_highlight')

    def _configure_tags(self):
        """Configure tags for Results + every workspace tab."""
        self._try(self._configure_tags_for_widget, getattr(self, 'result_box', None), prefix='_configure_tags.active')
        try:
            for _tid, _st in getattr(self, '_tabs', {}).items():
                _w = _st.get('text')
                if isinstance(_w, tk.Text):
                    self._configure_tags_for_widget(_w)
        except Exception as e:
            self._swallow(e)

    def _apply_notebook_and_menu_style(self):
        """Apply active-tab and menubar highlight colors to match listbox selection tone."""
        theme = self.THEMES['dark'] if self.dark_mode else self.THEMES['light']
        sel_bg = theme.get('listbox_select_bg', '#6d6891')
        sel_fg = theme.get('listbox_select_fg', 'white')

        # ttk Notebook tab styling (active/selected)
        try:
            style = ttk.Style()
            try:
                style.configure('TNotebook', background=theme.get('bg', 'SystemButtonFace'))
            except Exception:
                pass
            style.configure('TNotebook.Tab', foreground=theme.get('fg', 'black'))
            style.map('TNotebook.Tab',
                      background=[('selected', sel_bg), ('active', sel_bg)],
                      foreground=[('selected', sel_fg), ('active', sel_fg)])
        except Exception as e:
            self._swallow(e)

        # Menubar + submenus active color
        try:
            mb = getattr(self, 'menu_bar', None)
            if isinstance(mb, tk.Menu):
                try:
                    mb.configure(activebackground=sel_bg, activeforeground=sel_fg,
                                 bg=theme.get('bg', 'SystemButtonFace'), fg=theme.get('fg', 'black'))
                except Exception:
                    try:
                        mb.configure(activebackground=sel_bg, activeforeground=sel_fg)
                    except Exception:
                        pass
        except Exception as e:
            self._swallow(e)

        try:
            for m in (getattr(self, '_file_menu', None), getattr(self, '_edit_menu', None),
                      getattr(self, '_search_menu', None), getattr(self, '_view_menu', None),
                      getattr(self, '_help_menu', None)):
                if isinstance(m, tk.Menu):
                    try:
                        m.configure(activebackground=sel_bg, activeforeground=sel_fg,
                                    bg=theme.get('bg', 'SystemButtonFace'), fg=theme.get('fg', 'black'))
                    except Exception:
                        try:
                            m.configure(activebackground=sel_bg, activeforeground=sel_fg)
                        except Exception:
                            pass
        except Exception as e:
            self._swallow(e)

    def _apply_theme(self):
        # Apply current theme to widgets and refresh tag colors."""
        theme = self.THEMES['dark'] if self.dark_mode else self.THEMES['light']
        try:
            self._apply_notebook_and_menu_style()
        except Exception as e:
            self._swallow(e)


        # Root and primary frames
        self.root.configure(bg=theme['bg'])
        for frame in (self.main_frame, self.top_frame, getattr(self, 'lb_frame', None), getattr(self, 'ctrl_frame', None)):
            if frame is None:
                continue
            try:
                frame.configure(bg=theme['bg'])
            except Exception as e:
                self._swallow(e)
        # Listbox styling and selection colors
        try:
            self.file_listbox.configure(
                bg=theme['text_bg'],
                fg=theme['text_fg'],
                selectbackground=theme['listbox_select_bg'],
                selectforeground=theme['listbox_select_fg']
            )
        except Exception as e:
            self._swallow(e)
        # Buttons and labels
        for w in (self.toggle_button, self.contents_button, self.clear_button, getattr(self, 'close_all_tabs_btn', None), getattr(self, 'tabs_open_label', None), self.selection_label, self.size_label, self.count_label):
            try:
                w.configure(bg=theme['bg'], fg=theme['fg'])
            except Exception as e:
                self._swallow(e)
        # Results tab
        self.result_box.configure(bg=theme['text_bg'], fg=theme['text_fg'], insertbackground=theme['insert'])
        self.log_box.configure(bg=theme['log_bg'], fg=theme['log_fg'], insertbackground=theme['log_fg'])

        # Line numbers gutter + status bar
        try:
            self.line_numbers.configure(bg=theme['log_bg'], fg=theme['log_fg'])
        except Exception as e:
            self._swallow(e)
        try:
            self.status_label.configure(bg=theme['bg'], fg=theme['fg'])
        except Exception as e:
            self._swallow(e)
        # Progressbar palette
        style = ttk.Style()
        style.configure(
            "Thin.Horizontal.TProgressbar",
            troughcolor=theme['progress_trough'],
            background=theme['progress_bg']
        )

        # Refresh context-menu icons for Find / Find All (if they exist)

        try:
            if hasattr(self, '_find_icon') and self._find_icon:
                self._find_icon.put(theme.get('findnext_bg', '#b7f7b0'), to=(0, 0, 12, 12))

            if hasattr(self, '_findall_icon') and self._findall_icon:
                self._findall_icon.put(theme.get('findall_bg', '#fffd7a'), to=(0, 0, 12, 12))

        except Exception as e:
            self._swallow(e)
        # Refresh tag colors with the new theme
        self._configure_tags()

    def toggle_dark_mode(self):
        #Toggle dark mode and reapply theme styles.
        self.dark_mode = not self.dark_mode
        self._apply_theme()

    # -------------------- Menu & shortcuts --------------------
    def create_menu(self):
        #Create menu bar with File/Search/View/Help entries.
        menu_bar = tk.Menu(self.root)
        self.menu_bar = menu_bar
        # File menu
        file_menu = tk.Menu(menu_bar, tearoff=0)
        self._file_menu = file_menu

        file_menu.add_command(label='🆕 New Tab', command=self.new_tab, accelerator='Ctrl+N')
        file_menu.add_separator()
        file_menu.add_command(label='📁 Open File(s)', command=self.select_files, accelerator='Ctrl+O'); file_menu.add_separator()
        file_menu.add_command(label='📝 Print File Contents', command=self.print_file_contents, accelerator='Ctrl+P'); file_menu.add_separator()

        file_menu.add_command(label='💾 Save', command=self.save_current_tab, accelerator='Ctrl+S')
        try:
            self._file_menu_save_index = file_menu.index('end')
        except Exception:
            self._file_menu_save_index = None

        file_menu.add_command(label='✖ Close Tab', command=self.close_current_tab, accelerator='Ctrl+W')
        try:
            self._file_menu_close_index = file_menu.index('end')
        except Exception:
            self._file_menu_close_index = None

        file_menu.add_command(label='✖ Close All Tabs', command=self.close_all_tabs, accelerator='Ctrl+Shift+W')
        try:
            self._file_menu_closeall_index = file_menu.index('end')
        except Exception:
            self._file_menu_closeall_index = None

        file_menu.add_separator()
        file_menu.add_command(label='📩 Export', command=self.export_results, accelerator='Ctrl+E'); file_menu.add_separator()
        file_menu.add_command(label='❌ Quit', command=self.on_close, accelerator='Ctrl+Q')
        menu_bar.add_cascade(label='File', menu=file_menu, underline=0)

        # Edit menu
        edit_menu = tk.Menu(menu_bar, tearoff=0)
        self._edit_menu = edit_menu
        edit_menu.add_command(label='✂ Cut', command=self.edit_cut, accelerator='Ctrl+X')
        edit_menu.add_command(label='📋 Copy', command=self.edit_copy, accelerator='Ctrl+C')
        edit_menu.add_command(label='📥 Paste', command=self.edit_paste, accelerator='Ctrl+V')
        edit_menu.add_command(label='🔲 Select All', command=self.edit_select_all, accelerator='Ctrl+A')
        edit_menu.add_separator()
        edit_menu.add_command(label='🧹 Clear Results Tab', command=self.clear_text_area, accelerator='Ctrl+L')

        try:
            self._edit_menu_clear_results_index = edit_menu.index('end')

        except Exception:

            self._edit_menu_clear_results_index = None

        menu_bar.add_cascade(label='Edit', menu=edit_menu, underline=0)
        search_menu = tk.Menu(menu_bar, tearoff=0)
        self._search_menu = search_menu
        search_menu.add_command(label='🔍 Find', command=self.open_find_dialog, accelerator='Ctrl+F'); search_menu.add_separator()
        search_menu.add_command(label='⏹️ Cancel Search', command=self.cancel_search, accelerator='Ctrl+Shift+C')
        menu_bar.add_cascade(label='Search', menu=search_menu, underline=0)

        # View menu
        view_menu = tk.Menu(menu_bar, tearoff=0)
        self._view_menu = view_menu
        view_menu.add_command(label='🌒 Dark Mode', command=self.toggle_dark_mode)

        # Developer console debug logging (instrumentation)
        # This toggles ONLY self._debug() console output (it does NOT affect Events logger widget).
        try:
            self._debug_var = tk.BooleanVar(value=bool(getattr(self, 'DEBUG_HIGHLIGHT', False)))
        except Exception:
            # Fallback if tk.BooleanVar fails early (rare): keep a simple bool
            self._debug_var = None

        def _toggle_debug_logging():
            try:
                if self._debug_var is not None:
                    self.DEBUG_HIGHLIGHT = bool(self._debug_var.get())
                else:
                    self.DEBUG_HIGHLIGHT = not bool(getattr(self, 'DEBUG_HIGHLIGHT', False))
            except Exception as e:
                # If something goes wrong, keep app running and provide context in console when possible
                try:
                    self.DEBUG_HIGHLIGHT = bool(getattr(self, 'DEBUG_HIGHLIGHT', False))
                    self._debug(f"[DEBUG_TOGGLE] Failed to toggle debug logging: {type(e).__name__}: {e}")
                except Exception as e:
                    self._swallow(e)
            try:
                self._debug(f"[DEBUG_TOGGLE] Debug console logging is now {'ON' if self.DEBUG_HIGHLIGHT else 'OFF'}")
            except Exception as e:
                self._swallow(e)
        try:
            view_menu.add_checkbutton(label='🐞 Debug Logging', variable=self._debug_var, command=_toggle_debug_logging)
        except Exception:
            view_menu.add_command(label='🐞 Debug Logging', command=_toggle_debug_logging)

        menu_bar.add_cascade(label='View', menu=view_menu, underline=0)

        # Help menu
        help_menu = tk.Menu(menu_bar, tearoff=0)
        self._help_menu = help_menu
        help_menu.add_command(label='❔ About', command=self.show_about)
        menu_bar.add_cascade(label='Help', menu=help_menu, underline=0)

        self.root.config(menu=menu_bar)
        try:
            self._apply_notebook_and_menu_style()
        except Exception as e:
            self._swallow(e)
        try:
            self._update_menu_states_for_tab()
        except Exception as e:
            self._swallow(e)
    # -------------------- Shortcut handlers --------------------
        # Sync Clear Results UI state now that menus exist
        try:
            self._update_clear_results_button_state(force=True)
        except Exception as e:
            self._swallow(e)

    def _shortcut_open_files(self, event=None):
        self.select_files()
        return "break"

    def _shortcut_print_contents(self, event=None):
        self.print_file_contents()
        return "break"

    def _shortcut_export(self, event=None):
        self.export_results()
        return "break"

    def _shortcut_quit(self, event=None):
        self.on_close()
        return 'break'

    def _shortcut_find(self, event=None):
        self.open_find_dialog()
        return "break"

    def _shortcut_clear_text_area(self, event=None):
        # Ctrl+L: no-op when Results tab is empty (menu item can be disabled, but shortcuts still fire).

        try:
            if not self._results_is_nonempty():
                return 'break'
        except Exception:
            return 'break'

        self.clear_text_area()
        return 'break'

    def _get_focus_edit_widget(self):
        """Return the widget that should receive Edit-menu actions (Text/Entry), else None."""

        try:
            w = self.root.focus_get()
        except Exception:
            w = None

        return w if isinstance(w, (tk.Text, tk.Entry)) else None

        # IMPORTANT: Avoid double-action on tk.Entry for keyboard shortcuts.
        # Entry widgets already have class bindings for Ctrl+C/X/V/A; our global bind_all would run
        # afterwards and cause the action to happen twice. For key events, let Tk handle Entry.

    def edit_cut(self, event=None):
        w = self._get_focus_edit_widget()

        if w is None:
            return None

        if event is not None and isinstance(w, tk.Entry):
            return None

        try:
            w.event_generate('<<Cut>>')
        except Exception as e:
            self._swallow(e)

        return 'break'

    def edit_copy(self, event=None):
        w = self._get_focus_edit_widget()

        if w is None:
            return None

        if event is not None and isinstance(w, tk.Entry):
            return None

        try:
            w.event_generate('<<Copy>>')
        except Exception as e:
            self._swallow(e)

        return 'break'

    def edit_paste(self, event=None):
        w = self._get_focus_edit_widget()

        if w is None:
            return None

        if event is not None and isinstance(w, tk.Entry):
            return None

        try:
            w.event_generate('<<Paste>>')
        except Exception as e:
            self._swallow(e)

        return 'break'

    def edit_select_all(self, event=None):
        w = self._get_focus_edit_widget()

        if w is None:
            return None

        if event is not None and isinstance(w, tk.Entry):
            return None

        try:
            if isinstance(w, tk.Text):
                w.tag_add('sel', '1.0', 'end-1c')
                w.mark_set('insert', 'end-1c')
                w.see('insert')
            else:
                w.selection_range(0, 'end')
                w.icursor('end')

        except Exception as e:
            self._swallow(e)
        return 'break'

    def _shortcut_cut(self, event=None):
        return self.edit_cut(event)

    def _shortcut_copy(self, event=None):
        return self.edit_copy(event)

    def _shortcut_paste(self, event=None):
        return self.edit_paste(event)

    def _shortcut_select_all(self, event=None):
        return self.edit_select_all(event)

    def _shortcut_cancel_search(self, event=None):
        self.cancel_search()
        return "break"

    def _shortcut_search_files(self, event=None):
        # Keeps your current behavior (Ctrl+Shift+F)
        # NOTE: If your start_search expects a term, this shortcut may be better mapped to open_find_dialog().
        self.start_search("search_files")
        return "break"

    def _shortcut_search_text_area(self, event=None):
        # Keeps your current behavior (Ctrl+Shift+A)
        self.start_search("search_text_area")
        return "break"

    def _install_text_shortcut_overrides(self):
        # Override Text default Ctrl+O behavior in widgets that can take focus
        for w in (self.result_box, self.log_box):
            w.bind('<Control-o>', self._shortcut_open_files)
            w.bind('<Control-p>', self._shortcut_print_contents)
            w.bind('<Control-Shift-p>', self._shortcut_open_in_tabs)
            w.bind('<Control-Shift-P>', self._shortcut_open_in_tabs)
            w.bind('<Control-s>', self._shortcut_save)
            w.bind('<Control-e>', self._shortcut_export)
            w.bind('<Control-w>', self._shortcut_close_tab)
            w.bind('<Control-Shift-W>', self._shortcut_close_all_tabs)
            w.bind('<Control-Shift-w>', self._shortcut_close_all_tabs)
            w.bind('<Control-q>', self._shortcut_quit)
            w.bind('<Control-f>', self._shortcut_find)
            w.bind('<Control-l>', self._shortcut_clear_text_area)
            w.bind('<Control-x>', self._shortcut_cut)
            w.bind('<Control-X>', self._shortcut_cut)
            w.bind('<Control-c>', self._shortcut_copy)
            w.bind('<Control-C>', self._shortcut_copy)
            w.bind('<Control-v>', self._shortcut_paste)
            w.bind('<Control-V>', self._shortcut_paste)
            w.bind('<Control-a>', self._shortcut_select_all)
            w.bind('<Control-A>', self._shortcut_select_all)
            w.bind('<Control-n>', self.new_tab)
            w.bind('<Control-Prior>', self._shortcut_tab_left)
            w.bind('<Control-Next>', self._shortcut_tab_right)
            w.bind('<Control-Shift-C>', self._shortcut_cancel_search)
            w.bind('<Control-Shift-F>', self._shortcut_search_files)
            w.bind('<Control-Shift-A>', self._shortcut_search_text_area)
        # Apply Ctrl+O override to every workspace tab editor too (prevents Text class binding inserting a newline)
        try:
            for _tid, _st in getattr(self, '_tabs', {}).items():
                _tw = _st.get('text')
                if isinstance(_tw, tk.Text) and _tw not in (self.result_box, self.log_box):
                    _tw.bind('<Control-o>', self._shortcut_open_files)
                    _tw.bind('<Control-O>', self._shortcut_open_files)
        except Exception as e:
            self._swallow(e)

    def bind_shortcuts(self):
        # File-ish shortcuts
        self.root.bind_all('<Control-n>', self.new_tab)
        self.root.bind_all('<Control-o>', self._shortcut_open_files)
        self.root.bind_all('<Control-p>', self._shortcut_print_contents)
        self.root.bind_all('<Control-Shift-p>', self._shortcut_open_in_tabs)
        self.root.bind_all('<Control-Shift-P>', self._shortcut_open_in_tabs)
        self.root.bind_all('<Control-s>', self._shortcut_save)
        self.root.bind_all('<Control-e>', self._shortcut_export)
        self.root.bind_all('<Control-w>', self._shortcut_close_tab)
        self.root.bind_all('<Control-Shift-W>', self._shortcut_close_all_tabs)
        self.root.bind_all('<Control-Shift-w>', self._shortcut_close_all_tabs)
        self.root.bind_all('<Control-q>', self._shortcut_quit)

        # Find / Search
        self.root.bind_all('<Control-f>', self._shortcut_find)
        self.root.bind_all('<Control-Shift-F>', self._shortcut_search_files)
        self.root.bind_all('<Control-Shift-A>', self._shortcut_search_text_area)

        # Cancel / Clear
        self.root.bind_all('<Control-Shift-C>', self._shortcut_cancel_search)
        self.root.bind_all('<Control-l>', self._shortcut_clear_text_area)


        # Edit actions
        self.root.bind_all('<Control-x>', self._shortcut_cut)
        self.root.bind_all('<Control-X>', self._shortcut_cut)
        self.root.bind_all('<Control-c>', self._shortcut_copy)
        self.root.bind_all('<Control-C>', self._shortcut_copy)
        self.root.bind_all('<Control-v>', self._shortcut_paste)
        self.root.bind_all('<Control-V>', self._shortcut_paste)
        self.root.bind_all('<Control-a>', self._shortcut_select_all)
        self.root.bind_all('<Control-A>', self._shortcut_select_all)
        # Workspace tab navigation
        self.root.bind_all('<Control-Prior>', self._shortcut_tab_left)
        self.root.bind_all('<Control-Next>', self._shortcut_tab_right)
    # ---------------- Custom word selection + line selection ----------------
    def _clear_occurrence_highlight(self, event=None, widget=None):
        """Clear token occurrence highlights (Notepad++ style)."""
        w = widget
        if w is None:
            try:
                w = getattr(event, 'widget', None)
            except Exception:
                w = None
        if not isinstance(w, tk.Text):
            w = getattr(self, 'result_box', None)
        if not isinstance(w, tk.Text):
            return
        try:
            w.tag_remove('occurrence_highlight', '1.0', 'end')
        except Exception as e:
            self._swallow(e)
    def _is_single_token_string(self, s: str) -> bool:
        s = (s or '').strip()
        if not s:
            return False
        # single-line only
        if '\n' in s or '\r' in s or ' ' in s or '\t' in s:
            return False
        for ch in s:
            if not self._is_token_char(ch):
                return False
        return True

    def _maybe_update_occurrence_from_selection(self, widget: tk.Text):
        """Update occurrence highlights based on current selection.

        - If OCCURRENCE_WHOLE_TOKEN_ONLY is True: selection must be exactly one token (token chars only).
        - If OCCURRENCE_WHOLE_TOKEN_ONLY is False: any non-empty single-line selection triggers substring occurrence highlighting.

        Multi-line selections are ignored.
        """
        try:
            if not isinstance(widget, tk.Text):
                return
            if not widget.tag_ranges('sel'):
                return
            s = widget.index('sel.first')
            e = widget.index('sel.last')
            if s.split('.')[0] != e.split('.')[0]:
                return
            token = widget.get(s, e)
            if token is None:
                return
            token = str(token)
            if not token.strip():
                return
            max_len = int(getattr(self, 'OCCURRENCE_SUBSTRING_MAX_CHARS', 128) or 128)
            if max_len > 0 and len(token) > max_len:
                return
            whole_only = bool(getattr(self, 'OCCURRENCE_WHOLE_TOKEN_ONLY', True))
            if whole_only and (not self._is_single_token_string(token)):
                return
            line = int(s.split('.')[0])
            self._highlight_token_occurrences(widget, token, line)
        except Exception as e:
            self._swallow(e)
    
    def _bind_occurrence_clear_events(self):
        w = getattr(self, 'result_box', None)
        if isinstance(w, tk.Text):
            self._bind_occurrence_clear_events_for_widget(w)

        # Keep Tabs open counter in sync
        try:
            self._update_tabs_open_label()

        except Exception as e:
            self._swallow(e)

    def _bind_occurrence_clear_events_for_widget(self, w: tk.Text):
        if not isinstance(w, tk.Text):
            return
        if getattr(w, '_occ_clear_bound', False):
            return
        w._occ_clear_bound = True

        w.bind('<Button-1>', lambda e, ww=w: self._clear_occurrence_highlight(event=e, widget=ww), add='+')
        for seq in ('<Up>', '<Down>', '<Left>', '<Right>', '<Prior>', '<Next>', '<Home>', '<End>', '<Control-Home>', '<Control-End>'):
            w.bind(seq, lambda e, ww=w: self._clear_occurrence_highlight(event=e, widget=ww), add='+')
        w.bind('<Control-Left>', lambda e, ww=w: self._clear_occurrence_highlight(event=e, widget=ww), add='+')
        w.bind('<Control-Right>', lambda e, ww=w: self._clear_occurrence_highlight(event=e, widget=ww), add='+')
        w.bind('<Escape>', lambda e, ww=w: self._clear_occurrence_highlight(event=e, widget=ww), add='+')

    def _on_occurrence_selection_change_debounced(self, event=None):
        """Debounce occurrence highlighting triggered by selection changes (mouse drag, Shift+Arrow, etc.)."""
        try:
            if getattr(self, '_occ_sel_after_id', None) is not None:
                try:
                    self.root.after_cancel(self._occ_sel_after_id)
                except Exception as e:
                    self._swallow(e)
                self._occ_sel_after_id = None
        except Exception as e:
            self._swallow(e)
        try:
            delay = int(getattr(self, '_occ_sel_debounce_ms', 80) or 80)
        except Exception:
            delay = 80
        try:
            self._occ_sel_after_id = self.root.after(delay, self._on_occurrence_selection_change)
        except Exception:
            self._occ_sel_after_id = None

    def _on_occurrence_selection_change(self):
        """Apply occurrence highlighting if selection exists; otherwise do nothing."""
        try:
            w = getattr(self, 'result_box', None)
            if not isinstance(w, tk.Text):
                return
            if not w.tag_ranges('sel'):
                return
            if getattr(self, 'DEBUG_HIGHLIGHT', False):
                try:
                    s = w.index('sel.first')
                    e = w.index('sel.last')
                    t = w.get(s, e)
                    self._debug(f"[OCC] selection '{str(t)[:40]}' len={len(str(t))} whole_only={getattr(self, 'OCCURRENCE_WHOLE_TOKEN_ONLY', True)}")
                except Exception as e:
                    self._swallow(e)
            self._maybe_update_occurrence_from_selection(w)
        except Exception as e:
            self._swallow(e)

    def _install_custom_word_selection(self):
        """Override Tk's default double-click word selection.

        Tokens are made of alphanumerics plus TOKEN_EXTRA_CHARS.
        Default excludes ':' per user preference.
        """
        self.TOKEN_EXTRA_CHARS = "_-"  # underscore, dot, hyphen
        for w in (getattr(self, 'result_box', None), getattr(self, 'log_box', None)):
            if isinstance(w, tk.Text):
                w.bind('<Double-Button-1>', lambda e, widget=w: self._select_token_on_double_click(e, widget))
                w.bind('<Triple-Button-1>', lambda e, widget=w: self._select_line_on_triple_click(e, widget))
            w.bind('<Control-Shift-Left>',  lambda e, widget=w: self._kbd_token_select_left(e, widget))
            w.bind('<Control-Shift-Right>', lambda e, widget=w: self._kbd_token_select_right(e, widget))
            w.bind('<Control-Left>', lambda e, widget=w: self._kbd_token_move_left(e, widget), add='+')
            w.bind('<Control-Right>', lambda e, widget=w: self._kbd_token_move_right(e, widget), add='+')

    def _is_token_char(self, ch: str) -> bool:
        extras = getattr(self, 'TOKEN_EXTRA_CHARS', '_')
        return ch.isalnum() or ch in extras

    def _highlight_token_occurrences(self, widget: tk.Text, token: str, center_line: int):
        """Highlight occurrences of token within +/- OCCURRENCE_WINDOW_LINES around center_line.

        Modes:
        - OCCURRENCE_WHOLE_TOKEN_ONLY = True  -> whole-token matches only (token boundaries)
        - OCCURRENCE_WHOLE_TOKEN_ONLY = False -> substring matches allowed (token inside longer strings)

        Implementation is bounded to a line window and runs as a single compute per selection.
        """
        try:
            widget.tag_remove('occurrence_highlight', '1.0', 'end')
        except Exception as e:
            self._swallow(e)
        token = (token or '').strip()
        if not token:
            return
        if '\n' in token or '\r' in token or ' ' in token or '\t' in token:
            return

        try:
            total_lines = int(widget.index('end-1c').split('.')[0])
        except Exception:
            total_lines = 1

        rng = int(getattr(self, 'OCCURRENCE_WINDOW_LINES', 500) or 500)
        min_line = max(1, int(center_line) - rng)
        max_line = min(total_lines, int(center_line) + rng)

        whole_only = bool(getattr(self, 'OCCURRENCE_WHOLE_TOKEN_ONLY', True))

        try:
            block = widget.get(f'{min_line}.0', f'{max_line}.end')
        except Exception:
            return

        rx = None
        if whole_only:
            extras = getattr(self, 'TOKEN_EXTRA_CHARS', '_-')
            char_class = r'A-Za-z0-9' + re.escape(extras)
            rx = re.compile(rf'(?<![{char_class}]){re.escape(token)}(?![{char_class}])')

        try:
            lines = block.splitlines(True)
            tok_len = len(token)
            for off, ln in enumerate(range(min_line, max_line + 1)):
                if off >= len(lines):
                    break
                t = lines[off].rstrip('\r\n')
                if not t:
                    continue
                if whole_only and rx is not None:
                    for mm in rx.finditer(t):
                        c0, c1 = mm.start(), mm.end()
                        widget.tag_add('occurrence_highlight', f'{ln}.{c0}', f'{ln}.{c1}')
                else:
                    start = 0
                    while True:
                        i = t.find(token, start)
                        if i == -1:
                            break
                        widget.tag_add('occurrence_highlight', f'{ln}.{i}', f'{ln}.{i + tok_len}')
                        start = i + tok_len
        except Exception:
            return

    def _select_token_on_double_click(self, event, widget: tk.Text):
        try:
            idx = widget.index(f"@{event.x},{event.y}")
            line_s, col_s = idx.split('.')
            line = int(line_s)
            col = int(col_s)
            line_text = widget.get(f"{line}.0", f"{line}.end")
            if not line_text:
                return
            if col >= len(line_text):
                col = max(0, len(line_text) - 1)
            if not self._is_token_char(line_text[col]) and col > 0 and self._is_token_char(line_text[col - 1]):
                col -= 1
            if not self._is_token_char(line_text[col]):
                return
            left = col
            while left > 0 and self._is_token_char(line_text[left - 1]):
                left -= 1
            right = col
            while right < len(line_text) and self._is_token_char(line_text[right]):
                right += 1
            if right <= left:
                return
            start = f"{line}.{left}"
            end = f"{line}.{right}"
            widget.tag_remove('sel', '1.0', 'end')
            widget.tag_add('sel', start, end)
            widget.mark_set('insert', end)
            widget.see(start)
            # Highlight nearby occurrences of the selected token (bounded window)
            try:
                token = widget.get(start, end)
                self._highlight_token_occurrences(widget, token, line)
            except Exception as e:
                self._swallow(e)
            return 'break'
        except tk.TclError:
            return

    def _select_line_on_triple_click(self, event, widget: tk.Text):
        """Triple-click selects the entire row (line)."""
        try:
            idx = widget.index(f"@{event.x},{event.y}")
            line = idx.split('.')[0]
            start = f"{line}.0"
            end = f"{line}.end"
            widget.tag_remove('sel', '1.0', 'end')
            widget.tag_add('sel', start, end)
            widget.mark_set('insert', end)
            widget.see(start)
            return 'break'
        except tk.TclError:
            return

    # ----- Keyboard token selection (Ctrl+Shift+Left/Right) -----
    def _is_kbd_token_char(self, ch: str) -> bool:
        'Token chars for keyboard selection: alnum plus underscore and hyphen.'
        return ch.isalnum() or ch in '_-'

    def _kbd_token_select(self, event, widget: tk.Text, direction: str):
        'Extend selection by token to the left/right using token rules.'
        try:
            if not isinstance(widget, tk.Text):
                return 'break'

            # Anchor handling (persist across repeated Ctrl+Shift presses)
            if not widget.tag_ranges('sel'):
                anchor = widget.index('insert')
                setattr(widget, '_kbd_anchor', anchor)
            else:
                anchor = getattr(widget, '_kbd_anchor', widget.index('sel.first'))

            cur = widget.index('insert')
            line_s, col_s = cur.split('.')
            line = int(line_s)
            col = int(col_s)

            def get_line_text(ln: int) -> str:
                return widget.get(f'{ln}.0', f'{ln}.end')

            if direction == 'right':
                ln_text = get_line_text(line)
                # Skip separators to the right
                while True:
                    if col >= len(ln_text):
                        nxt = widget.index(f'{line+1}.0')
                        if widget.compare(nxt, '>=', 'end-1c'):
                            break
                        line += 1
                        col = 0
                        ln_text = get_line_text(line)
                        continue
                    if self._is_kbd_token_char(ln_text[col]):
                        break
                    col += 1
                # Skip token chars to token end
                while col < len(ln_text) and self._is_kbd_token_char(ln_text[col]):
                    col += 1
                new_idx = f'{line}.{col}'
            else:
                ln_text = get_line_text(line)
                if col > 0:
                    col -= 1
                else:
                    if line > 1:
                        line -= 1
                        ln_text = get_line_text(line)
                        col = len(ln_text) - 1

                # Skip separators to the left
                while True:
                    if col < 0:
                        if line <= 1:
                            col = 0
                            break
                        line -= 1
                        ln_text = get_line_text(line)
                        col = len(ln_text) - 1
                        continue
                    ch = ln_text[col] if 0 <= col < len(ln_text) else ''
                    if ch and self._is_kbd_token_char(ch):
                        break
                    col -= 1
                # Skip token chars to token start
                while col > 0 and self._is_kbd_token_char(ln_text[col-1]):
                    col -= 1
                new_idx = f'{line}.{col}'

            # Apply selection
            widget.tag_remove('sel', '1.0', 'end')
            if widget.compare(anchor, '<=', new_idx):
                widget.tag_add('sel', anchor, new_idx)
            else:
                widget.tag_add('sel', new_idx, anchor)

            widget.mark_set('insert', new_idx)
            widget.see(new_idx)

            try:
                self._update_status_bar()
            except Exception as e:
                self._swallow(e)
            # IMPORTANT: always compute/update occurrence highlights on successful token-select
            try:
                self._maybe_update_occurrence_from_selection(widget)
            except Exception as e:
                self._swallow(e)
            return 'break'
        except Exception:
            # If something went wrong, still try to update/clear occurrences based on current selection
            try:
                self._maybe_update_occurrence_from_selection(widget)
            except Exception as e:
                self._swallow(e)
            return 'break'

    def _kbd_token_select_left(self, event, widget: tk.Text):
        return self._kbd_token_select(event, widget, 'left')

    def _kbd_token_select_right(self, event, widget: tk.Text):
        return self._kbd_token_select(event, widget, 'right')

    # ----- Keyboard token navigation (Ctrl+Left/Right) -----
    def _kbd_token_move(self, event, widget: tk.Text, direction: str):
     """Move caret by token to the left/right using token rules (no selection).

     Token chars for navigation: alnum plus underscore and hyphen.
     This overrides Tk's default Ctrl+Arrow word navigation which can skip too far
     across special-character-concatenated strings.
     """
     try:
      if not isinstance(widget, tk.Text):
       return 'break'

      # Clear any selection (navigation should not extend selection)
      try:
       widget.tag_remove('sel', '1.0', 'end')
       try:
           self._clear_occurrence_highlight(widget=widget)
       except Exception as e:
           self._swallow(e)
      except Exception as e:
       self._swallow(e)
      # Reset stored anchor used by Ctrl+Shift token selection
      try:
       if hasattr(widget, '_kbd_anchor'):
        delattr(widget, '_kbd_anchor')
      except Exception as e:
       self._swallow(e)
      cur = widget.index('insert')
      line_s, col_s = cur.split('.')
      line = int(line_s)
      col = int(col_s)

      def get_line_text(ln: int) -> str:
       return widget.get(f'{ln}.0', f'{ln}.end')

      if direction == 'left':
       while True:
        ln_text = get_line_text(line)

        # If at start of line, jump to end of previous line (if any)
        if col == 0:
         if line <= 1:
          widget.mark_set('insert', '1.0')
          widget.see('insert')
          try:
           self._update_status_bar()
          except Exception as e:
           self._swallow(e)
          return 'break'
         line -= 1
         ln_text = get_line_text(line)
         col = len(ln_text)
         continue

        # Step 1: skip separators to the left
        while col > 0 and not self._is_kbd_token_char(ln_text[col-1]):
         col -= 1
         if col == 0:
          break

        # Step 2: skip token chars to the left (land at token start)
        while col > 0 and self._is_kbd_token_char(ln_text[col-1]):
         col -= 1

        new_idx = f'{line}.{col}'
        widget.mark_set('insert', new_idx)
        widget.see(new_idx)
        try:
         self._update_status_bar()
        except Exception as e:
         self._swallow(e)
        return 'break'

      else:  # right
       while True:
        ln_text = get_line_text(line)
        n = len(ln_text)

        # If at end of line, jump to start of next line (if any)
        if col >= n:
         nxt = widget.index(f'{line+1}.0')
         if widget.compare(nxt, '>=', 'end-1c'):
          widget.mark_set('insert', f'{line}.{n}')
          widget.see('insert')
          try:
           self._update_status_bar()
          except Exception as e:
           self._swallow(e)
          return 'break'
         line += 1
         col = 0
         continue

        # Step 1: if inside token, skip to token end
        while col < n and self._is_kbd_token_char(ln_text[col]):
         col += 1
         if col >= n:
          break

        # Step 2: skip separators to next token start
        while col < n and not self._is_kbd_token_char(ln_text[col]):
         col += 1
         if col >= n:
          break

        new_idx = f'{line}.{col}'
        widget.mark_set('insert', new_idx)
        widget.see(new_idx)
        try:
         self._update_status_bar()
        except Exception as e:
         self._swallow(e)
        return 'break'

     except Exception:
      return 'break'

    def _kbd_token_move_left(self, event, widget: tk.Text):
     return self._kbd_token_move(event, widget, 'left')

    def _kbd_token_move_right(self, event, widget: tk.Text):
     return self._kbd_token_move(event, widget, 'right')

    # ---------------- Undo/Redo (Ctrl+Z, Ctrl+Shift+Z) ----------------
    def _install_undo_redo_bindings(self):
        try:
            self.root.bind_all('<Control-z>', self._shortcut_undo)
            self.root.bind_all('<Control-Z>', self._shortcut_undo)
            self.root.bind_all('<Control-Shift-z>', self._shortcut_redo)
            self.root.bind_all('<Control-Shift-Z>', self._shortcut_redo)
        except Exception as e:
            self._swallow(e)
        try:
            self.result_box.bind('<Control-z>', self._shortcut_undo)
            self.result_box.bind('<Control-Z>', self._shortcut_undo)
            self.result_box.bind('<Control-Shift-z>', self._shortcut_redo)
            self.result_box.bind('<Control-Shift-Z>', self._shortcut_redo)
        except Exception as e:
            self._swallow(e)
    def _shortcut_undo(self, event=None):
        try:
            w = self.root.focus_get()
            if isinstance(w, tk.Text):
                w.edit_undo()
            return 'break'
        except Exception:
            return 'break'

    def _shortcut_redo(self, event=None):
        try:
            w = self.root.focus_get()
            if isinstance(w, tk.Text):
                w.edit_redo()
            return 'break'
        except Exception:
            return 'break'

    # ---------------- Status bar + line numbers ----------------
    def _install_status_and_linenum_bindings(self):
        for seq in ('<KeyRelease>', '<ButtonRelease-1>', '<B1-Motion>', '<FocusIn>'):
            self.result_box.bind(seq, self._update_status_bar, add='+')
        for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>', '<Configure>'):
            self.result_box.bind(seq, self._update_linenumbers_debounced, add='+')
        # Gutter robustness: update line numbers on text mutations (Enter/Delete/Paste/Undo/Redo)
        for seq in ('<KeyRelease>', '<Return>', '<BackSpace>', '<Delete>', '<<Paste>>', '<<Cut>>', '<<Undo>>', '<<Redo>>'):
            self.result_box.bind(seq, self._update_linenumbers_debounced, add='+')
        # Occurrence highlighting on selection changes (mouse drag, Shift+Arrow, etc.)
        for seq in ('<KeyRelease>', '<ButtonRelease-1>', '<B1-Motion>'):
            try:
                self.result_box.bind(seq, self._on_occurrence_selection_change_debounced, add='+')
            except Exception as e:
                self._swallow(e)
        self.root.after(50, self._update_status_bar)
        self.root.after(50, self._refresh_line_numbers)

    def _update_status_bar(self, event=None):
        try:
            idx = self.result_box.index('insert')
            ln, col = idx.split('.')
            sel_len = 0
            if self.result_box.tag_ranges('sel'):
                s = self.result_box.index('sel.first')
                e = self.result_box.index('sel.last')
                try:
                    sel_len = int(self.result_box.count(s, e, 'chars')[0])
                except Exception:
                    sel_len = len(self.result_box.get(s, e))
            total_lines = int(self.result_box.index('end-1c').split('.')[0])
            ln_i = int(ln)
            col_i = int(col)
            # Comma separators for total lines, current line, and selection length
            self.status_var.set(f"Lines {total_lines:,}   |   Ln {ln_i:,}, Col {col_i}   |   Sel {sel_len:,}")
        except Exception as e:
            self._swallow(e)
    def _update_linenumbers_debounced(self, event=None):
        try:
            if getattr(self, '_ln_after', None):
                self.root.after_cancel(self._ln_after)
        except Exception as e:
            self._swallow(e)
        self._ln_after = self.root.after(60, self._refresh_line_numbers)

    def _refresh_line_numbers(self, event=None):
        if not hasattr(self, 'line_numbers'):
            return
        try:
            first = int(self.result_box.index('@0,0').split('.')[0])
            last = int(self.result_box.index(f"@0,{self.result_box.winfo_height()}").split('.')[0])
            if last < first:
                last = first
            total_lines = int(self.result_box.index('end-1c').split('.')[0])
            # Gutter width: dynamic, min 4 digits and max 9 digits
            width = max(4, min(9, len(str(total_lines))))
            try:
                self.line_numbers.configure(width=width)
            except Exception as e:
                self._swallow(e)
            nums = "\n".join(str(i).rjust(width) for i in range(first, last + 1))
            self.line_numbers.config(state='normal')
            self.line_numbers.delete('1.0', 'end')
            self.line_numbers.insert('1.0', nums)
            self.line_numbers.config(state='disabled')
            try:
                self.line_numbers.yview_moveto(0.0)
            except Exception as e:
                self._swallow(e)
            # Do not scroll the gutter by fraction; it only contains the visible line numbers.
        except Exception as e:
            self._swallow(e)
    # ---------------- Text-area context menu + highlight tools ----------------
    def _install_text_area_context_menu(self):
        self._text_ctx_widget = None
        self._text_ctx_index = None

        self.text_ctx_menu = tk.Menu(self.root, tearoff=0)
        self.text_ctx_menu.add_command(label='Cut', command=self._ctx_cut)
        self.text_ctx_menu.add_command(label='Copy', command=self._ctx_copy)
        self.text_ctx_menu.add_command(label='Paste', command=self._ctx_paste)

        self.text_ctx_menu.add_separator()
        self.text_ctx_menu.add_command(label='Undo', command=self._ctx_undo)
        self.text_ctx_menu.add_command(label='Redo', command=self._ctx_redo)
        self.text_ctx_menu.add_separator()

        self._hl_one_menu = tk.Menu(self.text_ctx_menu, tearoff=0)
        self._hl_all_menu = tk.Menu(self.text_ctx_menu, tearoff=0)
        self._hl_clear_menu = tk.Menu(self.text_ctx_menu, tearoff=0)

        self._hl_icons = []
        colors = getattr(self, 'CUSTOM_HL_COLORS', []) or [(f'Color {i}', '#ffffcc') for i in range(1, 11)]
        for i, (name, color) in enumerate(colors, start=1):
            icon = tk.PhotoImage(width=12, height=12)
            icon.put(color, to=(0, 0, 12, 12))
            self._hl_icons.append(icon)
            self._hl_one_menu.add_command(label=name, image=icon, compound='left', command=lambda n=i: self._ctx_highlight_one(n))
            self._hl_all_menu.add_command(label=name, image=icon, compound='left', command=lambda n=i: self._ctx_highlight_all(n))
            self._hl_clear_menu.add_command(label=name, image=icon, compound='left', command=lambda n=i: self._ctx_clear_highlight(n))

        self._hl_clear_menu.insert_command(0, label='All highlight colors', command=self._ctx_clear_all_highlights)
        self._hl_clear_menu.insert_separator(1)

        # --- Clear Highlight: add Find/Find All clear actions (italic + color-coded) ---
        try:
            base_font = tkfont.nametofont('TkMenuFont')
            italic_font = base_font.copy()
            italic_font.configure(slant='italic')
            self._menu_italic_font = italic_font
        except Exception:
            self._menu_italic_font = ('TkMenuFont', 9, 'italic')

        theme = self.THEMES['dark'] if self.dark_mode else self.THEMES['light']
        find_color = theme.get('findnext_bg', '#b7f7b0')
        findall_color = theme.get('findall_bg', '#fffd7a')
        self._find_icon = tk.PhotoImage(width=12, height=12)
        self._find_icon.put(find_color, to=(0, 0, 12, 12))
        self._findall_icon = tk.PhotoImage(width=12, height=12)
        self._findall_icon.put(findall_color, to=(0, 0, 12, 12))
        try:
            self._hl_icons.append(self._find_icon)
            self._hl_icons.append(self._findall_icon)
        except Exception as e:
            self._swallow(e)
        self._hl_clear_menu.add_separator()
        self._hl_clear_menu.add_command(label='Find', image=self._find_icon, compound='left', font=self._menu_italic_font, command=self._ctx_clear_find_highlight)
        self._hl_clear_menu.add_command(label='Find All', image=self._findall_icon, compound='left', font=self._menu_italic_font, command=self._ctx_clear_findall_highlight)

        self.text_ctx_menu.add_cascade(label='Highlight One', menu=self._hl_one_menu)
        self.text_ctx_menu.add_cascade(label='Highlight All', menu=self._hl_all_menu)
        self.text_ctx_menu.add_cascade(label='Clear Highlight', menu=self._hl_clear_menu)

        self.result_box.bind('<Button-3>', self._show_text_context_menu)
        self.result_box.bind('<Control-Button-1>', self._show_text_context_menu)
        # Keyboard context-menu key
        self.result_box.bind('<App>', lambda e, w=self.result_box: self._show_text_context_menu_keyboard(e, w))
        self.result_box.bind('<Menu>', lambda e, w=self.result_box: self._show_text_context_menu_keyboard(e, w))
        # Also enable on log box
        self.log_box.bind('<Button-3>', self._show_text_context_menu)
        self.log_box.bind('<Control-Button-1>', self._show_text_context_menu)
        self.log_box.bind('<App>', lambda e, w=self.log_box: self._show_text_context_menu_keyboard(e, w))
        self.log_box.bind('<Menu>', lambda e, w=self.log_box: self._show_text_context_menu_keyboard(e, w))

    def _show_text_context_menu_keyboard(self, event, widget=None):
        'Show the text-area context menu from keyboard (Menu/Application key).'
        try:
            w = widget or getattr(event, 'widget', None)
            if not isinstance(w, tk.Text):
                return
            self._text_ctx_widget = w
            try:
                self._text_ctx_index = w.index('insert')
            except Exception:
                self._text_ctx_index = '1.0'
            try:
                w.mark_set('insert', self._text_ctx_index)
                w.focus_set()
            except Exception as e:
                self._swallow(e)
            try:
                bbox = w.bbox('insert')
            except Exception:
                bbox = None
            if bbox:
                x, y, width, height = bbox
                x_root = w.winfo_rootx() + x
                y_root = w.winfo_rooty() + y + height
            else:
                x_root = w.winfo_rootx() + 10
                y_root = w.winfo_rooty() + 10
            has_sel = bool(w.tag_ranges('sel'))
            self.text_ctx_menu.entryconfig('Cut', state=('normal' if has_sel else 'disabled'))
            try:
                can_undo = bool(w.edit_canundo())
            except Exception:
                can_undo = True
            try:
                can_redo = bool(w.edit_canredo())
            except Exception:
                can_redo = True
            self.text_ctx_menu.entryconfig('Undo', state=('normal' if can_undo else 'disabled'))
            self.text_ctx_menu.entryconfig('Redo', state=('normal' if can_redo else 'disabled'))
            self.text_ctx_menu.tk_popup(x_root, y_root)
        finally:
            try:
                self.text_ctx_menu.grab_release()
            except Exception as e:
                self._swallow(e)

    def _show_text_context_menu(self, event):
        try:
            self._text_ctx_widget = event.widget
            self._text_ctx_index = self._text_ctx_widget.index(f"@{event.x},{event.y}")
            self._text_ctx_widget.mark_set('insert', self._text_ctx_index)
            self._text_ctx_widget.focus_set()

            has_sel = bool(self._text_ctx_widget.tag_ranges('sel'))
            self.text_ctx_menu.entryconfig('Cut', state=('normal' if has_sel else 'disabled'))
            try:
                can_undo = bool(self._text_ctx_widget.edit_canundo())
            except Exception:
                can_undo = True
            try:
                can_redo = bool(self._text_ctx_widget.edit_canredo())
            except Exception:
                can_redo = True
            self.text_ctx_menu.entryconfig('Undo', state=('normal' if can_undo else 'disabled'))
            self.text_ctx_menu.entryconfig('Redo', state=('normal' if can_redo else 'disabled'))

            self.text_ctx_menu.tk_popup(event.x_root, event.y_root)
        finally:
            try:
                self.text_ctx_menu.grab_release()
            except Exception as e:
                self._swallow(e)

    def _ctx_cut(self):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                w.event_generate('<<Cut>>')
            except Exception as e:
                self._swallow(e)

    def _ctx_copy(self):
        w = self._text_ctx_widget
        if not isinstance(w, tk.Text):
            return
        try:
            if not w.tag_ranges('sel'):
                rng = self._get_token_range_at_index(w, self._text_ctx_index)
                if rng:
                    s, e = rng
                    w.tag_add('sel', s, e)
            w.event_generate('<<Copy>>')
        except Exception as e:
            self._swallow(e)

    def _ctx_paste(self):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                w.event_generate('<<Paste>>')
            except Exception as e:
                self._swallow(e)

    def _ctx_undo(self):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                w.edit_undo()
            except Exception as e:
                self._swallow(e)

    def _ctx_redo(self):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                w.edit_redo()
            except Exception as e:
                self._swallow(e)

    def _get_token_range_at_index(self, widget: tk.Text, idx: str):
        try:
            line_s, col_s = idx.split('.')
            line = int(line_s)
            col = int(col_s)
            line_text = widget.get(f"{line}.0", f"{line}.end")
            if not line_text:
                return None
            if col >= len(line_text):
                col = max(0, len(line_text) - 1)
            if not self._is_token_char(line_text[col]) and col > 0 and self._is_token_char(line_text[col - 1]):
                col -= 1
            if not self._is_token_char(line_text[col]):
                return None
            left = col
            while left > 0 and self._is_token_char(line_text[left - 1]):
                left -= 1
            right = col
            while right < len(line_text) and self._is_token_char(line_text[right]):
                right += 1
            return (f"{line}.{left}", f"{line}.{right}")
        except Exception:
            return None

    def _get_selection_or_token(self, widget: tk.Text):
        try:
            if widget.tag_ranges('sel'):
                s = widget.index('sel.first')
                e = widget.index('sel.last')
                t = widget.get(s, e)
                return t, s, e
            rng = self._get_token_range_at_index(widget, self._text_ctx_index or widget.index('insert'))
            if not rng:
                return '', None, None
            s, e = rng
            t = widget.get(s, e)
            return t, s, e
        except Exception:
            return '', None, None

    def _ctx_highlight_one(self, color_idx: int):
        w = self._text_ctx_widget
        if not isinstance(w, tk.Text):
            return
        t, s, e = self._get_selection_or_token(w)
        if not t or not s or not e:
            return
        tag = f"hl{int(color_idx)}"
        try:
            w.tag_add(tag, s, e)
            try:
                w.tag_raise('search_highlight')
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            self._swallow(e)

    def _ctx_highlight_all(self, color_idx: int):
        w = self._text_ctx_widget
        if not isinstance(w, tk.Text):
            return
        t, s, e = self._get_selection_or_token(w)
        if not t:
            return
        tag = f"hl{int(color_idx)}"
        try:
            start = '1.0'
            while True:
                pos = w.search(t, start, stopindex='end', nocase=False, regexp=False)
                if not pos:
                    break
                end = f"{pos}+{len(t)}c"
                w.tag_add(tag, pos, end)
                start = end
            try:
                w.tag_raise('search_highlight')
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            self._swallow(e)

    def _ctx_clear_highlight(self, color_idx: int):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                w.tag_remove(f"hl{int(color_idx)}", '1.0', 'end')
            except Exception as e:
                self._swallow(e)

    def _ctx_clear_all_highlights(self):
        w = self._text_ctx_widget
        if isinstance(w, tk.Text):
            try:
                for i in range(1, 11):
                    w.tag_remove(f"hl{i}", '1.0', 'end')
            except Exception as e:
                self._swallow(e)
            # Also clear Find (green) and Find All (yellow) highlights
            try:
                self._ctx_clear_find_highlight()
            except Exception as e:
                self._swallow(e)
            try:
                self._ctx_clear_findall_highlight()
            except Exception as e:
                self._swallow(e)

    def _ctx_clear_find_highlight(self):
        """Clear Find/Find Next highlight (search_highlight tag).
        This removes the green Find highlight and resets Find state.
        """
        w = self._text_ctx_widget

        if isinstance(w, tk.Text):
            try:
                w.tag_remove('search_highlight', '1.0', 'end')
            except Exception as e:
                self._swallow(e)
        for a in ('_last_find_start', '_last_find_end'):
            if hasattr(w, a):
                try:
                    delattr(w, a)
                except Exception as e:
                    self._swallow(e)
        if hasattr(self, 'find_button'):
            try:
                self.find_button.config(text='Find')
            except Exception as e:
                self._swallow(e)

    def _ctx_clear_findall_highlight(self):
        """Clear Find All highlights (highlight tag) and disable repainting of visible highlights.
        Find All uses precomputed match arrays; we clear both the tag and the arrays so highlights do not come back
        on scroll/resize.
        """
        w = self._text_ctx_widget

        if isinstance(w, tk.Text):
            try:
                w.tag_remove('highlight', '1.0', 'end')
            except Exception as e:
                self._swallow(e)
        for attr in ('_match_lines', '_match_cols_s', '_match_cols_e', '_total_lines', '_matches_version'):
            if hasattr(w, attr):
                try:
                    delattr(w, attr)
                except Exception as e:
                    self._swallow(e)

    # ------------ Scrolling / highlighting lifecycle ------------
    def _on_vscroll(self, *args):
        # Scrollbar - move Text view and schedule highlight refresh.
        try:
            self.result_box.yview(*args)
            # Gutter content is regenerated for the visible range; no direct yview sync needed.
            self._update_linenumbers_debounced()
            if not getattr(self, "_suppress_scroll_cb", False):
                self._debounced_update()
        except Exception as e:
            self._debug(f"[SCROLLBAR] _on_vscroll error: {e}")

    def _on_yscroll(self, *args):
        # Text view changed - update scrollbar and schedule highlight.
        try:
            if hasattr(self, "v_scroll"):
                self.v_scroll.set(*args)
            # Gutter content is regenerated for the visible range; no direct yview sync needed.
            self._update_linenumbers_debounced()
            if not getattr(self, "_suppress_scroll_cb", False):
                self._debounced_update()
        except Exception as e:
            self._debug(f"[SCROLLBAR] _on_yscroll error: {e}")

    # ------------ Scrolling / highlighting lifecycle (tab-aware) ------------
    def bind_highlight_events_once(self):
        """Bind repaint triggers for the active editor."""
        w = getattr(self, 'result_box', None)
        if isinstance(w, tk.Text):
            self._bind_highlight_events_for_widget(w)

    def _bind_highlight_events_for_widget(self, w: tk.Text):
        if not isinstance(w, tk.Text):
            return
        if getattr(w, '_hl_events_bound', False):
            return
        w._hl_events_bound = True

        # defaults
        if not hasattr(w, '_debounce_id'):
            w._debounce_id = None
        if not hasattr(w, '_highlight_gen'):
            w._highlight_gen = 0
        if not hasattr(w, '_highlight_running'):
            w._highlight_running = False

        w.bind('<MouseWheel>', lambda e, ww=w: self._debounced_update(e, widget=ww), add='+')
        w.bind('<Button-4>', lambda e, ww=w: self._debounced_update(e, widget=ww), add='+')
        w.bind('<Button-5>', lambda e, ww=w: self._debounced_update(e, widget=ww), add='+')
        w.bind('<Configure>', lambda e, ww=w: self._debounced_update(e, widget=ww), add='+')

        for seq in ('<Up>', '<Down>', '<Prior>', '<Next>', '<Home>', '<End>', '<Control-Home>', '<Control-End>'):
            w.bind(seq, lambda e, ww=w: self._debounced_update(e, widget=ww), add='+')

    def _debounced_update(self, event=None, widget=None):
        w = widget
        if w is None and event is not None:
            w = getattr(event, 'widget', None)
        if not isinstance(w, tk.Text):
            w = getattr(self, 'result_box', None)
        if not isinstance(w, tk.Text):
            return

        aid = getattr(w, '_debounce_id', None)
        if aid:
            self._try(self.root.after_cancel, aid, prefix='after_cancel.debounce')
            w._debounce_id = None

        w._highlight_gen = int(getattr(w, '_highlight_gen', 0) or 0) + 1
        delay = int(getattr(self, '_debounce_delay', 100) or 100)
        w._debounce_id = self._try(self.root.after, delay, lambda ww=w: self.update_visible_highlights(widget=ww),
                                   prefix='after.debounce', default=None)

    def update_visible_highlights(self, widget=None):
        w = widget or getattr(self, 'result_box', None)
        if not isinstance(w, tk.Text):
            return

        ml = getattr(w, '_match_lines', None)
        cs = getattr(w, '_match_cols_s', None)
        ce = getattr(w, '_match_cols_e', None)
        if not (isinstance(ml, list) and isinstance(cs, list) and isinstance(ce, list)):
            return

        if getattr(w, '_matches_version', None) != getattr(w, '_content_version', None):
            return

        if getattr(w, '_highlight_running', False):
            w._highlight_gen = int(getattr(w, '_highlight_gen', 0) or 0) + 1
            self._try(self.root.after, 50, lambda ww=w: self.update_visible_highlights(widget=ww), prefix='after.hl.resched')
            return

        w._highlight_running = True
        local_gen = int(getattr(w, '_highlight_gen', 0) or 0)

        try:
            vis_start = int(w.index('@0,0').split('.')[0])
            vis_end = int(w.index(f"@0,{w.winfo_height()}").split('.')[0])
        except Exception:
            vis_start, vis_end = 1, 1

        total_lines = getattr(w, '_total_lines', None)
        if total_lines:
            vis_start = max(1, vis_start)
            vis_end = min(vis_end, int(total_lines))

        left = bisect.bisect_left(ml, vis_start)
        right = bisect.bisect_right(ml, vis_end)

        VISIBLE_MAX = 2000
        if (right - left) > VISIBLE_MAX:
            right = left + VISIBLE_MAX

        self._try(w.tag_remove, 'highlight', f'{vis_start}.0', f'{vis_end}.end', prefix='tag_remove.highlight.visible')

        batch_size = 400
        idx0 = left

        def process_batch():
            nonlocal idx0
            if local_gen != int(getattr(w, '_highlight_gen', 0) or 0):
                w._highlight_running = False
                return
            end_idx = min(idx0 + batch_size, right)
            for i in range(idx0, end_idx):
                line = ml[i]
                self._try(w.tag_add, 'highlight', f"{line}.{cs[i]}", f"{line}.{ce[i]}", prefix='tag_add.highlight')
            idx0 = end_idx
            if idx0 < right:
                self._try(self.root.after, 10, process_batch, prefix='after.hl.batch')
            else:
                w._highlight_running = False
                self._try(w.update_idletasks, prefix='update_idletasks.hl')

        process_batch()

    def _reset_undo_baseline(self, widget=None, *, modified: bool = False):
        """Reset the undo/redo stacks after a programmatic bulk content change.
        Why: Tk Text (undo=True) records programmatic inserts/deletes in the undo stack.
        For bulk operations (load/print/filter/decode/clear), we treat the resulting buffer
        as the new baseline so Ctrl+Z only undoes *user* edits that come after.

        Args:
            widget: tk.Text to reset; defaults to current editor if None.
            modified: whether to leave the widget marked modified (default False).
        """
        w = widget or getattr(self, 'result_box', None)

        if not isinstance(w, tk.Text):
            return

        try:
            w.edit_reset()
            try:
                w.edit_separator()
            except Exception:
                pass
            try:
                w.edit_modified(bool(modified))
            except Exception:
                pass

        except Exception as e:
            self._swallow(e)

    def begin_content_update(self, widget=None):
        w = widget or getattr(self, 'result_box', None)
        if not isinstance(w, tk.Text):
            return

        w._suppress_scroll_cb = True

        aid = getattr(w, '_debounce_id', None)
        if aid:
            self._try(self.root.after_cancel, aid, prefix='after_cancel.begin_content')
            w._debounce_id = None

        w._highlight_gen = int(getattr(w, '_highlight_gen', 0) or 0) + 1
        w._highlight_running = False

        self._try(w.tag_remove, 'highlight', '1.0', 'end', prefix='tag_remove.highlight.all')

        for attr in ('_match_lines', '_match_cols_s', '_match_cols_e', '_total_lines', '_matches_version'):
            if hasattr(w, attr):
                try:
                    delattr(w, attr)
                except Exception as e:
                    self._swallow(e)

        w._content_version = int(getattr(w, '_content_version', 0) or 0) + 1

    def end_content_update(self, widget=None):
        w = widget or getattr(self, 'result_box', None)
        if not isinstance(w, tk.Text):
            return
        w._suppress_scroll_cb = False

    def _rebuild_result_widgets(self):
        """Recreate the result Text widgets (fast clear) to avoid long stalls on huge buffers.
        Keeps the surrounding frames/paned layout intact.
        """
        # Destroy existing widgets if present
        for wname in ('line_numbers', 'result_box', 'v_scroll', 'h_scroll'):
            w = getattr(self, wname, None)
            if w is not None:
                try:
                    w.destroy()
                except Exception as e:
                    self._swallow(e)
        # Recreate widgets
        self.line_numbers = tk.Text(self.result_inner, width=4, padx=4, takefocus=0, borderwidth=0, relief='flat', wrap='none')
        self.line_numbers.pack(side='left', fill='y')
        self.line_numbers.config(state='disabled')

        self.result_box = tk.Text(self.result_inner, wrap='none', undo=True, maxundo=10, autoseparators=True)
        try:
            self.result_box.configure(font=getattr(self, '_mono_font', ('Lucida Console', 10)))
        except Exception as e:
            self._swallow(e)
        try:
            self.line_numbers.configure(font=getattr(self, '_mono_font', ('Lucida Console', 10)))
        except Exception as e:
            self._swallow(e)
        self.result_box.pack(side='left', fill='both', expand=True)
        try:
            self._bind_occurrence_clear_events()
        except Exception as e:
            self._swallow(e)
        self.v_scroll = tk.Scrollbar(self.result_inner, orient='vertical', width=30)
        self.v_scroll.pack(side='right', fill='y')
        self.v_scroll.config(command=self._on_vscroll)
        self.result_box.config(yscrollcommand=self._on_yscroll)

        self.h_scroll = tk.Scrollbar(self.result_frame, orient='horizontal', command=self.result_box.xview, width=30)
        self.h_scroll.pack(fill='x')
        self.result_box.config(xscrollcommand=self.h_scroll.set)

        # Re-bind result-box related events (without touching log_box/root bindings excessively)
        try:
            for seq in ('<KeyRelease>', '<ButtonRelease-1>', '<B1-Motion>', '<FocusIn>'):
                self.result_box.bind(seq, self._update_status_bar, add='+')
            for seq in ('<MouseWheel>', '<Button-4>', '<Button-5>', '<Configure>'):
                self.result_box.bind(seq, self._update_linenumbers_debounced, add='+')
            # Gutter robustness: update line numbers on text mutations (Enter/Delete/Paste/Undo/Redo)
            for seq in ('<KeyRelease>', '<Return>', '<BackSpace>', '<Delete>', '<<Paste>>', '<<Cut>>', '<<Undo>>', '<<Redo>>'):
                self.result_box.bind(seq, self._update_linenumbers_debounced, add='+')
        except Exception as e:
            self._swallow(e)
        try:
            # Highlight/scroll coalescing
            self.bind_highlight_events_once()
        except Exception as e:
            self._swallow(e)
        try:
            # Re-bind context menu to the new result_box (menu already exists)
            self.result_box.bind('<Button-3>', self._show_text_context_menu)
            self.result_box.bind('<Control-Button-1>', self._show_text_context_menu)
            self.result_box.bind('<App>', lambda e, w=self.result_box: self._show_text_context_menu_keyboard(e, w))
            self.result_box.bind('<Menu>', lambda e, w=self.result_box: self._show_text_context_menu_keyboard(e, w))
        except Exception as e:
            self._swallow(e)
        try:
            # Shortcuts and custom selection
            self._install_text_shortcut_overrides()
            self._install_custom_word_selection()
            self._install_undo_redo_bindings()
            # Re-bind occurrence clear events (after rebuild bindings)
            try:
                self._bind_occurrence_clear_events()
            except Exception as e:
                self._swallow(e)
        except Exception as e:
            self._swallow(e)
        # Update Results tab mapping for rebuilt widgets
        try:
            if getattr(self, '_results_tab_id', None) in getattr(self, '_tabs', {}):
                self._tabs[self._results_tab_id]['text'] = self.result_box
                self._tabs[self._results_tab_id]['gutter'] = self.line_numbers
        except Exception as e:
            self._swallow(e)
        # Refresh tags/theme for the recreated widget
        try:
            self._configure_tags()
        except Exception as e:
            self._swallow(e)
        try:
            self._apply_theme()
        except Exception as e:
            self._swallow(e)
        try:
            self.root.after_idle(self._update_status_bar)
            self.root.after_idle(self._refresh_line_numbers)
        except Exception as e:
            self._swallow(e)

        # Re-install Results clear-button monitoring for recreated widget

        try:

            self._install_results_clear_button_monitoring()

        except Exception as e:

            self._swallow(e)


    def clear_text_area(self):
        # Clear the Results tab and reset related state safely.
        try:
            self._workspace_select_results()
        except Exception as e:
            self._swallow(e)
        if self.result_box.compare("end-1c", ">", "1.0"):
            if not self._mb_askyesno("Confirm Clear", "Clear the Results tab?"):
                return

        # 1) Stop/clear any in-flight searches (thread-safe)
        if isinstance(self.search_active, threading.Event):
            self.search_active.clear()

        # 2) Begin content update lifecycle: suppress callbacks, clear highlight/state, bump version
        self.begin_content_update()

        # 3) Fast clear: recreate Text widgets to avoid long stalls on huge buffers
        try:
            self._rebuild_result_widgets()
        except Exception:
            # Fallback to traditional delete if rebuild fails
            try:
                self.result_box.delete("1.0", "end")
            except Exception as e:
                self._swallow(e)
            try:
                self._reset_undo_baseline(self._get_results_text_widget(), modified=False)
            except Exception as e:
                self._swallow(e)
        # 4) Reset matches label and progress bar
        self._update_match_count(0)
        try:
            self.progress["value"] = 0
        except tk.TclError:
            pass

        # 5) End lifecycle and schedule highlight refresh (no-op on empty buffer)
        self.end_content_update()
        self._debounced_update()

        # Immediate refresh of status bar + line numbers (no click required)
        try:
            self.root.after_idle(self._update_status_bar)
            self.root.after_idle(self._refresh_line_numbers)
        except Exception as e:
            self._swallow(e)
        # 6) Log action for traceability
        try:
            self._update_clear_results_button_state(force=True)
        except Exception as e:
            self._swallow(e)


        self.log_message("Results tab cleared.")

    # -------------------- File selection & printing --------------------
    def select_files(self):
        # Preserve prior selection unless new unique files are added
        was_empty = (self.file_listbox.size() == 0)
        try:
            prior_selected_paths = [self.file_paths[i] for i in self.file_listbox.curselection()]
        except Exception:
            prior_selected_paths = []
        # Open file dialog, normalize de-dup, and update listbox.
        prior_file_paths = self.file_paths or []
        selection = filedialog.askopenfilenames(
            filetypes=[
                ("All files", "*.*"),
                ("Log files", "*.log"),
                ("Text files", "*.txt"),
                ("Files without extension", "*"),
            ]
        )
        if selection:
            prior_norm = {os.path.normpath(p) for p in prior_file_paths}
            new_files = [p for p in selection if os.path.normpath(p) not in prior_norm]
            if new_files:
                self.file_paths = prior_file_paths + new_files
                self.update_listbox(new_files=new_files, prior_selected=prior_selected_paths, was_empty=was_empty)
                self.log_message(f"{len(new_files)} new file(s) added. Total: {len(self.file_paths)} file(s) loaded.")
            else:
                self.file_paths = prior_file_paths
                self.log_message("No new unique files selected. All selected files were already loaded.")
        else:
            self.file_paths = prior_file_paths             # User cancelled; keep prior list untouched
            if prior_file_paths:  # Only if there were files before
                self.log_message("No new files selected, keeping prior files loaded.")
            else:
                self.log_message("No files selected.")

    def _append_file_to_listbox_if_missing(self, file_path: str, select: bool = True):
        """Append file_path to the listbox (and self.file_paths) if not already present.
        Matches the UX of selecting new files: appended at end, selected, and scrolled into view.
        """

        if not file_path:
            return

        try:
            norm = os.path.normpath(file_path)
        except Exception:
            norm = file_path

        try:
            existing = [os.path.normpath(p) for p in (self.file_paths or [])]
        except Exception:
            existing = list(self.file_paths or [])

        if norm in existing:
            return

        try:
            self.file_paths.append(file_path)
        except Exception as e:
            self._swallow(e)
            return

        try:
            self.file_listbox.insert(tk.END, self._format_listbox_item(file_path))

            if select:
                self.file_listbox.selection_clear(0, tk.END)
                last = self.file_listbox.size() - 1

                if last >= 0:
                    self.file_listbox.selection_set(last)
                    self.file_listbox.activate(last)
                    self.file_listbox.see(last)

            self.update_selection_label()

        except Exception as e:
            self._swallow(e)

    def _get_results_text_widget(self):
        """Return the *Results tab* Text widget regardless of current active tab.
        This prevents actions like Print Contents from accidentally writing into a file tab
        when that tab is active.
        """
        try:
            tid = getattr(self, '_results_tab_id', None)
            st = (getattr(self, '_tabs', {}) or {}).get(tid, {}) if tid else {}
            w = st.get('text')
            if isinstance(w, tk.Text):
                return w
        except Exception:
            pass
        w = getattr(self, 'result_box', None)
        return w if isinstance(w, tk.Text) else None

    def _get_results_gutter_widget(self):
        """Return the Results tab gutter Text widget (line numbers)."""
        try:
            tid = getattr(self, '_results_tab_id', None)
            st = (getattr(self, '_tabs', {}) or {}).get(tid, {}) if tid else {}
            g = st.get('gutter')
            if isinstance(g, tk.Text):
                return g
        except Exception:
            pass
        g = getattr(self, 'line_numbers', None)
        return g if isinstance(g, tk.Text) else None

    def print_file_contents(self):
        # Load selected files into the Results tab with headers and progress.
        # NOTE: Must always target the Results Text widget, even if a file tab is active.
        selected_files = self.get_selected_file_paths()

        if not selected_files:
            self._mb_showwarning("Warning 😨", "No Files Selected.")
            return

        # One file -> open in its own tab; multiple -> print into Results tab (replace).
        if len(selected_files) == 1:
            self.open_file_in_tab(selected_files[0], focus=True)
            return

        # Force Results tab active and update active editor pointers immediately.
        try:
            self._workspace_select_results()
        except Exception as e:
            self._swallow(e)
        try:
            # Ensure self.result_box/self.line_numbers now point to the Results widgets.
            self._on_workspace_tab_changed()
        except Exception as e:
            self._swallow(e)

        w_results = self._get_results_text_widget()

        if not isinstance(w_results, tk.Text):
            # Fallback to current editor if something went wrong (should not happen).
            w_results = getattr(self, 'result_box', None)

        # Compute total bytes for selected files (cached for UI speed).
        total_bytes = 0

        for p in selected_files:
            try:
                total_bytes += self._get_file_size_cached(p)
            except Exception as e:
                self._swallow(e)

        self._last_print_total_bytes = int(total_bytes)

        # Safety guardrails before loading big content into Tk Text.
        try:
            soft = int(getattr(self, 'SOFT_LIMIT_BYTES', 0) or 0)
            hard = int(getattr(self, 'HARD_LIMIT_BYTES', 0) or 0)
        except Exception:
            soft, hard = 0, 0
        if soft > 0 and hard > 0:
            if total_bytes > hard:
                msg = (
                    f"You are trying to load {self._format_bytes(total_bytes)} into the Results tab.\n\n"
                    f"This can make the app unresponsive for Clear/Find operations.\n\n"
                    f"This operation is blocked (Hard limit: {self._format_bytes(hard)}).\n\n"
                    f"Tip: Use Find in Files or reduce the selection."
                )

                self._mb_showwarning('Large Load Blocked', msg)

                return

            elif total_bytes > soft:
                msg = (
                    f"You are trying to load {self._format_bytes(total_bytes)} into the Results tab.\n\n"
                    f"Loading this amount may cause the app to become unresponsive for Clear/Find operations.\n\n"
                    f"Recommended maximum without issues is about {self._format_bytes(soft)} on this configuration.\n\n"
                    f"Proceed?"
                )

                if not self._mb_askyesno('Large Load Warning', msg):
                    return

        # Begin lifecycle (suppresses callbacks and clears stale state) for the Results widget.
        self.begin_content_update(widget=w_results)

        try:
            # Explicitly clear to fully replace prior output.
            w_results.delete('1.0', 'end')
        except Exception as e:
            self._swallow(e)

        written_bytes = 0
        CHUNK = 1_048_576  # 1 MiB

        for file_path in selected_files:
            filename = os.path.basename(file_path)
            self.log_message(f"Printing File: {filename}...")

            # Insert file header
            try:
                w_results.insert('end', f"\n Contents of file: {filename} :\n\n", ('file_header',))
            except Exception as e:
                self._swallow(e)

            # Binary read + decode per chunk for performance
            try:
                with open(file_path, 'rb') as f:
                    first_chunk = True
                    while True:
                        b = f.read(CHUNK)

                        if not b:
                            break

                        if first_chunk and b.startswith(b'\xef\xbb\xbf'):
                            t = b.decode('utf-8-sig', errors='ignore')

                        else:
                            t = b.decode('utf-8', errors='ignore')

                        first_chunk = False
                        w_results.insert('end', t)
                        written_bytes += len(b)
                        pct = 100.0 * (written_bytes / total_bytes) if total_bytes > 0 else 100.0

                        try:
                            self.progress['value'] = pct
                            self.root.update_idletasks()
                        except tk.TclError:
                            pass

            except OSError as e:
                self.log_message(f"Error reading {file_path}: {e}")
            except Exception as e:
                self._swallow(e)

        # Reset progress at the end
        try:
            self.progress['value'] = 0
        except tk.TclError:
            pass

        self.log_message(f"Done, printed {len(selected_files)} file(s).")

        # End lifecycle and schedule highlight recompute for visible area (Results widget)
        self.end_content_update(widget=w_results)
        # Reset undo stack after programmatic print into Results
        self._reset_undo_baseline(w_results, modified=False)
        try:
            self._debounced_update(widget=w_results)
        except Exception as e:
            self._swallow(e)

        # Immediate refresh of status bar + line numbers (no click required).

        try:
            self.root.after_idle(self._update_status_bar)
            self.root.after_idle(self._refresh_line_numbers)
        except Exception as e:
            self._swallow(e)

    def update_listbox(self, new_files=None, prior_selected=None, was_empty=False):
        # Refresh listbox items from self.file_paths with smarter selection behavior.
        # Selection rules:
        #  - If listbox was empty before (was_empty=True), select all.
        #  - Else if new_files provided, select only those newly added.
        #  - Else preserve prior_selected (if provided).
        new_files = new_files or []
        prior_selected = prior_selected or []
        try:
            new_norm = {os.path.normpath(p) for p in new_files}
        except Exception:
            new_norm = set(new_files)
        try:
            prior_norm = {os.path.normpath(p) for p in prior_selected}
        except Exception:
            prior_norm = set(prior_selected)

        self.file_listbox.delete(0, tk.END)
        for path in self.file_paths:
            self.file_listbox.insert(tk.END, self._format_listbox_item(path))

        total = self.file_listbox.size()
        self.file_listbox.selection_clear(0, tk.END)

        if total <= 0:
            self.all_selected = False
            try:
                self.toggle_button.config(text='Select All')
            except Exception as e:
                self._swallow(e)
            self.update_selection_label()
            return

        if was_empty:
            self.file_listbox.selection_set(0, tk.END)
        elif new_norm:
            for i, p in enumerate(self.file_paths):
                try:
                    if os.path.normpath(p) in new_norm:
                        self.file_listbox.selection_set(i)
                except Exception:
                    if p in new_norm:
                        self.file_listbox.selection_set(i)
        elif prior_norm:
            for i, p in enumerate(self.file_paths):
                try:
                    if os.path.normpath(p) in prior_norm:
                        self.file_listbox.selection_set(i)
                except Exception:
                    if p in prior_norm:
                        self.file_listbox.selection_set(i)

        self.update_selection_label()
        # Auto-scroll listbox to show newly selected file(s)
        # Selecting items does not automatically scroll the Listbox; when we rebuild the list,
        # we explicitly ensure the newly-selected item(s) are visible (matches the old UX).
        try:
            _sel = self.file_listbox.curselection()
            if _sel:
                if was_empty:
                    # First load: keep the natural view at the top (like the original behavior).
                    _idx = 0
                elif new_norm:
                    # Additional loads: jump to the last newly-selected (typically the last new file).
                    _idx = int(_sel[-1])
                else:
                    _idx = None
                if _idx is not None:
                    self.file_listbox.activate(_idx)
                    self.file_listbox.see(_idx)

        except Exception as e:
            self._swallow(e)

        self.file_listbox.focus_set()
        try:
            self._update_selected_size_label()
        except Exception as e:
            self._swallow(e)

    def toggle_selection(self):
        # Toggle listbox selection between all and none.
        if getattr(self, 'all_selected', True):
            self.file_listbox.select_clear(0, tk.END)
            self.toggle_button.config(text="Select All")
        else:
            self.file_listbox.select_set(0, tk.END)
            self.toggle_button.config(text="Deselect All")

        self.all_selected = not getattr(self, 'all_selected', True)
        self.update_selection_label()

    def _ellipsize(self, s: str, max_chars: int) -> str:
        # Trim string to max_chars, appending '...' when needed.
        try:
            s = str(s)
        except Exception:
            return ''
        if max_chars <= 0:
            return ''
        if len(s) <= max_chars:
            return s
        if max_chars <= 3:
            return s[:max_chars]
        return s[:max_chars-3] + '...'

    def _calc_listbox_columns(self):
        """Return (name_chars, size_chars) so sizes appear near filenames and do not clip.

        - Uses monospace font metrics to estimate available chars in lb_frame.
        - Name column is based on the *max filename length* (clamped) so sizes are not pushed far right.
        - Size column is based on the max formatted size length (clamped).
        """
        # Estimate available characters from pixel width and font metrics
        try:
            fnt = tkfont.Font(font=getattr(self, '_lb_font', ('Lucida Console', 10)))
            px_per_char = max(6, fnt.measure('0'))
        except Exception:
            px_per_char = 8
        try:
            w_px = int(self.lb_frame.winfo_width() or getattr(self, '_lb_fixed_px', 320))
        except Exception:
            w_px = int(getattr(self, '_lb_fixed_px', 320))
        avail_chars = max(24, int(w_px / max(1, px_per_char)) - 1)

        # Determine max filename length and max size length among loaded files
        try:
            names = [os.path.basename(p) for p in (self.file_paths or [])]
        except Exception:
            names = []
        max_name = max([len(n) for n in names], default=12)

        try:
            sizes = [self._format_bytes(self._get_file_size_cached(p)) for p in (self.file_paths or [])]
        except Exception:
            sizes = []
        max_size = max([len(s) for s in sizes], default=9)
        size_chars = max(8, min(14, max_size))

        # Name column: based on max_name but cannot exceed available space
        # Keep it close: cap at 50 chars even if there is more room
        name_cap = 50
        name_chars = min(max_name, name_cap, max(10, avail_chars - (size_chars + 4)))
        return int(name_chars), int(size_chars)

    def _format_listbox_item(self, path: str) -> str:
        # Listbox row: <name padded> + 4 spaces + <size right-aligned> (monospace).
        try:
            name = os.path.basename(path)
        except Exception:
            name = str(path)
        try:
            size_b = self._get_file_size_cached(path)
        except Exception:
            size_b = 0
        size_s = self._format_bytes(size_b)
        try:
            name_chars, size_chars = self._calc_listbox_columns()
        except Exception:
            name_chars, size_chars = (40, 12)
        name_disp = self._ellipsize(name, name_chars)
        return f"{name_disp:<{name_chars}}    {size_s:>{size_chars}}"

    def _format_bytes(self, n: int) -> str:
        # Human-friendly file size formatting
        try:
            n = int(n)
        except Exception:
            n = 0
        if n < 0:
            n = 0
        units = ['B', 'KiB', 'MiB', 'GiB', 'TiB']
        f = float(n)
        u = 0
        while f >= 1024.0 and u < len(units) - 1:
            f /= 1024.0
            u += 1
        if u == 0:
            return f"{int(f):,} {units[u]}"
        return f"{f:,.2f} {units[u]}"

    def _get_file_size_cached(self, path: str) -> int:
        # Cache per-path sizes (stat can be slow over network shares)
        if not path:
            return 0
        try:
            p = os.path.normpath(path)
        except Exception:
            p = path
        if p in self._file_size_cache:
            return int(self._file_size_cache.get(p) or 0)
        try:
            sz = os.path.getsize(p) if os.path.exists(p) else 0
        except Exception:
            sz = 0
        self._file_size_cache[p] = int(sz)
        return int(sz)

    def _update_selected_size_label(self):
        # Update the 'File(s) Size' label based on current listbox selection
        try:
            idxs = self.file_listbox.curselection()
        except Exception:
            idxs = ()
        total = 0
        try:
            for i in idxs:
                try:
                    total += self._get_file_size_cached(self.file_paths[int(i)])
                except Exception as e:
                    self._swallow(e)
        except Exception:
            total = 0
        try:
            if hasattr(self, 'size_label'):
                self.size_label.config(text=f"File(s) Size: {self._format_bytes(total)}")
        except Exception as e:
            self._swallow(e)
        return int(total)

    def update_selection_label(self, event=None):
        # Update label with selected count and button text accordingly.
        selected_indices = self.file_listbox.curselection()
        selected_count = len(selected_indices)
        total_count = self.file_listbox.size()
        self.selection_label.config(text=f"Selected files: {selected_count}")

        if selected_count == total_count and total_count > 0:
            self.toggle_button.config(text="Deselect All")
            self.all_selected = True
        else:
            self.toggle_button.config(text="Select All")
            self.all_selected = False
        # Update size label
        try:
            self._update_selected_size_label()
        except Exception as e:
            self._swallow(e)

    def get_selected_file_paths(self):
        # Return full paths for current selection from listbox.
        selected_indices = self.file_listbox.curselection()
        return [self.file_paths[i] for i in selected_indices]

    def _lb_shift_extend(self, new_index: int):
        """Extend listbox selection from the anchor to new_index."""
        lb = self.file_listbox
        size = lb.size()
        if size <= 0:
            return
        new_index = max(0, min(size - 1, int(new_index)))
        try:
            anchor = int(lb.index('anchor'))
        except Exception:
            anchor = new_index
            try:
                lb.selection_anchor(new_index)
            except Exception as e:
                self._swallow(e)
        lo, hi = (anchor, new_index) if anchor <= new_index else (new_index, anchor)
        lb.selection_clear(0, tk.END)
        lb.selection_set(lo, hi)
        lb.activate(new_index)
        lb.see(new_index)
        self.update_selection_label()

    def _lb_visible_range(self):
        """Return (top_index, bottom_index, visible_count) for the file listbox.
       Uses pixel geometry so PgUp/PgDn operates on exactly the currently visible rows.
        """
        lb = self.file_listbox
        size = lb.size()

        if size <= 0:
            return (0, -1, 0)

        try:
            lb.update_idletasks()
        except Exception as e:
            self._swallow(e)
        try:
            top = int(lb.nearest(0))
            bottom = int(lb.nearest(max(0, lb.winfo_height() - 1)))
        except Exception:
            top = int(lb.nearest(0)) if size else 0
            bottom = min(size - 1, top + max(1, int(lb['height']) - 1))

        if bottom < top:
            bottom = top

        top = max(0, min(size - 1, top))
        bottom = max(0, min(size - 1, bottom))

        return (top, bottom, bottom - top + 1)

    def _lb_page_delta(self):
        """Backward-compatible: number of visible rows (one page)."""
        _t, _b, n = self._lb_visible_range()
        return max(1, n)

    def _on_lb_shift_pageup(self, event=None):
        lb = self.file_listbox
        cur = lb.curselection()
        idx = int(cur[0]) if cur else int(lb.index('active') or 0)

        _top, _bottom, n = self._lb_visible_range()

        if n <= 0:
            return 'break'

        # Align so the current index is at the bottom of the viewport (avoids partial-page selection)
        new_top = max(0, idx - (n - 1))

        try:
            lb.yview(new_top)
        except Exception as e:
            self._swallow(e)
        top2, _bottom2, _n2 = self._lb_visible_range()
        self._lb_shift_extend(top2)
        return 'break'

    def _on_lb_shift_pagedown(self, event=None):
        lb = self.file_listbox
        cur = lb.curselection()
        idx = int(cur[-1]) if cur else int(lb.index('active') or 0)

        _top, _bottom, n = self._lb_visible_range()

        if n <= 0:
            return 'break'

        # Align so the current index is at the top of the viewport (avoids partial-page selection)
        try:
            lb.yview(idx)
        except Exception as e:
            self._swallow(e)
        _top2, bottom2, _n2 = self._lb_visible_range()
        self._lb_shift_extend(bottom2)
        return 'break'

    def _on_lb_shift_home(self, event=None):
        self._lb_shift_extend(0)
        return "break"

    def _on_lb_shift_end(self, event=None):
        lb = self.file_listbox
        self._lb_shift_extend(lb.size() - 1)
        return "break"

    def _on_file_listbox_double_click(self, event=None):
        """Open the double-clicked file in its own tab."""
        lb = self.file_listbox
        try:
            idx = lb.nearest(event.y)
        except Exception:
            return 'break'
        if idx is None or idx < 0:
            return 'break'
        try:
            path = self.file_paths[int(idx)]
        except Exception:
            return 'break'
        # Ensure selection aligns with clicked item
        try:
            cur = set(lb.curselection())
            if idx not in cur:
                lb.selection_clear(0, tk.END)
                lb.selection_set(idx)
                lb.activate(idx)
                lb.see(idx)
                self.update_selection_label()
        except Exception as e:
            self._swallow(e)
        self.open_file_in_tab(path, focus=True)
        return 'break'

    # -------------------- Find (single) & Find All --------------------
    def open_find_dialog(self):
        # If a Find dialog is already open, just bring it to front
        if hasattr(self, "find_win") and self.find_win and self.find_win.winfo_exists():
            try:
                self.find_win.deiconify()
                self.find_win.lift()
                self.find_win.focus_force()
                # If you stored the entry widget on the dialog, refocus it:
                if hasattr(self, "_find_entry") and self._find_entry.winfo_exists():
                    self._find_entry.focus_set()
                return
            except tk.TclError:
                # In case the window handle is stale; fall through to recreate
                pass

        # Cancel any pending highlight updates to avoid UI churn when dialog appears
        if getattr(self, "_debounce_id", None):
            try:
                self.root.after_cancel(self._debounce_id)
            except tk.TclError:
                pass
            self._debounce_id = None

        # Create the dialog and remember the reference
        find_win = tk.Toplevel(self.root)
        self.find_win = find_win
        find_win.title("Find 🔎")

        # Make it transient and stay on top of the main window (nicer behavior)
        try:
            find_win.transient(self.root)
            # Optional: avoid full input grab to keep app responsive
            # find_win.grab_set()  # use only if you truly want modal behavior
        except tk.TclError:
            pass

        # Position dialog relative to main window
        x = self.root.winfo_x() + 600
        y = self.root.winfo_y() + 400
        find_win.geometry(f"+{x}+{y}")

        # Close handler: destroy and clear the reference
        def _close_find():
            try:
                find_win.destroy()
            finally:
                # Release the reference so a new dialog can be created later
                self.find_win = None

        find_win.protocol("WM_DELETE_WINDOW", _close_find)
        find_win.bind("<Escape>", lambda e: _close_find())


        # ---------- Dialog UI ----------
        # Tabbed Find dialog (scalable for future tabs)
        notebook = ttk.Notebook(find_win)
        self._find_notebook = notebook
        notebook.pack(padx=10, pady=10, fill='both', expand=True)
        # Enable standard ttk traversal bindings (if available)
        try:
            notebook.enable_traversal()
        except Exception as e:
            self._swallow(e)
        # ---------------------------
        # Tab 1: Find
        # ---------------------------
        tab_find = tk.Frame(notebook)
        notebook.add(tab_find, text='Find')

        entry_frame = tk.Frame(tab_find)
        entry_frame.pack(padx=10, pady=10, fill='x')
        tk.Label(entry_frame, text='Search String:').pack(side='left', padx=(0, 5))
        entry = tk.Entry(entry_frame, width=40)
        entry.pack(side='left', expand=True, fill='x')
        entry.focus_set()

        # Keep a reference to entry so we can refocus it when reusing the dialog
        self._find_entry = entry

        options_frame = tk.Frame(tab_find)
        options_frame.pack(padx=10, pady=5, fill='x')

        regex_var = tk.BooleanVar(value=True)  # keep your current default
        case_var = tk.BooleanVar()

        tk.Checkbutton(options_frame, text='Use Regex', variable=regex_var).pack(side='left', padx=10)
        tk.Checkbutton(options_frame, text='Case Sensitive', variable=case_var).pack(side='left', padx=10)

        buttons_frame = tk.Frame(tab_find)
        buttons_frame.pack(padx=10, pady=15)

        find_button = tk.Button(
            buttons_frame,
            text='Find',
            width=12,
            command=lambda: (
                self._require_nonempty_term(entry.get()) and
                self._require_nonempty_text_area() and
                self.find_term(entry.get(), regex_var.get(), case_var.get())
            )
        )
        find_button.pack(side='left', padx=8)
        self.find_button = find_button  # for label updates in find_term()

        tk.Button(
            buttons_frame,
            text='Find All',
            width=12,
            command=lambda: (
                self._require_nonempty_term(entry.get()) and
                self._require_nonempty_text_area() and
                self.find_all_terms(entry.get(), regex_var.get(), case_var.get())
            )
        ).pack(side='left', padx=8)

        tk.Button(
            buttons_frame,
            text='Find in Files',
            width=12,
            command=lambda: (
                self._require_nonempty_term(entry.get()) and
                self.start_search('search_files', entry.get(), regex_var.get(), case_var.get())
            )
        ).pack(side='left', padx=8)

        tk.Button(
            buttons_frame,
            text='Filter Matches',
            width=12,
            command=lambda: (
                self._require_nonempty_term(entry.get()) and
                self._require_nonempty_text_area() and
                self.start_search('search_text_area', entry.get(), regex_var.get(), case_var.get())
            )
        ).pack(side='left', padx=8)

        # Bind Enter / Shift+Enter
        entry.bind('<Return>', lambda e: (
            self._require_nonempty_term(entry.get()) and
            self._require_nonempty_text_area() and
            self.find_term(entry.get(), regex_var.get(), case_var.get())
        ))
        entry.bind('<Shift-Return>', lambda e: (
            self._require_nonempty_term(entry.get()) and
            self._require_nonempty_text_area() and
            self.find_term(entry.get(), regex_var.get(), case_var.get(), reverse=True)
        ))

        # ---------------------------
        # Tab 2: RCV
        # ---------------------------
        tab_rcv = tk.Frame(notebook)
        notebook.add(tab_rcv, text='RCV')

        rcv_container = tk.Frame(tab_rcv)
        rcv_container.pack(fill='both', expand=True, padx=12, pady=12)

        # Top container : tk.OptionMenu + Entry field
        rcv_top = tk.Frame(rcv_container)
        rcv_top.pack(fill='x', pady=(0, 8))

        # Middle container : Regex / Case sensitive / Show Rules / Save to file
        rcv_mid = tk.Frame(rcv_container)
        rcv_mid.pack(fill='x', pady=(0, 8))

        # Bottom container : Failed / Passed + Search button
        rcv_bottom = tk.Frame(rcv_container)
        rcv_bottom.pack(fill='x')

        # Variables
        self.rcv_mode_var = tk.StringVar(value='Rule')
        self.rcv_query_var = tk.StringVar()

        # Command-mode options (enabled only in Command mode)
        self.rcv_regex_var = tk.BooleanVar(value=True)        # Regex default: ON
        self.rcv_case_var = tk.BooleanVar(value=False)        # Case sensitive default: OFF
        self.rcv_show_rules_var = tk.BooleanVar(value=False)  # Show Rules default: OFF

        # Shared option
        self.rcv_save_var = tk.BooleanVar(value=True)         # Save to file default: ON

        # Rule-mode options (enabled only in Rule mode)
        self.rcv_failed_var = tk.BooleanVar(value=True)       # Failed default: ON
        self.rcv_passed_var = tk.BooleanVar(value=False)      # Passed default: OFF

        # --- Top row widgets (NO external label) ---
        self.rcv_mode_menu = tk.OptionMenu(rcv_top, self.rcv_mode_var, 'Command', 'Rule')
        self.rcv_mode_menu.config(width=10)
        self.rcv_mode_menu.pack(side='left', padx=(0, 10))

        self.rcv_rule_entry = tk.Entry(rcv_top, textvariable=self.rcv_query_var)
        self.rcv_rule_entry.pack(side='left', fill='x', expand=True)

        # --- Middle row widgets ---
        self.rcv_regex_cb = tk.Checkbutton(rcv_mid, text='Regex', variable=self.rcv_regex_var)
        self.rcv_regex_cb.pack(side='left', padx=(0, 18))

        self.rcv_case_cb = tk.Checkbutton(rcv_mid, text='Case sensitive', variable=self.rcv_case_var)
        self.rcv_case_cb.pack(side='left', padx=(0, 18))

        self.rcv_show_rules_cb = tk.Checkbutton(rcv_mid, text='Show Rules', variable=self.rcv_show_rules_var)
        self.rcv_show_rules_cb.pack(side='left', padx=(0, 18))

        self.rcv_save_cb = tk.Checkbutton(rcv_mid, text='Save to file', variable=self.rcv_save_var)
        self.rcv_save_cb.pack(side='right')

        # --- Bottom row widgets ---
        self.rcv_failed_cb = tk.Checkbutton(rcv_bottom, text='Failed', variable=self.rcv_failed_var)
        self.rcv_failed_cb.pack(side='left', padx=(0, 18))

        self.rcv_passed_cb = tk.Checkbutton(rcv_bottom, text='Passed', variable=self.rcv_passed_var)
        self.rcv_passed_cb.pack(side='left', padx=(0, 18))

        def _rcv_start(event=None):
            mode = self.rcv_mode_var.get()
            q = self.rcv_query_var.get()
            save = bool(self.rcv_save_var.get())
            if mode == 'Rule':
                failed = bool(self.rcv_failed_var.get())
                passed = bool(self.rcv_passed_var.get())
                case_sensitive = bool(self.rcv_case_var.get())  # kept False by default in Rule mode
                self.start_rcv_search(q, failed, passed, save, case_sensitive)
            else:
                use_regex = bool(self.rcv_regex_var.get())
                case_sensitive = bool(self.rcv_case_var.get())
                show_rules = bool(self.rcv_show_rules_var.get())
                self.start_rcv_command_search(q, use_regex, case_sensitive, show_rules, save)
            return 'break'

        self.rcv_search_btn = tk.Button(rcv_bottom, text='Search', width=12, command=_rcv_start)
        self.rcv_search_btn.pack(side='right')

        # Enter triggers Search from RCV entry
        self.rcv_rule_entry.bind('<Return>', _rcv_start)

        def _apply_rcv_mode_constraints(*_):
            mode = self.rcv_mode_var.get()
            if mode == 'Command':
                # Command: enable Regex/Case/Show Rules, disable Failed/Passed
                self.rcv_regex_cb.config(state='normal')
                self.rcv_case_cb.config(state='normal')
                self.rcv_show_rules_cb.config(state='normal')
                self.rcv_failed_cb.config(state='disabled')
                self.rcv_passed_cb.config(state='disabled')
            else:
                # Rule: enable Failed/Passed, disable Regex/Case/Show Rules
                self.rcv_regex_cb.config(state='disabled')
                self.rcv_case_cb.config(state='disabled')
                self.rcv_show_rules_cb.config(state='disabled')
                self.rcv_failed_cb.config(state='normal')
                self.rcv_passed_cb.config(state='normal')

            # Save to file always enabled
            self.rcv_save_cb.config(state='normal')

        self.rcv_mode_var.trace_add('write', _apply_rcv_mode_constraints)
        _apply_rcv_mode_constraints()

        def _focus_active_tab(event=None):
            # Ensure cursor goes to the primary entry of the active tab
            try:
                sel = notebook.select()
                if sel == str(tab_find):
                    entry.focus_set()
                elif sel == str(tab_rcv):
                    self.rcv_rule_entry.focus_set()
            except tk.TclError:
                pass

        # Focus entry whenever the user changes tabs (mouse OR keyboard)
        notebook.bind('<<NotebookTabChanged>>', _focus_active_tab)

        # Explicit Ctrl+Tab / Ctrl+Shift+Tab navigation (robust across platforms)
        def _nb_switch(delta: int):
            try:
                tabs = list(notebook.tabs())
                if not tabs:
                    return
                cur = notebook.select()
                i = tabs.index(cur) if cur in tabs else 0
                notebook.select(tabs[(i + delta) % len(tabs)])
            except tk.TclError:
                pass

        def _on_ctrl_tab(event=None):
            _nb_switch(+1)
            find_win.after_idle(_focus_active_tab)
            return 'break'

        def _on_ctrl_shift_tab(event=None):
            _nb_switch(-1)
            find_win.after_idle(_focus_active_tab)
            return 'break'

        find_win.bind('<Control-Tab>', _on_ctrl_tab)
        find_win.bind('<Control-Shift-Tab>', _on_ctrl_shift_tab)
        find_win.bind('<Control-ISO_Left_Tab>', _on_ctrl_shift_tab)

        # Default to Find tab and keep focus in the Find entry
        try:
            notebook.select(tab_find)
        except tk.TclError:
            pass
        find_win.after_idle(_focus_active_tab)

        find_win.after(50, self._restore_find_dialog_focus)
    # Flush geometry so the dialog is fully laid out
        try:
            self.root.update_idletasks()
        except tk.TclError:
            pass

    def find_term(self, term, use_regex, case_sensitive, reverse=False):

        t0 = time.perf_counter()

        # 1. Validation: Regex not allowed in reverse
        if reverse and use_regex:
            self._mb_showwarning("Not Allowed", "Regex searches are not supported in backward direction.")
            return

        # 2. Determine Start Position
        start_pos = self.result_box.index("insert")
        if reverse:
            start_pos = f"{start_pos}-1c"
        else:
            start_pos = f"{start_pos}+1c"

        # 3. Setup Search Parameters
        count_var = tk.IntVar()

        # Perform the search (Native Tcl speed)
        found_index = self.result_box.search(
            term,
            start_pos,
            stopindex=None,
            nocase=not case_sensitive,
            regexp=use_regex,
            backwards=reverse,
            count=count_var
        )

        # 4. Handle "Not Found" (EOF/BOF Logic)
        if not found_index:
            msg = "End of file reached. Continue from start?" if not reverse else "Start of file reached. Continue from bottom?"
            if self._mb_askyesno("Find", msg):
                wrap_start = "end" if reverse else "1.0"
                self.result_box.mark_set("insert", wrap_start)
                found_index = self.result_box.search(
                    term,
                    wrap_start,
                    stopindex=None,
                    nocase=not case_sensitive,
                    regexp=use_regex,
                    backwards=reverse,
                    count=count_var
                )
                if not found_index:
                    self.log_message(f'The searched term "{term}" was NOT found in the whole text currently displayed.')
                    self._mb_showinfo("Find", f"'{term}' not found.")
                    return
            else:
                return  # User said No to wrap

        # 5. Handle "Found"
        match_len = count_var.get()
        if match_len == 0:
            match_len = len(term)
        end_index = f"{found_index}+{match_len}c"
        # --- FIX: Reset selection + selection anchor after Find ---
        # If a previous double-click left a selection active, Shift+Arrow may extend
        # from the old anchor to the new Find location (multi-line selection).
        # We clear any existing selection and reset Tk's internal selection anchor.
        try:
            self.result_box.tag_remove('sel', '1.0', 'end')
        except tk.TclError:
            pass
        # Clear any custom token-selection anchor used by Ctrl+Shift token selection
        try:
            if hasattr(self.result_box, '_kbd_anchor'):
                delattr(self.result_box, '_kbd_anchor')
        except Exception:
            pass
        # Reset Tk text selection anchor marks if present (safe across Tk builds)
        for _m in ('tk::anchor1', 'tk::anchor2'):
            try:
                self.result_box.mark_set(_m, found_index)
            except tk.TclError:
                pass


        # A. Highlight: remove previous only (fast)
        if hasattr(self.result_box, '_last_find_start') and hasattr(self.result_box, '_last_find_end'):
            try:
                self.result_box.tag_remove('search_highlight', getattr(self.result_box,'_last_find_start'), getattr(self.result_box,'_last_find_end'))
            except tk.TclError:
                pass

        self.result_box.tag_add("search_highlight", found_index, end_index)
        setattr(self.result_box, '_last_find_start', found_index)
        setattr(self.result_box, '_last_find_end', end_index)

        # B & C. Scroll to view + move cursor, with scroll suppression
        self._suppress_scroll_cb = True
        try:
            self.result_box.see(found_index)
            self.result_box.mark_set("insert", found_index)
        finally:
            self._suppress_scroll_cb = False

        # button label change (post ops)
        self.find_button.config(text="Find Next")

        # --- Final checkpoint after all ops ---
        t1 = time.perf_counter()

        # Compose single-line log showing only total time spent
        self.log_message(f'Term Searched: "{term}" found in {(t1 - t0) * 1000.0:,.2f} ms')

    def find_all_terms(self, term, use_regex, case_sensitive):
        """
        Thread-safe Find All:
        - Snapshots Text content on UI thread (NO Tk calls in worker).
        - Worker scans snapshot only (plain string).
        - UI updates (progress, labels, tags, install arrays) scheduled via root.after().
        - Cancellation uses self.search_active Event (Ctrl+Shift+C clears it).
        """

        # Prevent concurrent background file/text searches (optional but recommended)
        if self.search_thread and self.search_thread.is_alive():
            self.log_message("A search is already in progress. Cancel it before Find All.")
            return
        # Target widget is the active tab at invocation time (tab-independent Find All)
        w_target = getattr(self, 'result_box', None)

        # Guard: term must exist
        if not term:
            try:
                w_target.tag_remove("highlight", "1.0", "end")
            except tk.TclError:
                pass
            self._update_match_count(0)
            try:
                self.progress.configure(value=0)
            except tk.TclError:
                pass
            return

        # Guard: avoid overlapping Find All runs
        if getattr(self, "_findall_thread", None) and self._findall_thread.is_alive():
            self.log_message("Find All already in progress. Cancel it before starting another.")
            return

        # Ensure cancellation token exists (IMPORTANT: do NOT replace the Event object)
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()

        # ---- Local helper: cancellation check (worker-safe) ----
        def cancelled():
            return isinstance(self.search_active, threading.Event) and (not self.search_active.is_set())

        # ---- UI THREAD SNAPSHOT (Pattern #1 core) ----
        try:
            # Guard: Find All copies the full buffer; warn if last printed content was large
            try:
                if getattr(self, '_last_print_total_bytes', 0) > getattr(self, 'SOFT_LIMIT_BYTES', 0):
                    if not self._mb_askyesno('Find All',
                        'Find All on a large buffer may take a long time and can appear to freeze.\n\nProceed anyway?'):
                        self.log_message('Find All cancelled by user due to large buffer. Consider Find in Files.')
                        return
            except Exception as e:
                self._swallow(e)
            # Pre-check using native Tk search: if no matches, avoid snapshotting huge buffers
            _idx = ''
            try:
                _cv = tk.IntVar()
                _idx = self.result_box.search(term, '1.0', 'end-1c', nocase=not case_sensitive, regexp=use_regex, count=_cv)
            except Exception:
                _idx = ''
            if not _idx:
                # No matches: behave like Find All not found, without copying the whole buffer
                try:
                    self.result_box.tag_remove('highlight', '1.0', 'end')
                except Exception as e:
                    self._swallow(e)
                self._update_match_count(0)
                self.log_message(f'The searched term "{term}" was NOT found in the whole text currently displayed.')
                try:
                    self.progress.configure(value=0)
                    self._progress_target = 0
                    self.progress.update_idletasks()
                except Exception as e:
                    self._swallow(e)
                try:
                    self.root.configure(cursor='')
                    self.root.update_idletasks()
                except Exception as e:
                    self._swallow(e)
                self._mb_showinfo('Find All', f'"{term}" not found.')
                return

            # Snapshot safely in chunks
            snapshot_text = self._safe_text_snapshot(chunk_chars=2000000)
        except tk.TclError:
            snapshot_text = ""

        if not snapshot_text:
            self.log_message("Current Tab is empty. Nothing to search in.")
            self._update_match_count(0)
            try:
                self.progress.configure(value=0)
            except tk.TclError:
                pass
            return

        # Advertise Find All start (UI thread)

        mode = "Regex" if use_regex else "Plain"
        case = "Case-sensitive" if case_sensitive else "Case-insensitive"
        self.log_message(f'Looking for all matches of "{term}" into displayed text... ({mode}, {case})')
        try:
            self.root.configure(cursor="watch")
        except Exception as e:
            self._swallow(e)
        try:
            self.progress.configure(value=0)
        except tk.TclError:
            pass

        # Helper: Apply computed results on UI thread
        def apply_results(match_lines, match_cols_s, match_cols_e, total_lines, match_count):
            if cancelled():
                # Don't update UI if user cancelled
                try:
                    self.progress.configure(value=0)
                except tk.TclError:
                    pass
                return

            # If no matches -> behave like regular Find (log + popup) and exit early
            if match_count == 0:
                try:
                    w_target.tag_remove("highlight", "1.0", "end")
                except tk.TclError:
                    pass

                self._update_match_count(0)
                self.log_message(f'The searched term "{term}" was NOT found in the whole text currently displayed.')
                # Reset progress BEFORE the modal messagebox so it does not wait until the box is closed.
                try:
                    self.progress.configure(value=0)
                    self._progress_target = 0
                    self.progress.update_idletasks()
                except Exception as e:
                    self._swallow(e)
                try:
                    self.root.configure(cursor="")
                    self.root.update_idletasks()
                except Exception as e:
                    self._swallow(e)
                self._mb_showinfo("Find All", f'"{term}" not found.')
                return

            # Clear prior highlight tags
            try:
                w_target.tag_remove("highlight", "1.0", "end")
            except tk.TclError:
                pass

            # Install arrays atomically
            w_target._match_lines = match_lines
            w_target._match_cols_s = match_cols_s
            w_target._match_cols_e = match_cols_e
            w_target._total_lines = total_lines

            # Tag arrays to current content version (your existing mechanism)
            w_target._matches_version = getattr(w_target, "_content_version", 0)

            # Update UI counters/progress
            self._update_match_count(match_count)
            try:
                self.progress.configure(value=100)
            except tk.TclError:
                pass

            # Jump to first match so user sees results immediately
            first_line = match_lines[0]
            first_col  = match_cols_s[0]
            first_idx  = f"{first_line}.{first_col}"

            self._suppress_scroll_cb = True
            try:
                w_target.see(first_idx)
                w_target.mark_set("insert", first_idx)
            finally:
                self._suppress_scroll_cb = False

            # Paint only visible highlights (now that we jumped, first match will be visible)
            self.update_visible_highlights(widget=w_target)
            self.log_message(f"Find All completed. Matches: {match_count:,}.")
            try:
                self.root.configure(cursor="")
            except Exception as e:
                self._swallow(e)
            # Reset progress later
            self.root.after(750, lambda: self.progress.configure(value=0))

        # Worker thread: CPU-only scan on snapshot string (NO Tk calls!)
        def worker(text):
            try:
                # Initial progress reset
                self.root.after(0, lambda: self.progress.configure(value=0))

                # Build line_starts (maps char index -> line/col)
                # You already do something similar; keeping it consistent and fast.
                line_starts = [0]
                chunk = 5_000_000
                processed = 0
                text_len = len(text)

                for pos in range(0, text_len, chunk):
                    if cancelled():
                        self.root.after(0, lambda: self.progress.configure(value=0))
                        return

                    seg = text[pos:pos + chunk]
                    idx = seg.find("\n")
                    while idx != -1:
                        line_starts.append(pos + idx + 1)
                        idx = seg.find("\n", idx + 1)

                    processed += len(seg)
                    prep_pct = 10.0 * (processed / max(1, text_len))
                    self.root.after(0, lambda v=prep_pct: self.progress.configure(value=v))

                total_lines = len(line_starts)

                # Phase 2: compile and scan matches (progress 10..100)
                flags = 0 if case_sensitive else re.IGNORECASE
                try:
                    pattern = re.compile(term if use_regex else re.escape(term), flags)
                except re.error as e:
                    self.root.after(0, lambda: self._update_match_count(0))
                    self.root.after(0, lambda: self.progress.configure(value=0))
                    self.root.after(0, lambda: self._mb_showerror("Regex Error 😨", f"Invalid regular expression:\n\n{e}"))
                    return

                match_lines = []
                match_cols_s = []
                match_cols_e = []
                match_count = 0

                # Scan matches
                
                # Scan matches (one-pass line mapping; avoids per-match bisect)
                text_len = len(text)
                total_lines = len(line_starts)
                li0 = 0
                next_start = line_starts[1] if total_lines > 1 else (text_len + 1)
                
                for i, m in enumerate(pattern.finditer(text)):
                    if cancelled():
                        self.root.after(0, lambda: self.progress.configure(value=0))
                        return
                    s, e = m.start(), m.end()
                
                    while (li0 + 1) < total_lines and s >= next_start:
                        li0 += 1
                        next_start = line_starts[li0 + 1] if (li0 + 1) < total_lines else (text_len + 1)
                
                    line_no = li0 + 1
                    col_s = s - line_starts[li0]
                    col_e = e - line_starts[li0]
                
                    match_lines.append(line_no)
                    match_cols_s.append(col_s)
                    match_cols_e.append(col_e)
                    match_count += 1

                    # Progress occasionally (10..100)
                    if (i % 1000) == 0:
                        pct = 10.0 + 90.0 * (s / max(1, text_len))
                        self.root.after(0, lambda v=pct: self.progress.configure(value=v))
                
                # Apply results on UI thread in one shot
                self.root.after(
                    0,
                    lambda: apply_results(match_lines, match_cols_s, match_cols_e, total_lines, match_count)
                )

            except Exception as e:
                self.root.after(0, lambda: self.log_message(f"Find All error: {type(e).__name__}: {e}"))
                self.root.after(0, lambda: self.progress.configure(value=0))

        # Launch worker
        self._findall_thread = threading.Thread(target=worker, args=(snapshot_text,), daemon=True)
        self._findall_thread.start()

    # -------------------- Search in files / Results tab --------------------
    def start_search(self, search_source, term=None, use_regex=True, case_sensitive=False, highlight=False):
        # Start a background search across files or the Results tab.
        if self.search_thread and self.search_thread.is_alive():
            self.log_message("Search already in progress.")
            return

        # IMPORTANT: do NOT replace the Event object
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()
        self.ui_queue.put(('cursor', 'watch'))
        selected_files_snapshot = None
        text_snapshot = None

        if search_source == "search_files":
            selected_files_snapshot = self.get_selected_file_paths()

        elif search_source == "search_text_area":
            # Pre-check: if no matches, avoid snapshotting huge buffers
            try:
                _cv = tk.IntVar()
                _idx = self.result_box.search(term or '', '1.0', 'end-1c', nocase=not case_sensitive, regexp=use_regex, count=_cv)
            except Exception:
                _idx = ''
            if not _idx:
                # No matches: keep Results tab unchanged and report
                self.ui_queue.put(('set_match_count', 0))
                self.ui_queue.put(('progress_instant', 0))
                self.ui_queue.put(('msgbox_info', 'Filter Matches', f'"{term}" not found.'))
                self.ui_queue.put(('log', f'The searched term "{term}" was NOT found in the whole text currently displayed. Results tab was not modified.'))
                self.ui_queue.put(('done',))
                # Start UI poller if not already running
                if self._ui_poller_id is None:
                    self._ui_poller_id = self.root.after(50, self._ui_poller)
                return
            # Snapshot safely in chunks
            try:
                text_snapshot = self._safe_text_snapshot(chunk_chars=2000000)
            except Exception as e:
                self.ui_queue.put(('msgbox_error', 'Snapshot Error', f'{type(e).__name__}: {e}'))
                self.ui_queue.put(('cancelled', True))
                # Start UI poller if not already running
                if self._ui_poller_id is None:
                    self._ui_poller_id = self.root.after(50, self._ui_poller)
                return

        self.search_thread = threading.Thread(
            target=self.search_files,
            args=(
                search_source, term, use_regex, case_sensitive, highlight,
                selected_files_snapshot, text_snapshot
            ),
            daemon=True
        )

        self.search_thread.start()

        # Start poller if not already running
        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(50, self._ui_poller)

    def cancel_search(self):
        """
        Cancels any active background operation that relies on self.search_active,
        and also clears the current 'Find/Find Next' highlight (normal Find).
        Bound to Ctrl+Shift+C.
        """

        # 1) Cancel background operations (Find All / Find in Files / Filter Matches)
        if isinstance(self.search_active, threading.Event) and self.search_active.is_set():
            self.search_active.clear()

        # 2) Clear current Find highlight (per-tab)
        w = getattr(self, 'result_box', None)
        if isinstance(w, tk.Text) and hasattr(w, '_last_find_start') and hasattr(w, '_last_find_end'):
            try:
                w.tag_remove('search_highlight', getattr(w,'_last_find_start'), getattr(w,'_last_find_end'))
            except tk.TclError:
                pass

        # 3) Reset Find button label (if exists)
        if hasattr(self, "find_button"):
            try:
                self.find_button.config(text="Find")
            except tk.TclError:
                pass

    def search_files(
        self,
        search_source,
        term,
        use_regex,
        case_sensitive,
        highlight,
        selected_files=None,
        text_snapshot=None):
        """
        Worker-thread search (Option 1):
        - Scans files/lines in the worker thread.
        - Sends UI updates ONLY after finishing each file (not line-by-line).
        - Does NOT touch any Tk widgets directly.
        - Uses self.ui_queue for UI work (must be consumed by a main-thread poller).
        """

        search_term = term or ""
        highlight_results = bool(highlight)

        # Helper to check cancellation (single source of truth)
        def cancelled():
            return isinstance(self.search_active, threading.Event) and (not self.search_active.is_set())

        # Single, consistent cancellation exit path
        def cancel_exit(log_msg=None):
            detailed_logged = False

            if log_msg:
                self.ui_queue.put(("log", log_msg))
                detailed_logged = True

            # Always reset progress on cancel
            self.ui_queue.put(('cursor', ''))
            self.ui_queue.put(("progress", 0))

            # Tell UI poller whether we already logged a detailed cancel message
            self.ui_queue.put(("cancelled", detailed_logged))
            return

        # Defensive: if cancel already requested, exit quickly
        if cancelled():
            cancel_exit()
            return

        # ---- Compile regex (worker-safe). UI errors must be queued. ----
        flags = 0 if case_sensitive else re.IGNORECASE

        if use_regex:
            try:
                pattern = re.compile(search_term, flags)
            except re.error as e:
                # Queue both a log and (optionally) a messagebox action
                self.ui_queue.put(("log", f"Regex compilation error: {e}"))
                self.ui_queue.put(("msgbox_error", "Regex Error 😨", f"Invalid regular expression:\n\n{e}"))
                self.ui_queue.put(("cancelled", True))
                return
        else:
            pattern = None

        # -------------------------------------------------------------------------
        # SEARCH IN FILES (Option 1: update UI only after finishing each file)
        # -------------------------------------------------------------------------
        if search_source == "search_files":
            # IMPORTANT: selected_files must be a snapshot from the UI thread
            if selected_files is None:
                selected_files = getattr(self, "_selected_files_snapshot", None)

            if not selected_files:
                self.ui_queue.put(("log", "No files selected."))
                self.ui_queue.put(("msgbox_warning", "File Error", "No files selected."))
                self.ui_queue.put(("cancelled", True))
                return

            # NOTE: Do NOT clear results yet. We will clear only if/when we actually have matches to show.
            self.ui_queue.put(("progress", 0))
            self.ui_queue.put(("set_match_count", 0))

            total_files = len(selected_files)
            total_bytes = 0
            for p in selected_files:
                try:
                    if os.path.exists(p):
                        total_bytes += os.path.getsize(p)
                except OSError:
                    pass
            bytes_done = 0
            last_pct = -1
            total_matches = 0

            output_started = False  # becomes True after the first file with matches is emitted
            for file_index, file_path in enumerate(selected_files, start=1):
                filename = os.path.basename(file_path)

                if cancelled():
                    processed = file_index - 1
                    cancel_exit(f"Search cancelled after processing {processed}/{total_files} files, (before starting {filename}).")
                    return

                self.ui_queue.put(("log", f'Searching for "{search_term}" into {filename}...'))

                matches_for_file = []
                file_cancelled_midway = False

                try:
                    import codecs
                    decoder = codecs.getincrementaldecoder('utf-8')(errors='ignore')
                    buf = ''
                    CHUNK = 1024 * 1024
                    with open(file_path, 'rb') as f:
                        while True:
                            if cancelled():
                                file_cancelled_midway = True
                                break
                            b = f.read(CHUNK)
                            if not b:
                                break
                            bytes_done += len(b)
                            buf += decoder.decode(b)
                            parts = buf.splitlines(True)
                            if parts and not (parts[-1].endswith('\n') or parts[-1].endswith('\r')):
                                buf = parts.pop()
                            else:
                                buf = ''
                            for line in parts:
                                if use_regex:
                                    if pattern.search(line):
                                        matches_for_file.append(line.strip())
                                else:
                                    if case_sensitive:
                                        if search_term in line:
                                            matches_for_file.append(line.strip())
                                    else:
                                        if search_term.lower() in line.lower():
                                            matches_for_file.append(line.strip())
                            if total_bytes > 0:
                                pct = int((bytes_done * 100) / total_bytes)
                                if pct != last_pct:
                                    last_pct = pct
                                    self.ui_queue.put(('progress', pct))
                    # flush remaining
                    buf += decoder.decode(b'', final=True)
                    for line in buf.splitlines(True):
                        if not line:
                            continue
                        if use_regex:
                            if pattern.search(line):
                                matches_for_file.append(line.strip())
                        else:
                            if case_sensitive:
                                if search_term in line:
                                    matches_for_file.append(line.strip())
                            else:
                                if search_term.lower() in line.lower():
                                    matches_for_file.append(line.strip())
                except Exception as e:
                    self.ui_queue.put(("log", f"Error reading {file_path}: {e}"))

                # If cancelled mid-file, do NOT output partial file section (keeps output consistent)
                if file_cancelled_midway:
                    processed = file_index - 1
                    cancel_exit(
                        f"Search cancelled after processing {processed}/{total_files} files; "
                        f"cancelled during {filename}. No partial output appended for this file."
                        )
                    return

                # Output results for this file (single UI update chunk)
                if matches_for_file:
                    # First match found across all files -> now it's safe to clear/replace the Results tab
                    if not output_started:
                        output_started = True
                        self.ui_queue.put(('focus_results',))
                        self.ui_queue.put(("clear_results",))
                        self.ui_queue.put(("set_match_count", 0))
                    header = f"\n Matches found into {filename} ({len(matches_for_file)}):\n\n"
                    body = "\n".join(matches_for_file) + "\n"
                    self.ui_queue.put(("append_text", header, "file_header"))
                    self.ui_queue.put(("append_text", body, None))

                    total_matches += len(matches_for_file)
                    self.ui_queue.put(("set_match_count", total_matches))

            # Completed normally
            # If there were no matches, keep the existing Results tab untouched
            if not output_started:
                self.ui_queue.put(("log", "No matches found in selected files. Results tab was not modified."))
                self.ui_queue.put(("log", f"Files processed: {total_files}"))
                self.ui_queue.put(("progress_instant", 0))
                self.ui_queue.put(("msgbox_info", "Find in Files", f'"{search_term}" not found.'))
                self.ui_queue.put(("done",))
                return
            self.ui_queue.put(("log", f"Files processed: {total_files}"))
            self.ui_queue.put(("progress", 0))
            # Final cancellation gate: never report 'done' if cancelled

            if cancelled():
                cancel_exit("Search cancelled.")
                return

            self.ui_queue.put(('progress', 100))
            self.ui_queue.put(('cursor', ''))
            self.ui_queue.put(("done",))
            return

        # -------------------------------------------------------------------------
        # Search in Results tab (filter) - also worker-safe, replaces UI only at end
        # -------------------------------------------------------------------------
        elif search_source == "search_text_area":
            # IMPORTANT: text_snapshot must be a snapshot from the UI thread
            if text_snapshot is None:
                text_snapshot = getattr(self, "_text_snapshot", "")

            if not text_snapshot:
                self.ui_queue.put(("log", "Results tab is empty. Nothing to search in."))
                self.ui_queue.put(("cancelled", True))
                return

            lines = text_snapshot.splitlines()
            total_lines = len(lines)

            needle = search_term if case_sensitive else search_term.lower()

            matches = []
            self.ui_queue.put(("log", f'Searching for "{search_term}" into results area...'))
            self.ui_queue.put(("progress", 0))

            for i, line in enumerate(lines, start=1):
                if cancelled():
                    cancel_exit("Filtering cancelled. Results tab was not modified.")
                    return

                hay = line if case_sensitive else line.lower()

                if use_regex:
                    if pattern.search(line):
                        matches.append(line.strip())
                else:
                    if needle in hay:
                        matches.append(line.strip())

                # Update progress occasionally (not every line)
                if (i % 200) == 0 or i == total_lines:
                    self.ui_queue.put(("progress", (i / max(1, total_lines)) * 100.0))

            # Only now we modify Results tab (UI thread) since not cancelled
            if matches:
                # Matches found -> replace Results tab contents
                self.ui_queue.put(('focus_results',))
                self.ui_queue.put(("clear_results",))

                header = f"\n Matches found in Results tab: ({len(matches)})\n\n"
                body = "\n".join(matches) + "\n"
                self.ui_queue.put(("append_text", header, "text_header"))
                self.ui_queue.put(("append_text", body, None))
                self.ui_queue.put(("set_match_count", len(matches)))
            else:
                # No matches -> do NOT modify Results tab (align with Find in Files behavior)
                self.ui_queue.put(("set_match_count", 0))
                self.ui_queue.put(("log", f'The searched term "{search_term}" was NOT found in the whole text currently displayed. Results tab was not modified.'))
                self.ui_queue.put(("progress_instant", 0))
                self.ui_queue.put(("msgbox_info", "Filter Matches", f'"{search_term}" not found.'))
                self.ui_queue.put(("done",))
                return

            self.ui_queue.put(("progress", 0))
            # Final cancellation gate: never report 'done' if cancelled

            if cancelled():
                cancel_exit("Search cancelled.")
                return

            self.ui_queue.put(('progress', 100))
            self.ui_queue.put(('cursor', ''))
            self.ui_queue.put(("done",))

            # Optional: highlight matches AFTER replacement (still must be UI-threaded)
            # If you want this, do it via queue action handled by poller.
            if highlight_results:
                self.ui_queue.put(("highlight_request", search_term, use_regex, flags))
            return

        else:
            self.ui_queue.put(("log", f"Unknown search_source: {search_source}"))
            self.ui_queue.put(("cancelled", True))
            return

    def highlight_all_matches(self, term, text, use_regex, flags):
        #Apply highlight tag to all matches within provided text snapshot.
        pattern = re.compile(term, flags) if use_regex else re.compile(re.escape(term), flags)
        for match in pattern.finditer(text):
            start = f"1.0+{match.start()}c"
            end = f"1.0+{match.end()}c"
            self.result_box.tag_add("highlight", start, end)

    # -------------------- Export --------------------
    def export_results(self):
        # Export current Text content to a file (UTF-8 with BOM).
        text_now = self.result_box.get("1.0", "end-1c")
        self.matches = text_now.splitlines()
        if not self.matches:
            self._mb_showwarning("Export Error", "Current Tab is empty.")
            return

        export_path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[
                ("Log files", "*.log"),
                ("Text files", "*.txt"),
                ("All files", "*.*"),
            ]
        )
        if not export_path:
            return

        try:
            with open(export_path, 'w', encoding='utf-8-sig', newline="\n") as f:
                for line in self.matches:
                    f.write(line + '\n')
            self._mb_showinfo("Export Successful", f"Results exported to {export_path}")
            self.log_message(f"Results exported to {export_path}")
        except Exception as e:
            self._mb_showerror("Export Error", f"Failed to export results: {e}")
            self.log_message(f"Export error: {e}")

    # --------------------
    # RCV Tab Search Logic
    # --------------------

    def start_rcv_command_search(self, term_text: str, use_regex: bool, case_sensitive: bool, show_rules: bool, save: bool):
        term_text = (term_text or '').strip()
        if not term_text:
            self._mb_showwarning('RCV', 'Please enter a value.')
            return

        # Avoid overlap with other background work
        if (self.search_thread and self.search_thread.is_alive()) or (getattr(self, '_rcv_thread', None) and self._rcv_thread.is_alive()):
            self.log_message('A search is already in progress. Cancel it before starting an RCV search.')
            return

        # Ensure cancellation token exists & is set
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()

        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(20, self._ui_poller)
        try:
            self.root.configure(cursor='watch')
        except Exception as e:
            self._swallow(e)
        try:
            self._snap_progress(1)
        except Exception as e:
            self._swallow(e)
        try:
            # IMPORTANT: avoid Tk->Python Unicode conversion crashes on huge buffers
            # (e.g., SystemError: Negative size passed to PyUnicode_New)
            snapshot_text = self._safe_text_snapshot(chunk_chars=500000)
        except (tk.TclError, SystemError) as e:
            snapshot_text = ''
            self.log_message(f"Snapshot error: {type(e).__name__}: {e}")
            try:
                self._mb_showwarning('RCV', 'Text buffer is too large to snapshot safely for this operation.\n\nTip: Use Find in Files / reduce the selection, or keep the buffer under ~950 MiB.')
            except Exception as e:
                self._swallow(e)
            try:
                self.root.configure(cursor='')
            except Exception as e:
                self._swallow(e)
            try:
                self._snap_progress(0)
            except Exception as e:
                self._swallow(e)
            return
        if not snapshot_text:
            self.log_message('Current Tab is empty. Nothing to search in.')
            self._mb_showwarning('RCV', 'Current Tab is empty. Nothing to search in.')
            try:
                self.root.configure(cursor='')
            except Exception as e:
                self._swallow(e)
            self._snap_progress(0)
            return

        output_dir = None
        try:
            if getattr(self, 'file_paths', None):
                output_dir = os.path.dirname(self.file_paths[0])
        except Exception:
            output_dir = None

        # Progress reset + log
        self.ui_queue.put(('set_match_count', 0))
        self.log_message(f"RCV Command search started. Term='{term_text}', Regex={use_regex}, CaseSensitive={case_sensitive}, ShowRules={show_rules}, Save={save}")

        # Launch worker
        self._rcv_thread = threading.Thread(
            target=self._rcv_command_worker,
            args=(snapshot_text, term_text, bool(use_regex), bool(case_sensitive), bool(show_rules), bool(save), output_dir),
            daemon=True
        )
        self._rcv_thread.start()

        # Start UI poller if not already running
        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(50, self._ui_poller)

    def _rcv_command_worker(self, snapshot_text: str, term_text: str, use_regex: bool, case_sensitive: bool, show_rules: bool, save: bool, output_dir):
        """Worker thread for Command-mode cycle-id search (NO Tk calls). Search logic unchanged; adds progress only."""

        def cancelled() -> bool:
            return isinstance(self.search_active, threading.Event) and (not self.search_active.is_set())

        def cancel_exit(log_msg=None):
            detailed = False
            if log_msg:
                self.ui_queue.put(('log', log_msg))
                detailed = True
            self.ui_queue.put(('cancelled', detailed))

        flags = 0 if case_sensitive else re.IGNORECASE
        try:
            pat = re.compile(term_text if use_regex else re.escape(term_text), flags)
        except re.error as e:
            self.ui_queue.put(('log', f"RCV Command regex compilation error: {e}"))
            self.ui_queue.put(('msgbox_error', 'Regex Error 😨', f"Invalid regular expression:\n\n{e}"))
            self.ui_queue.put(('done',))
            return

        lines = snapshot_text.splitlines()
        total_lines = len(lines)
        if total_lines <= 0:
            self.ui_queue.put(('log', 'Current Tab is empty. Nothing to search in.'))
            self.ui_queue.put(('done',))
            return

        hex_pat = re.compile(r"0x[0-9A-Fa-f]+")

        # Helper: extract cycle id from the fixed column (4th column)
        # This avoids accidentally picking other hex values inside parentheses, e.g. pilp=0xe2f5,mse=0x0,ref=0xf5
        def _line_cycle_id(ln: str):
            try:
                parts = ln.split('\t')
                if len(parts) >= 4:
                    cid = parts[3].strip()
                    return cid if cid.startswith('0x') else None
            except Exception as e:
                self._swallow(e)
            # Fallback: first hex token on the line (cycle id appears first in your logs)
            mm = hex_pat.search(ln)
            return mm.group(0) if mm else None

        # Level 1: collect unique cycle IDs where the term matches (row-by-row)
        cycle_ids = []
        seen = set()
        last_pct = -1
        for i, line in enumerate(lines, start=1):
            if cancelled():
                cancel_exit('RCV search cancelled.')
                return
            if not pat.search(line):
                continue
            cid = _line_cycle_id(line)
            if not cid:
                continue
            if cid not in seen:
                seen.add(cid)
                cycle_ids.append(cid)
            if (i % 50000) == 0 or i == total_lines:
                pct = int(2 + 38 * (i / max(1, total_lines)))
                if pct != last_pct:
                    last_pct = pct
                    self.ui_queue.put(('progress', pct))

        # Update Matches once (count of cycle IDs)
        self.ui_queue.put(('set_match_count', len(cycle_ids)))

        if not cycle_ids:
            self.ui_queue.put(('log', f"RCV Command: No cycle IDs found for term: {term_text}"))
            self.ui_queue.put(('progress_instant', 100))
            self.ui_queue.put(('progress_delay', 60, 0))
            self.ui_queue.put(('msgbox_info_delay', 70, 'RCV', 'No matches found.'))
            self.ui_queue.put(('done',))
            return

        # Phase 2: for each cycle id, scan from start and collect lines        
        # Build index map in one pass to avoid O(N*M) scans per cycle id
        target = set(cycle_ids)
        occ = {cid: [] for cid in cycle_ids}
        for idx, ln in enumerate(lines):
            cid = _line_cycle_id(ln)
            if cid and cid in target:
                occ[cid].append(idx)
        
        out_lines = []
        total_cycles = len(cycle_ids)
        next_pct = 1
        self.ui_queue.put(('progress', 40))

        for ci, cid in enumerate(cycle_ids, start=1):
            if cancelled():
                cancel_exit('RCV search cancelled.')
                return

            # Progress in 1% steps (max 100 UI updates)
            pct_f = (ci * 100.0) / max(1, total_cycles)
            while next_pct <= 100 and pct_f >= next_pct:
                mapped = 40.0 + 60.0 * (next_pct / 100.0)
                self.ui_queue.put(('progress', mapped))
                next_pct += 1

            idxs = occ.get(cid, [])
            if len(idxs) < 2:
                msg = f"incomplete info logged for cycle id: {cid} (only {len(idxs)} row(s) found)"
                out_lines.append(msg)
                self.ui_queue.put(('log', msg))
                for j in idxs:
                    out_lines.append(lines[j])
                out_lines.append('')
                continue

            # Prefer the first command/response pair when Show Rules is unchecked
            cmdresp = [j for j in idxs if ('==>' in lines[j] or '<==' in lines[j])]
            pair = cmdresp[:2] if len(cmdresp) >= 2 else idxs[:2]
            out_lines.append(lines[pair[0]])
            out_lines.append(lines[pair[1]])
            if show_rules:
                for j in idxs[2:]:
                    out_lines.append(lines[j])
            out_lines.append('')

        output_text = "\n".join(out_lines).rstrip() + "\n"
        self.ui_queue.put(('progress_instant', 100))

        # Output target: file vs Text area
        if save:
            if not output_dir:
                self.ui_queue.put(('log', 'RCV: Save requested but no input file path is available; outputting to Results tab instead.'))
                self.ui_queue.put(('msgbox_warning', 'RCV', 'Save requested, but no input file path is available. Output will be shown in the Results tab.'))
                self.ui_queue.put(('focus_results',))
                self.ui_queue.put(('clear_results',))
                self.ui_queue.put(('append_text', output_text, None))
                self.ui_queue.put(('done',))
                return

            ts = datetime.now().strftime('%Y%m%d_%H%M%S')
            safe_term = re.sub(r'[^A-Za-z0-9._-]+', '_', term_text)[:60]
            fname = f"Command_{safe_term}_{ts}.log"
            out_path = os.path.join(output_dir, fname)
            try:
                with open(out_path, 'w', encoding='utf-8', newline='\n') as f:
                    f.write(output_text)
                self.ui_queue.put(('log', f"RCV results saved to: {out_path}"))
                self.ui_queue.put(('msgbox_info', 'RCV', 'RCV results saved to:\n' + out_path))
                self.ui_queue.put(('add_file', out_path))
            except Exception as e:
                self.ui_queue.put(('log', f"RCV save error: {type(e).__name__}: {e}"))
                self.ui_queue.put(('msgbox_error', 'RCV', 'Failed to save RCV results: ' + str(e)))
                self.ui_queue.put(('focus_results',))
                self.ui_queue.put(('clear_results',))
                self.ui_queue.put(('append_text', output_text, None))
            self.ui_queue.put(('done',))
            return

        self.ui_queue.put(('focus_results',))
        self.ui_queue.put(('clear_results',))
        self.ui_queue.put(('append_text', output_text, None))
        self.ui_queue.put(('done',))
        return
    
    def start_rcv_search(self, rule_text: str, failed: bool, passed: bool, save: bool, case_sensitive: bool):
        #Run the RCV two-level search against the currently displayed Text content.
        rule_text = (rule_text or '').strip()

        # UI validations
        if not rule_text:
            self._mb_showwarning('RCV', 'Please enter a Rule value.')
            return
        if not failed and not passed:
            self._mb_showwarning('RCV', 'Please select at least one of: Failed / Passed.')
            return

        # Avoid overlap with other background work
        if (self.search_thread and self.search_thread.is_alive()) or (getattr(self, '_rcv_thread', None) and self._rcv_thread.is_alive()):
            self.log_message('A search is already in progress. Cancel it before starting an RCV search.')
            return

        # Ensure cancellation token exists & is set
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()

        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(20, self._ui_poller)
        try:
            self.root.configure(cursor='watch')
        except Exception as e:
            self._swallow(e)
        try:
            self._snap_progress(1)
        except Exception as e:
            self._swallow(e)
        # Determine output directory for Save mode (folder of first loaded file)
        output_dir = None
        try:
            if getattr(self, 'file_paths', None):
                output_dir = os.path.dirname(self.file_paths[0])
        except Exception:
            output_dir = None

        try:
            # IMPORTANT: avoid Tk->Python Unicode conversion crashes on huge buffers
            # (e.g., SystemError: Negative size passed to PyUnicode_New)
            snapshot_text = self._safe_text_snapshot(chunk_chars=500000)
        except (tk.TclError, SystemError) as e:
            snapshot_text = ''
            self.log_message(f"Snapshot error: {type(e).__name__}: {e}")
            try:
                self._mb_showwarning('RCV', 'Text buffer is too large to snapshot safely for this operation.\n\nTip: Use Find in Files / reduce the selection, or keep the buffer under ~950 MiB.')
            except Exception as e:
                self._swallow(e)
            try:
                self.root.configure(cursor='')
            except Exception as e:
                self._swallow(e)
            try:
                self._snap_progress(0)
            except Exception as e:
                self._swallow(e)
            return
        if not snapshot_text:
            self.log_message('Current Tab is empty. Nothing to search in.')
            self._mb_showwarning('RCV', 'Current Tab is empty. Nothing to search in.')
            try:
                self.root.configure(cursor='')
            except Exception as e:
                self._swallow(e)
            self._snap_progress(0)
            return

        self.ui_queue.put(('progress', 2))
        self.ui_queue.put(('set_match_count', 0))
        self.log_message(f"RCV search started. Rule='{rule_text}', Failed={failed}, Passed={passed}, Save={save}")

        # Launch worker
        self._rcv_thread = threading.Thread(
            target=self._rcv_worker,
            args=(snapshot_text, rule_text, failed, passed, save, output_dir, case_sensitive),
            daemon=True
        )
        self._rcv_thread.start()

        # Start UI poller if not already running
        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(50, self._ui_poller)

    def _rcv_worker(self, snapshot_text: str, rule_text: str, failed: bool, passed: bool, save: bool, output_dir, case_sensitive: bool):
        """Worker thread for RCV search (NO Tk calls). Search logic unchanged; adds progress only."""

        def cancelled() -> bool:
            return isinstance(self.search_active, threading.Event) and (not self.search_active.is_set())

        # Helper: unified cancel exit
        def cancel_exit(log_msg=None):
            detailed = False
            if log_msg:
                self.ui_queue.put(('log', log_msg))
                detailed = True
            self.ui_queue.put(('cancelled', detailed))

        # Build level-1 regex pattern
        # NOTE: rule_text is treated as TRUE REGEX (user-provided).

        flags = 0 if case_sensitive else re.IGNORECASE
        try:
            if failed and passed:
                level1_pat = re.compile(rule_text, flags)
                level1_desc = rule_text
            elif failed:
                level1_pat = re.compile(rf"Fail.*{rule_text}", flags)
                level1_desc = f"Fail.*{rule_text}"
            else:
                level1_pat = re.compile(rf"Pass.*{rule_text}", flags)
                level1_desc = f"Pass.*{rule_text}"
        except re.error as e:
            self.ui_queue.put(('log', f"RCV regex compilation error: {e}"))
            self.ui_queue.put(('msgbox_error', 'Regex Error 😨', f"Invalid regular expression:\n\n{e}"))
            self.ui_queue.put(('done',))
            return

        lines = snapshot_text.splitlines()
        total_lines = len(lines)
        if total_lines <= 0:
            self.ui_queue.put(('log', 'Current Tab is empty. Nothing to search in.'))
            self.ui_queue.put(('done',))
            return

        hex_pat = re.compile(r"0x[0-9A-Fa-f]+")

        # Level 1: collect unique cycle_ids (preserve order)
        cycle_ids = []
        seen = set()
        last_pct = -1
        for i, line in enumerate(lines, start=1):
            if cancelled():
                cancel_exit('RCV search cancelled.')
                return
            m = level1_pat.search(line)
            if m:
                prefix = line[:m.start()]
                hexes = hex_pat.findall(prefix)
                if hexes:
                    cid = hexes[-1]
                    if cid not in seen:
                        seen.add(cid)
                        cycle_ids.append(cid)
            if (i % 50000) == 0 or i == total_lines:
                pct = int(2 + 33 * (i / max(1, total_lines)))
                if pct != last_pct:
                    last_pct = pct
                    self.ui_queue.put(('progress', pct))

        self.ui_queue.put(('set_match_count', len(cycle_ids)))

        if not cycle_ids:
            self.ui_queue.put(('log', f"RCV: No matches found for level-1 pattern: {level1_desc}"))
            self.ui_queue.put(('progress_instant', 100))
            self.ui_queue.put(('progress_delay', 60, 0))
            self.ui_queue.put(('msgbox_info_delay', 70, 'RCV', f"No matches found for: {level1_desc}"))
            self.ui_queue.put(('done',))
            return

        # Level 2: map cycle_id -> list of line indices where it appears (single pass)
        target = set(cycle_ids)
        occ = {cid: [] for cid in cycle_ids}
        last_pct = -1
        for i, line in enumerate(lines):
            if cancelled():
                cancel_exit('RCV search cancelled.')
                return
            if '0x' not in line:
                continue
            for hx in hex_pat.findall(line):
                if hx in target:
                    occ[hx].append(i)
            if (i % 50000) == 0 or i == total_lines - 1:
                pct = int(35 + 30 * (i / max(1, total_lines)))
                if pct != last_pct:
                    last_pct = pct
                    self.ui_queue.put(('progress', pct))

        # Compile once
        try:
            rule_pat = re.compile(rule_text, flags)
        except re.error as e:
            self.ui_queue.put(('log', f"RCV rule regex compilation error: {e}"))
            self.ui_queue.put(('msgbox_error', 'Regex Error 😨', f"Invalid rule regex:\n\n{e}"))
            self.ui_queue.put(('done',))
            return

        out_lines = []
        incomplete_msgs = []
        total_cycles = len(cycle_ids)
        last_pct = -1

        for ci, cid in enumerate(cycle_ids, start=1):
            if cancelled():
                cancel_exit('RCV search cancelled.')
                return
            idxs = occ.get(cid, [])
            # Need at least 3 lines ideally, but handle incomplete cases
            if len(idxs) < 2:
                msg = f"incomplete info logged for cycle id: {cid} (only {len(idxs)} row(s) found)"
                incomplete_msgs.append(msg)
                out_lines.append(msg)
                for j in idxs:
                    out_lines.append(lines[j])
                out_lines.append('')
            else:
                row1 = lines[idxs[0]]
                row2 = lines[idxs[1]]
                row3 = None
            # Search remaining occurrences for the one containing BOTH cid and rule text
                for j in idxs[2:]:
                    if rule_pat.search(lines[j]):
                        row3 = lines[j]
                        break
                if row3 is None:
                # Either only two occurrences exist, or none of the later ones match the rule
                    msg = f"incomplete info logged for cycle id: {cid} (expected 3rd row containing rule '{rule_text}' not found)"
                    incomplete_msgs.append(msg)
                    out_lines.extend([row1, row2, msg, ''])
                else:
                    out_lines.extend([row1, row2, row3, ''])

            pct = int(65 + 35 * (ci / max(1, total_cycles)))
            if pct != last_pct:
                last_pct = pct
                self.ui_queue.put(('progress', pct))

        # Log incomplete messages to events logger
        for msg in incomplete_msgs:
            self.ui_queue.put(('log', msg))

        output_text = "\n".join(out_lines).rstrip() + "\n"
        self.ui_queue.put(('progress_instant', 100))

        if save:
            if not output_dir:
                # No known path (no files loaded) -> fallback to Text area
                self.ui_queue.put(('log', 'RCV: Save requested but no input file path is available; outputting to Results tab instead.'))
                self.ui_queue.put(('msgbox_warning', 'RCV', 'Save requested, but no input file path is available. Output will be shown in the Results tab.'))
                self.ui_queue.put(('focus_results',))
                self.ui_queue.put(('clear_results',))
                self.ui_queue.put(('append_text', output_text, None))
                self.ui_queue.put(('done',))
                return

            ts = datetime.now().strftime('%Y%m%d_%H%M%S')
            safe_rule = re.sub(r'[^A-Za-z0-9._-]+', '_', rule_text)
            fname = f"Rule_{safe_rule}_{ts}.log"
            out_path = os.path.join(output_dir, fname)
            try:
                with open(out_path, 'w', encoding='utf-8', newline='\n') as f:
                    f.write(output_text)
                self.ui_queue.put(('log', f"RCV results saved to: {out_path}"))
                self.ui_queue.put(('msgbox_info', 'RCV', f"RCV results saved to:\n{out_path}"))
                self.ui_queue.put(('add_file', out_path))
            except Exception as e:
                self.ui_queue.put(('log', f"RCV save error: {type(e).__name__}: {e}"))
                self.ui_queue.put(('msgbox_error', 'RCV', f"Failed to save RCV results: {e}"))
                # Fallback: show in Text area
                self.ui_queue.put(('focus_results',))
                self.ui_queue.put(('clear_results',))
                self.ui_queue.put(('append_text', output_text, None))
            self.ui_queue.put(('done',))
            return

        # Not saving: display in results area (replace previous contents)
        self.ui_queue.put(('focus_results',))
        self.ui_queue.put(('clear_results',))
        self.ui_queue.put(('append_text', output_text, None))
        self.ui_queue.put(('done',))
        return

    # -------------------- Context menu & helpers --------------------
    def create_context_menu(self):
        # Build a context menu for the file list (remove / decode)."""
        self.context_menu = tk.Menu(self.root, tearoff=0)
        self.context_menu.add_command(label="Open in Tab", command=self._open_selected_in_tab)
        self.context_menu.add_separator()
        self.context_menu.add_command(label="Remove Selected", command=self.remove_selected_files)
        self.context_menu.add_command(label="Decode dmesg", command=self.decode_selected_file)

        # Bind right-click to show context menu
        self.file_listbox.bind("<Button-3>", self.show_context_menu)
        self.file_listbox.bind("<App>", self.show_context_menu)

    def show_context_menu(self, event):
        # Popup context menu near cursor or selected item (mouse or keyboard).
        try:
            # Ensure the item under the cursor is selected when there is no selection.
            if not self.file_listbox.curselection():
                index = self.file_listbox.nearest(event.y)
                self.file_listbox.selection_set(index)

            # Update the first menu label: Open in Tab vs Open in Tabs
            try:
                nsel = len(self.file_listbox.curselection())
            except Exception:
                nsel = 0
            label = 'Open in Tabs' if nsel > 1 else 'Open in Tab'
            try:
                self.context_menu.entryconfig(0, label=label)
            except Exception:
                pass

            # Mouse right-click → show at mouse pointer
            if event.type == tk.EventType.ButtonPress:
                self.context_menu.tk_popup(event.x_root, event.y_root)

            # Keyboard context-menu key → show next to selected item
            elif event.type == tk.EventType.KeyPress:
                index = self.file_listbox.curselection()[0]
                bbox = self.file_listbox.bbox(index)  # (x, y, width, height)

                if bbox:
                    x, y, width, height = bbox
                    x_root = self.file_listbox.winfo_rootx() + x + width
                    y_root = self.file_listbox.winfo_rooty() + y + height
                    self.context_menu.tk_popup(x_root, y_root)
        finally:
            try:
                self.context_menu.grab_release()
            except Exception:
                pass

    def remove_selected_files(self):
        # Remove selected entries from listbox and file_paths.
        selected_indices = self.file_listbox.curselection()
        if not selected_indices:
            self.log_message("No file selected to remove.")
            return
        for i in reversed(selected_indices):
            self.file_listbox.delete(i)
            try:
                p = os.path.normpath(self.file_paths[i])
                if p in self._file_size_cache:
                    del self._file_size_cache[p]
            except Exception as e:
                self._swallow(e)
            del self.file_paths[i]
        self.update_selection_label()
        self.log_message(f"{len(selected_indices)} file(s) removed.")

    # ------------ Misc utilities & messageboxes ------------
    def show_about(self):
        self._mb_showinfo(
            "App info",
            "Description:  DAT file searching and Dmesg decoder tool\n\n"
            "Version:      1.6\n"
            "Pilot:           Santiago Molina\n"
            "Copilot:      Yes, please\n\n"
            "Details:\n\nBesides of doing traditional text searches on one or multiple files loaded, this tool can help filtering specific searches on RCV's DAT files like command parameters and rule hits. Also, can decode Dmesg files for quicker user analysis\n"
        )

    def _debug(self, msg):
        # Console-only debug logger for internal instrumentation.
        # IMPORTANT: This is separate from the Events logger widget (log_message).
        # Toggle via self.DEBUG_HIGHLIGHT or environment variable DAT_SEARCH_TOOL_DEBUG.
        if getattr(self, 'DEBUG_HIGHLIGHT', False):
            try:
                print(msg)
            except Exception:
                pass

    def _swallow(self, e: Exception, prefix: str = ''):
        """Swallow exceptions in UI-only best-effort blocks.

        When DEBUG_HIGHLIGHT is enabled, emit details to console via _debug()
        (keeps the app running while still providing diagnostics).
        """
        try:
            if not bool(getattr(self, 'DEBUG_HIGHLIGHT', False)):
                return
        except Exception:
            return
        try:
            tb = traceback.format_exc()
        except Exception:
            tb = ''
        try:
            pfx = (prefix + ' ' if prefix else '')
            self._debug(f"[SAFE] {pfx}{type(e).__name__}: {e}\n{tb}")
        except Exception:
            pass

    def _try(self, fn, *args, prefix: str = '', default=None, **kwargs):
        """Execute fn(*args, **kwargs) and swallow exceptions (UI-only).

        Returns `default` when an exception occurs.
        """
        try:
            return fn(*args, **kwargs)
        except Exception as e:
            self._swallow(e, prefix=prefix)
            return default
    
    def log_message(self, message):
        # Append a timestamped message to the events logger.
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S.%f')[:-3]  # millisecond precision
        event = f"[{timestamp}] {message}"
        self.log_box.config(state='normal')
        self.log_box.insert(tk.END, '\n'+ event)
        self.log_box.config(state='disabled')
        self.log_box.see(tk.END)

    def _update_match_count(self, count: int):
        # Update Matches label with comma separators (e.g., 12,345).
        self.count_label.config(text=f"Matches: {count:,}")

    def _restore_find_dialog_focus(self):

        fw = getattr(self, 'find_win', None)
        if fw is None:
            return

        try:
            if not fw.winfo_exists():
                return
        except Exception:
            return

        try:
            fw.deiconify()
            fw.lift()
            fw.focus_force()
        except Exception as e:
            self._swallow(e)
        def _focus_entry():

            try:
                nb = getattr(self, '_find_notebook', None)
                tab_text = 'Find'

                if nb is not None and nb.winfo_exists():
                    tab_text = nb.tab(nb.select(), 'text')

                if tab_text == 'RCV':
                    w = getattr(self, 'rcv_rule_entry', None)

                else:
                    w = getattr(self, '_find_entry', None)

                if w is not None and w.winfo_exists():
                    w.focus_set()

                    try:
                        w.icursor('end')

                    except Exception as e:
                        self._swallow(e)
            except Exception as e:
                self._swallow(e)
        self.root.after_idle(_focus_entry)

    def _mb_showinfo(self, title, msg):
        from tkinter import messagebox as _mb
        _mb.showinfo(title, msg)
        self._restore_find_dialog_focus()

    def _mb_showwarning(self, title, msg):
        from tkinter import messagebox as _mb
        _mb.showwarning(title, msg)
        self._restore_find_dialog_focus()

    def _mb_showerror(self, title, msg):
        from tkinter import messagebox as _mb
        _mb.showerror(title, msg)
        self._restore_find_dialog_focus()

    def _mb_askyesno(self, title, msg):
        from tkinter import messagebox as _mb
        res = _mb.askyesno(title, msg)
        self._restore_find_dialog_focus()
        return res

    def _require_nonempty_term(self, term: str) -> bool:
        # Return True if term is non-empty; otherwise show a warning and return False.
        if not term:
            self._mb_showwarning("Input Error", "Please enter a search term.")
            return False
        return True

    def _safe_text_snapshot(self, chunk_chars: int = 2000000) -> str:
        """Safely snapshot Text widget content in chunks to avoid rare Tk->Python Unicode conversion crashes."""
        try:
            end_idx = 'end-1c'
            if self.result_box.compare(end_idx, '==', '1.0'):
                return ''
        except Exception as e:
            self._swallow(e)
        parts = []
        start = '1.0'
        try:
            while True:
                nxt = self.result_box.index(f'{start}+{int(chunk_chars)}c')
                try:
                    chunk = self.result_box.get(start, nxt)
                except Exception:
                    # Includes SystemError seen on huge buffers
                    raise
                if chunk:
                    parts.append(chunk)
                if self.result_box.compare(nxt, '>=', end_idx):
                    break
                start = nxt
        except Exception as e:
            self.log_message(f'Snapshot error: {type(e).__name__}: {e}')
            raise
        return ''.join(parts)

    def _require_nonempty_text_area(self) -> bool:
        # Fast emptiness check: compare indices (no buffer copy).
        if self.result_box.compare("end-1c", "==", "1.0"):
            self.log_message("Current Tab is empty. Nothing to search in.")
            return False
        return True

    def _is_background_busy(self) -> bool:
        """Return True if any background operation is currently running."""
        try:
            if getattr(self, 'search_thread', None) is not None and self.search_thread.is_alive():
                return True
        except Exception as e:
            self._swallow(e)
        try:
            if getattr(self, '_rcv_thread', None) is not None and self._rcv_thread.is_alive():
                return True
        except Exception as e:
            self._swallow(e)
        try:
            if getattr(self, '_findall_thread', None) is not None and self._findall_thread.is_alive():
                return True
        except Exception as e:
            self._swallow(e)
        try:
            if getattr(self, '_decode_thread', None) is not None and self._decode_thread.is_alive():
                return True
        except Exception as e:
            self._swallow(e)
        try:
            if getattr(self, 'ui_queue', None) is not None and (not self.ui_queue.empty()):
                return True
        except Exception as e:
            self._swallow(e)
        return False

    def on_close(self):
        # Ask for confirmation before exiting (prevents accidental close via X / Ctrl+Q)
        if getattr(self, '_closing', False):
            return

        busy = False
        try:
            busy = bool(self._is_background_busy())
        except Exception:
            busy = False

        msg = 'Are you sure you want to close the app?'
        if busy:
            msg = 'A background operation is still running.\n\nCancel it and exit the app?'

        try:
            if not self._mb_askyesno('Quit', msg):
                return
        except Exception:
            return

        if busy:
            try:
                if isinstance(self.search_active, threading.Event):
                    self.search_active.clear()
            except Exception as e:
                self._swallow(e)
        # Handle unsaved tabs before shutting down
        try:
            res_id = getattr(self, '_results_tab_id', None)
            tab_ids = list(self.workspace.tabs()) if hasattr(self, 'workspace') else list(self._tabs.keys())
            dirty_tabs = [tid for tid in tab_ids if tid != res_id and self._tabs.get(tid, {}).get('modified')]
        except Exception:
            dirty_tabs = []

        for tid in list(dirty_tabs):
            try:
                self.workspace.select(tid)
                self._on_workspace_tab_changed()
            except Exception as e:
                self._swallow(e)
            st = self._tabs.get(tid)
            if not st or (not st.get('modified')):
                continue

            choice = self._ask_modified_tab_action(tid)
            if choice == 'cancel':
                return
            if choice == 'save':
                self.save_current_tab()
                st2 = self._tabs.get(tid)
                if st2 and st2.get('modified'):
                    return
            elif choice == 'export':
                ok = self._export_current_tab_for_close()
                if not ok:
                    return
            elif choice == 'discard':
                pass

        self._closing = True

        try:
            if isinstance(self.search_active, threading.Event):
                self.search_active.clear()
        except Exception as e:
            self._swallow(e)
        try:
            if self._ui_poller_id is not None:
                self.root.after_cancel(self._ui_poller_id)
                self._ui_poller_id = None
        except Exception as e:
            self._swallow(e)
        try:
            if self.search_thread and self.search_thread.is_alive():
                self.search_thread.join(timeout=0.5)
        except Exception as e:
            self._swallow(e)
        try:
            self.root.destroy()
        except Exception as e:
            self._swallow(e)

    def decode_selected_file(self):
        """Decode selected dmesg file(s) using a worker thread (non-blocking UI)."""
        # Prevent overlap with other background operations
        if (self.search_thread and self.search_thread.is_alive()) or (getattr(self, '_rcv_thread', None) and self._rcv_thread.is_alive()) or (getattr(self, '_decode_thread', None) and self._decode_thread.is_alive()):
            self.log_message('A background operation is already in progress. Cancel it before starting Decode dmesg.')
            return
        selected_indices = self.file_listbox.curselection()
        if not selected_indices:
            self._mb_showerror('Decode dmesg', 'No file selected.')
            return
        file_paths = [self.file_paths[i] for i in selected_indices]
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()
        self.ui_queue.put(('cursor', 'watch'))
        self.ui_queue.put(('log', f'Decode dmesg started for {len(file_paths)} file(s).'))
        self._decode_thread = threading.Thread(target=self._decode_dmesg_worker, args=(file_paths,), daemon=True)
        self._decode_thread.start()
        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(50, self._ui_poller)

    def _decode_dmesg_worker(self, file_paths):
        """Worker thread: decode one or more dmesg files. NO Tk calls here.

        - Uses bytes-based progress (single pass) from _decode_dmesg_one.
        - Avoids animated progress rollback at completion.
        - Posts a single completion event with accurate total elapsed time.
        - Defers informational messagebox until after the completion event is posted.
        """

        def cancelled():
            return isinstance(self.search_active, threading.Event) and (not self.search_active.is_set())

        t_run0 = time.perf_counter()
        total_files = len(file_paths or [])
        ok_files = 0
        out_paths = []

        for file_path in (file_paths or []):
            if cancelled():
                self.ui_queue.put(('cursor', ''))
                self.ui_queue.put(('cancelled', False))
                return

            filename = os.path.basename(file_path)
            t0 = time.perf_counter()

            # Start-of-file status
            self.ui_queue.put(('log', f'Decode dmesg started: {filename}'))
            # Start progress immediately (no animation artefacts)
            self.ui_queue.put(('progress_instant', 0))

            ok, msg, out_path, lines_seen = self._decode_dmesg_one(file_path, cancelled)
            dt_file = time.perf_counter() - t0

            if cancelled():
                self.ui_queue.put(('cursor', ''))
                self.ui_queue.put(('cancelled', False))
                return

            if not ok:
                self.ui_queue.put(('log', f'Decode dmesg failed: {filename} - {msg}'))
                self.ui_queue.put(('msgbox_error', 'Decode dmesg', f'{filename}: {msg}'))
                continue

            ok_files += 1
            out_paths.append(out_path)

            # File completion log (includes accurate per-file elapsed time)
            try:
                out_base = os.path.basename(out_path)
            except Exception:
                out_base = str(out_path)
            self.ui_queue.put(('log', f'Decode dmesg finished: {filename} -> {out_base} ({lines_seen:,} lines) in {dt_file:.2f}s'))
            self.ui_queue.put(('add_file', out_path))

        # Whole-run completion
        dt_total = time.perf_counter() - t_run0

        # Make sure progress shows complete (no animated rollback)
        self.ui_queue.put(('progress_instant', 100))
        self.ui_queue.put(('cursor', ''))

        # Post completion event with accurate elapsed time and counts
        self.ui_queue.put(('decode_done', dt_total, total_files, ok_files))

        # Defer informational messagebox until AFTER completion event is posted
        if out_paths:
            if len(out_paths) == 1:
                self.ui_queue.put(('msgbox_info', 'Decode dmesg', f'Decoded log saved to:\n{out_paths[0]}'))
            else:
                shown = '\n'.join(out_paths[:5])
                more = '' if len(out_paths) <= 5 else f"\n... and {len(out_paths) - 5} more"
                self.ui_queue.put(('msgbox_info', 'Decode dmesg', f'Decoded logs saved to:\n{shown}{more}'))

    def _decode_dmesg_one(self, file_path: str, cancelled_cb):
        """Decode a single file. Returns (ok, message, output_path, lines_seen).

        Worker-safe: NO Tk calls. Posts progress via ui_queue (bytes-based).
        """
        try:
            total_bytes = os.path.getsize(file_path)
        except OSError as e:
            return False, f'Cannot read file size: {e}', None, 0
        if total_bytes <= 0:
            return False, 'Selected file is empty.', None, 0

        base, _ext = os.path.splitext(file_path)
        output_path = base + '_decoded.log'

        import codecs
        decoder = codecs.getincrementaldecoder('utf-8')(errors='replace')
        buf = ''
        bytes_read = 0
        last_pct = -1
        lines_seen = 0
        found_nvme = False

        try:
            with open(file_path, 'rb') as fin, open(output_path, 'w', encoding='utf-8', newline='\n') as fout:
                sct_sc_dict = self.get_sct_sc_dict()

                while True:
                    if cancelled_cb():
                        raise RuntimeError('cancelled')
                    chunk = fin.read(1024 * 1024)
                    if not chunk:
                        break
                    bytes_read += len(chunk)
                    buf += decoder.decode(chunk)
                    parts = buf.splitlines(True)
                    if parts and not (parts[-1].endswith('\n') or parts[-1].endswith('\r')):
                        buf = parts.pop()
                    else:
                        buf = ''
                    for line in parts:
                        lines_seen += 1
                        if '<-RES' in line:
                            found_nvme = True
                            fout.write(self.decode_Response(line, sct_sc_dict))
                        elif 'REQ->' in line:
                            found_nvme = True
                            fout.write(self.decode_Request(line))
                        else:
                            fout.write(line)
                    pct = int((bytes_read * 100) / total_bytes)
                    if pct != last_pct:
                        last_pct = pct
                        self.ui_queue.put(('progress', pct))
                buf += decoder.decode(b'', final=True)
                for line in buf.splitlines(True):
                    if not line:
                        continue
                    lines_seen += 1
                    if '<-RES' in line:
                        found_nvme = True
                        fout.write(self.decode_Response(line, sct_sc_dict))
                    elif 'REQ->' in line:
                        found_nvme = True
                        fout.write(self.decode_Request(line))
                    else:
                        fout.write(line)
        except RuntimeError as e:
            try:
                if os.path.exists(output_path):
                    os.remove(output_path)
            except Exception as e:
                self._swallow(e)
            if str(e) == 'cancelled':
                return False, 'Decode cancelled.', None, lines_seen
            return False, str(e), None, lines_seen
        except Exception as e:
            try:
                if os.path.exists(output_path):
                    os.remove(output_path)
            except Exception as e:
                self._swallow(e)
            return False, f'{type(e).__name__}: {e}', None, lines_seen

        if not found_nvme:
            try:
                if os.path.exists(output_path):
                    os.remove(output_path)
            except Exception as e:
                self._swallow(e)
            return False, 'No NVMe debug driver entries found for the selected file.', None, lines_seen

        return True, 'OK', output_path, lines_seen

    def decode_Response(self, line, sct_sc_dict):
        match = re.search(r'sct\s+0x\(?([0-9A-Fa-f]+)\)?\s+sc\s+0x\(?([0-9A-Fa-f]+)\)?', line)
        if not match:
            return line  # No SCT/SC found

        sct_hex = str(int(match.group(1), 16)) + 'h'  # Converts '01' to '1h'
        sc_hex = match.group(2).upper().zfill(2) + 'h'  # Keeps '0A' as '0Ah'

        decoded = sct_sc_dict.get(sct_hex, {}).get(sc_hex, "No Match found for such Status Code")
        return line.rstrip() + f"                 --- Decoding: {decoded}\n"

    def decode_Request(self, line):
        import re

        # Extract qid
        qid_match = re.search(r'qid\s+\(?((0x[0-9A-Fa-f]+))\)?', line)
        qid = qid_match.group(2) if qid_match else '0x00'
        cmd_type = "Admin Cmd" if qid == "0x00" else "IO Cmd"

        # Extract opcode
        opcode_match = re.search(r'opcode\s+\(?((0x[0-9A-Fa-f]+))\)?', line)
        opcode = opcode_match.group(2) if opcode_match else '0x00'
        cmd_name = self.get_command_name(cmd_type, opcode)
        # Extract NSID
        nsid_match = re.search(r'nsid\s+\(?((0x[0-9A-Fa-f]+))\)?', line)
        nsid_hex = nsid_match.group(2) if nsid_match else '0x00'
        if nsid_hex.lower() == "0xffffffff":
            nsid_text = "NSID = 0xFFFFFFFF (broadcast to all NS's)"
        else:
            nsid_dec = int(nsid_hex, 16)
            nsid_text = f"NSID = {nsid_dec}"

        # Extract CDW10 to CDW15
        cdw_match = re.search(r'cdw10-15\s+\[(.*?)\]', line)
        cdw_raw = cdw_match.group(1).split() if cdw_match else ["0x00"] * 6
        # print("CDW Raw = "+str(cdw_raw)+"\n")      # uncomment for debug purposes

        cdw_lists = []
        #dword = 10
        for hex_val in cdw_raw:
            bin_str = bin(int(hex_val, 16))[2:].zfill(32)
            reversed_bits = list(map(int, bin_str[::-1]))
            cdw_lists.append(reversed_bits)
            #print("Dword "+str(dword)+" = "+str(reversed_bits)+"\n")       # uncomment for debugging purposes
            #dword+=1

        cdw10_list, cdw11_list, cdw12_list, cdw13_list, cdw14_list, cdw15_list = cdw_lists

        # Decode command-specific fields via dispatcher (separate from command-name decoding)

        decoded_text = self.decode_command_fields(cmd_type, opcode, cdw10_list, cdw11_list, cdw12_list, cdw13_list, cdw14_list, cdw15_list)

        # Construct final line
        final_line = line.rstrip() + f" --- Decoding: {cmd_type} {cmd_name} {nsid_text} {decoded_text}\n"
        return final_line
    
    def decode_dmesg(self, file_path):
        """Decode a single dmesg file using the worker-thread implementation."""
        if getattr(self, '_decode_thread', None) and self._decode_thread.is_alive():
            self.log_message('Decode already in progress.')
            return
        if not isinstance(self.search_active, threading.Event):
            self.search_active = threading.Event()
        self.search_active.set()
        self.ui_queue.put(('cursor', 'watch'))
        self._decode_thread = threading.Thread(target=self._decode_dmesg_worker, args=([file_path],), daemon=True)
        self._decode_thread.start()
        if self._ui_poller_id is None:
            self._ui_poller_id = self.root.after(50, self._ui_poller)

    def decode_admin_opcode(self, opcode):
        opcode_dict = {
            "0x00": "Delete I/O Submission Queue",
            "0x01": "Create I/O Submission Queue",
            "0x02": "Get Log Page",
            "0x04": "Delete I/O Completion Queue",
            "0x05": "Create I/O Completion Queue",
            "0x06": "Identify",
            "0x08": "Abort",
            "0x09": "Set Features",
            "0x0A": "Get Features",
            "0x0C": "Asynchronous Event Request",
            "0x0D": "Namespace Management",
            "0x10": "Firmware Commit",
            "0x11": "Firmware Image Download",
            "0x14": "Device Self-test",
            "0x15": "Namespace Attachment",
            "0x18": "Keep Alive",
            "0x19": "Directive Send",
            "0x1A": "Directive Receive",
            "0x1C": "Virtualization Management",
            "0x1D": "NVMe-MI Send",
            "0x1E": "NVMe-MI Receive",
            "0x20": "Capacity Management",
            "0x21": "Discovery Information Management",
            "0x22": "Fabric Zoning Receive",
            "0x24": "Lockdown",
            "0x25": "Fabric Zoning Lookup",
            "0x28": "Clear Exported NVM Resource Configuration",
            "0x2A": "Create Exported NVM Subsystem",
            "0x2D": "Manage Exported NVM Subsystem",
            "0x31": "Manage Exported Namespace",
            "0x35": "Manage Exported Port",
            "0x39": "Send Discovery Log Page",
            "0x3D": "Track Send",
            "0x3E": "Track Receive",
            "0x41": "Migration Send",
            "0x42": "Migration Receive",
            "0x45": "Controller Data Queue",
            "0x7C": "Doorbell Buffer Config",
            "0x7F": "Fabrics Commands",
            "0x80": "Format NVM",
            "0x81": "Security Send",
            "0x82": "Security Receive",
            "0x84": "Sanitize",
            "0x85": "Load Program",
            "0x86": "Get LBA Status",
            "0x88": "Program Activation Management",
            "0x89": "Memory Range Set Management",
            "0xE1": "Test Command - Write",
            "0xE2": "Test Command - Read"
        }

        if opcode in opcode_dict:
            opcode_name = opcode_dict[opcode]
        elif 192 <= int(opcode, 16) <= 255:
            opcode_name = "Vendor Specific"
        else:
            opcode_name = f"[Unknown Opcode: ({opcode})]"

        return opcode_name

    def decode_io_opcode(self, opcode):
        """Decode NVM Command Set I/O opcode (SQE OPC for non-admin queues).

        Source: NVM Express NVM Command Set Specification Rev 1.2, Figure 21 (Opcodes for NVM Commands).
        Notes:
          - Vendor specific range for NVM I/O commands: 0x80-0xFF
          - Opcodes not listed in Figure 21 are reserved
        """
        io_opcode_dict = {
            "0x00": "Flush",
            "0x01": "Write",
            "0x02": "Read",
            "0x04": "Write Uncorrectable",
            "0x05": "Compare",
            "0x08": "Write Zeroes",
            "0x09": "Dataset Management",
            "0x0C": "Verify",
            "0x0D": "Reservation Register",
            "0x0E": "Reservation Report",
            "0x11": "Reservation Acquire",
            "0x12": "I/O Management Receive",
            "0x15": "Reservation Release",
            "0x18": "Cancel",
            "0x19": "Copy",
            "0x1D": "I/O Management Send",
        }

        if opcode in io_opcode_dict:
            return io_opcode_dict[opcode]

        # Vendor Specific I/O opcodes are 0x80 to 0xFF
        try:
            if 128 <= int(opcode, 16) <= 255:
                return "Vendor Specific"
        except Exception:
            pass

        return f"[Unknown IO Opcode: ({opcode})]"

    def get_command_name(self, cmd_type, opcode):
        """Return a human-readable command name based on cmd_type and opcode.

        This method intentionally decouples command-name decoding from per-command field decoding.
        """
        if cmd_type == "Admin Cmd":
            return self.decode_admin_opcode(opcode)
        return self.decode_io_opcode(opcode)

    def decode_io_not_implemented(self, cmd_name):
        """Placeholder field decoder for I/O commands not yet implemented."""
        return f"[Decode pending for IO command: {cmd_name}]"

    def decode_command_fields(self, cmd_type, opcode, cdw10_list, cdw11_list, cdw12_list, cdw13_list, cdw14_list, cdw15_list):
        """Decode command-specific fields (CDW10-15) based on cmd_type and opcode.

        This keeps field decoding separate from command name decoding (see get_command_name()).
        """
        # Dispatcher dictionaries
        admin_dispatcher = {
            "0x00": lambda: self.decode_delete_io_submission_or_completion_queue(cdw10_list),
            "0x01": lambda: self.decode_create_io_submission_queue(cdw10_list, cdw11_list, cdw12_list),
            "0x02": lambda: self.decode_get_log_page(cdw10_list, cdw11_list, cdw12_list, cdw13_list, cdw14_list),
            "0x04": lambda: self.decode_delete_io_submission_or_completion_queue(cdw10_list),
            "0x05": lambda: self.decode_create_io_completion_queue(cdw10_list, cdw11_list),
            "0x06": lambda: self.decode_identify(cdw10_list, cdw11_list, cdw14_list),
            "0x08": lambda: self.decode_abort(cdw10_list),
            "0x09": lambda: self.decode_set_features(cdw10_list, cdw14_list),
            "0x0A": lambda: self.decode_get_features(cdw10_list, cdw14_list),
            "0x0C": lambda: self.decode_asynchronous_event_request(),
            "0x0D": lambda: self.decode_namespace_management(cdw10_list, cdw11_list),
            "0x10": lambda: self.decode_firmware_commit(cdw10_list),
            "0x11": lambda: self.decode_firmware_download(cdw10_list, cdw11_list),
            "0x14": lambda: self.decode_device_self_test(cdw10_list),
            "0x15": lambda: self.decode_namespace_attachment(cdw10_list),
            "0x19": lambda: self.decode_directive_send_or_receive(cdw10_list, cdw11_list, cdw12_list, cdw13_list),
            "0x1A": lambda: self.decode_directive_send_or_receive(cdw10_list, cdw11_list, cdw12_list, cdw13_list),
            "0x1C": lambda: self.decode_virtualization_management(cdw10_list, cdw11_list),
            "0x80": lambda: self.decode_format_nvm(cdw10_list),
            "0x84": lambda: self.decode_sanitize(cdw10_list, cdw11_list),
            # Add more Admin command decoders here
        }

        # NVM Command Set I/O opcode dispatcher (Figure 21)
        # For this phase, these are stubs that prove we correctly route to the IO dispatcher.
        io_dispatcher = {
            "0x00": lambda: self.decode_io_not_implemented("Flush"),
            "0x01": lambda: self.decode_io_not_implemented("Write"),
            "0x02": lambda: self.decode_io_not_implemented("Read"),
            "0x04": lambda: self.decode_io_not_implemented("Write Uncorrectable"),
            "0x05": lambda: self.decode_io_not_implemented("Compare"),
            "0x08": lambda: self.decode_io_not_implemented("Write Zeroes"),
            "0x09": lambda: self.decode_io_not_implemented("Dataset Management"),
            "0x0C": lambda: self.decode_io_not_implemented("Verify"),
            "0x0D": lambda: self.decode_io_not_implemented("Reservation Register"),
            "0x0E": lambda: self.decode_io_not_implemented("Reservation Report"),
            "0x11": lambda: self.decode_io_not_implemented("Reservation Acquire"),
            "0x12": lambda: self.decode_io_not_implemented("I/O Management Receive"),
            "0x15": lambda: self.decode_io_not_implemented("Reservation Release"),
            "0x18": lambda: self.decode_io_not_implemented("Cancel"),
            "0x19": lambda: self.decode_io_not_implemented("Copy"),
            "0x1D": lambda: self.decode_io_not_implemented("I/O Management Send"),
        }

        # Select appropriate decoder
        if cmd_type == "Admin Cmd":
            decode_func = admin_dispatcher.get(opcode, lambda: "[Unknown Admin Command]")
            return decode_func()

        # IO command path
        try:
            if 128 <= int(opcode, 16) <= 255:
                return "[Vendor Specific IO Command]"
        except Exception:
            pass

        decode_func = io_dispatcher.get(opcode, lambda: "[Unknown IO Command]")
        return decode_func()


    def decode_csi(self, command_set_identifier):
        csi_dict = {
            0:  "NVM Command Set",                              # NVM Command Set Specification
            1:  "Key Value Command Set",                        # Key Value Command Set Specification
            2:  "Zoned Namespace Command Set",                  # Zoned Namespace Command Set Specification
            3:  "Subsystem Local Memory Command Set",           # Subsystem Local Memory Command Set Specification
            4:  "Computational Programs Command Set",           # Computational Programs Command Set Specification
            # 05-2F: Reserved
            # 30-3F: Vendor Specific
            # 40-FF: Reserved
        }

        csi = csi_dict.get(int(command_set_identifier), f"[Unknown CSI: ({command_set_identifier})]")
        return csi

    def decode_fid(self, feature_identifier):

        fid_dict = {
            1: "Arbitration",
            2: "Power Management",
            3: "LBA Range Type",
            4: "Temperature Threshold",
            5: "Error Recovery",
            6: "Volatile Write Cache",
            7: "Number of Queues",
            8: "Interrupt Coalescing",
            9: "Interrupt Vector Configuration",
            10: "Write Atomicity Normal",
            11: "Asynchronous Event Configuration",
            12: "Autonomous Power State Transition",
            13: "Host Memory Buffer",
            14: "Timestamp",
            15: "Keep Alive Timer",
            16: "Host Controlled Thermal Management",
            17: "Non-Operational Power State Config",
            18: "Read Recovery Level Config",
            19: "Predictable Latency Mode Config",
            20: "Predictable Latency Mode Window",
            21: "LBA Status Information Attributes",
            22: "Host Behavior Support",
            23: "Sanitize Config",
            24: "Endurance Group Event Configuration",
            25: "I/O Command Set Profile",
            26: "Spinup Control",
            27: "Power Loss Signaling Config",
            28: "Performance Characteristics",
            29: "Flexible Data Placement",
            30: "Flexible Data Placement Events",
            31: "Namespace Admin Label",
            33: "Controller Data Queue",
            120: "Embedded Management Controller Address",
            121: "Host Management Agent Address",
            125: "Enhanced Controller Metadata",
            126: "Controller Metadata",
            127: "Namespace Metadata",
            128: "Software Progress Marker",
            129: "Host Identifier",
            130: "Reservation Notification Mask",
            131: "Reservation Persistence",
            132: "Namespace Write Protection Config",
            133: "Boot Partition Write Protection Config"
        }

        if feature_identifier in fid_dict:
            fid = fid_dict[feature_identifier]
        elif 192 <= feature_identifier <= 255:
            fid = "Vendor Specific"
        else:
            fid = f"[Unknown FID: ({feature_identifier})]"

        return fid

    def decode_bits_value(self, my_list, index_start, index_end):
        # Extract the sublist from index_start to index_end (inclusive)
        bits = my_list[index_start:index_end + 1]

        # Reverse the order of bits
        bits = bits[::-1]

        # Convert list of bits to a string
        binary_str = ''.join(str(bit) for bit in bits)
        #print("start: "+str(index_start)+" end: "+str(index_end)+" binary string = "+str(binary_str))      # uncomment for debug purposes

        # Convert binary string to decimal
        decimal_value = int(binary_str, 2)

        return str(decimal_value)

    def decode_delete_io_submission_or_completion_queue(self, cdw10):                       # Admin cmd 00h & 04h
        queue_identifier = self.decode_bits_value(cdw10, 0, 15)
        decoded_text_line = ("QID: " + queue_identifier)

        return decoded_text_line

    def decode_create_io_submission_queue(self, cdw10, cdw11, cdw12):                       # Admin cmd 01h
        queue_identifier            = self.decode_bits_value(cdw10, 0, 15)
        queue_size                  = self.decode_bits_value(cdw10, 16, 31)
        physically_contiguous       = self.decode_bits_value(cdw11, 0, 0)
        queue_priority              = self.decode_bits_value(cdw11, 1, 2)
        completion_queue_identifier = self.decode_bits_value(cdw11, 16, 31)
        nvm_set_identifier          = self.decode_bits_value(cdw12, 0, 15)

        qprio_dict = {
            0:  "Urgent",
            1:  "High",
            2:  "Medium",
            3:  "Low"
        }

        qprio = qprio_dict.get(int(queue_priority), f"[Unknown QPRIO: ({queue_priority})]")

        decoded_text_line = (
            "QID: " + queue_identifier +
            ", QSIZE: " + queue_size + " entries (zero-based value)" +
            ", PC: " + physically_contiguous +
            ", QPRIO: " + qprio +
            ", CQID: " + completion_queue_identifier +
            ", NVMSETID: " + nvm_set_identifier
            )

        return decoded_text_line

    def decode_get_log_page(self, cdw10, cdw11, cdw12, cdw13, cdw14):                       # Admin cmd 02h
        log_page_identifier         = int(self.decode_bits_value(cdw10, 0, 7))
        log_specific_parameter      = self.decode_bits_value(cdw10, 8, 14)
        retain_asynchronous_event   = self.decode_bits_value(cdw10, 15, 15)
        log_specific_identifier     = self.decode_bits_value(cdw11, 16, 31)
        uuid_index                  = self.decode_bits_value(cdw14, 0, 6)
        offset_type                 = self.decode_bits_value(cdw14, 23, 23)
        command_set_identifier      = self.decode_bits_value(cdw14, 24, 31)

        # NUMD must be calculated by combining NUMDU + NUMDL
        # In Python, list slicing is exclusive of the end index
        numdl_bits = cdw10[16:32]
        numdu_bits = cdw11[0:16]
        numd_bits = numdl_bits + numdu_bits
        number_of_dwords = self.decode_bits_value(numd_bits, 0, 31)

        lpol_bits = cdw12[0:32]
        lpou_bits = cdw13[0:32]
        lpo_bits = lpol_bits + lpou_bits
        log_pag_offset = self.decode_bits_value(lpo_bits, 0, 31)

        lid_dict = {
            0:  "Supported Log Pages",                              # LID = 00h
            1:  "Error Information",                                # LID = 01h
            2:  "SMART / Health Information",                       # LID = 02h
            3:  "Firmware Slot Information",                        # LID = 03h
            4:  "Changed Attached Namespace List",                  # LID = 04h
            5:  "Commands Supported and Effects",                   # LID = 05h
            6:  "Device Self-test",                                 # LID = 06h
            7:  "Telemetry Host-Initiated",                         # LID = 07h
            8:  "Telemetry Controller-Initiated",                   # LID = 08h
            9:  "Endurance Group Information",                      # LID = 09h
            10: "Predictable Latency Per NVM Set",                  # LID = 0Ah
            11: "Predictable Latency Event Aggregate",              # LID = 0Bh
            12: "Asymmetric Namespace Access",                      # LID = 0Ch
            13: "Persistent Event Log",                             # LID = 0Dh
            14: "LBA Status Information",                           # LID = 0Eh
            15: "Endurance Group Event Aggregate",                  # LID = 0Fh
            16: "Media Unit Status",                                # LID = 10h
            17: "Supported Capacity Configuration List",            # LID = 11h
            18: "Feature Identifiers Supported and Effects",        # LID = 12h
            19: "NVMe-MI Commands Supported and Effects",           # LID = 13h
            20: "Command and Feature Lockdown",                     # LID = 14h
            21: "Boot Partition",                                   # LID = 15h
            22: "Rotational Media Information",                     # LID = 16h
            23: "Dispersed Namespace Participating NVM Subsystems", # LID = 17h
            24: "Management Address List",                          # LID = 18h
            26: "Reachability Groups",                              # LID = 1Ah
            27: "Reachability Associations",                        # LID = 1Bh
            28: "Changed Allocated Namespace List",                 # LID = 1Ch
            32: "FDP Configurations",                               # LID = 20h
            33: "Reclaim Unit Handle Usage",                        # LID = 21h
            34: "FDP Statistics",                                   # LID = 22h
            35: "FDP Events",                                       # LID = 23h
            112: "Discovery",                                       # LID = 70h
            113: "Host Discovery",                                  # LID = 71h
            114: "AVE Discovery",                                   # LID = 72h
            115: "Pull Model DDC Request",                          # LID = 73h
            128: "Reservation Notification",                        # LID = 80h
            129: "Sanitize Status",                                 # LID = 81h
            191: "Changed Zone List",                               # LID = BFh
        }

        csi = self.decode_csi(command_set_identifier)

        if log_page_identifier in lid_dict:
            lid = lid_dict[log_page_identifier]
        elif 130 <= log_page_identifier <= 190:
            lid = "Reserved for I/O Command Set Specific"
        elif 192 <= log_page_identifier <= 255:
            lid = "Vendor Specific"
        else:
            lid = f"[Unknown LID: ({log_page_identifier})]"

        decoded_text_line = (
            "LID = " + lid +
            ", LSP = " + log_specific_parameter +
            ", RAE = " + retain_asynchronous_event +
            ", NUMD = " + number_of_dwords + " dwords (zero-based)" +
            ", LSI = " + log_specific_identifier +
            ", LPO = " + log_pag_offset + " bytes" +
            ", UUID = " + uuid_index +
            ", OT = " + offset_type +
            ", CSI = " + csi
        )
        return decoded_text_line

    def decode_create_io_completion_queue(self, cdw10, cdw11):                              # Admin cmd 05h
        queue_identifier            = self.decode_bits_value(cdw10, 0, 15)
        queue_size                  = self.decode_bits_value(cdw10, 16, 31)
        physically_contiguous       = self.decode_bits_value(cdw11, 0, 0)
        interrupts_enabled          = self.decode_bits_value(cdw11, 1, 1)
        interrupt_vector            = self.decode_bits_value(cdw11, 16, 31)

        decoded_text_line = (
            "QID: " + queue_identifier +
            ", QSIZE: " + queue_size + " entries (zero-based value)" +
            ", PC: " + physically_contiguous +
            ", IEN: " + interrupts_enabled +
            ", IV: " + interrupt_vector
            )

        return decoded_text_line

    def decode_identify(self, cdw10, cdw11, cdw14):                                         # Admin cmd 06h
        controller_or_namespace_structure   = int(self.decode_bits_value(cdw10, 0, 7))
        contoller_identifier                = self.decode_bits_value(cdw10, 16, 31)
        cns_specific_identifier             = self.decode_bits_value(cdw11, 0, 15)
        command_set_identifier              = self.decode_bits_value(cdw11, 24, 31)
        uuid_index                          = self.decode_bits_value(cdw14, 0, 6)

        cns_dict = {
            0: "Identify Namespace",
            1: "Identify Controller",
            2: "Active Namespace ID list",
            3: "Namespace Identification Descriptor list",
            4: "NVM Set List",
            5: "I/O Command Set specific Identify Namespace",
            6: "I/O Command Set specific Identify Controller",
            7: "Active Namespace ID list (I/O Command Set)",
            8: "I/O Command Set Independent Identify Namespace",
            9: "Identify Namespace (Format Index)",
            10: "Identify Namespace (Format Index) I/O Cmd Set from CSI field",
            16: "Allocated Namespace ID list",
            17: "Identify Namespace (allocated NSID)",
            18: "Controller list for NSID",
            19: "Controller list in subsystem",
            20: "Primary Controller Capabilities",
            21: "Secondary Controller list",
            22: "Namespace Granularity List",
            23: "UUID List",
            24: "Domain List",
            25: "Endurance Group List",
            26: "I/O Command Set specific Allocated Namespace",
            27: "I/O Command Set specific Identify Namespace",
            28: "I/O Command Set data structure",
            29: "Underlying Namespace List",
            30: "Ports List",
            31: "I/O Command Set Independent Identify Namespace (allocated NSID)",
            32: "Supported Controller State Formats"
        }

        csi = self.decode_csi(command_set_identifier)

        if controller_or_namespace_structure in cns_dict:
            cns_id = cns_dict[controller_or_namespace_structure]
        elif 33 <= controller_or_namespace_structure <= 255:
            cns_id = "Vendor Specific"
        else:
            cns_id = f"[Unknown CNS: ({controller_or_namespace_structure})]"

        decoded_text_line = (
            "CNS = " + cns_id +
            ", CNTID = " + contoller_identifier +
            ", CNSSID = " + cns_specific_identifier +
            ", CSI = " + csi +
            ", UUID = " + uuid_index
        )
        return decoded_text_line

    def decode_abort(self, cdw10):                                                          # Admin cmd 08h
        submission_queue_identifier = self.decode_bits_value(cdw10, 0, 15)
        command_identifier          = self.decode_bits_value(cdw10, 16, 31)

        decoded_text_line = (
            "SQID: " + submission_queue_identifier +
            ", CID: " + command_identifier
            )

        return decoded_text_line

    def decode_set_features(self, cdw10, cdw14):                                            # Admin cmd 09h
        feature_identifier  = int(self.decode_bits_value(cdw10, 0, 7))
        save                = self.decode_bits_value(cdw10, 31, 31)
        uuid_index          = self.decode_bits_value(cdw14, 0, 6)

        fid = self.decode_fid(feature_identifier)

        decoded_text_line = (
            "FID = " + fid +
            ", SAVE = " + save +
            ", UUID = " + uuid_index +
            ", (dw11, dw12, dw13 & dw15 are Feature Specific)"
        )
        return decoded_text_line

    def decode_get_features(self, cdw10, cdw14):                                            # Admin cmd 0Ah
        feature_identifier  = int(self.decode_bits_value(cdw10, 0, 7))
        select              = self.decode_bits_value(cdw10, 8, 10)
        uuid_index          = self.decode_bits_value(cdw14, 0, 6)

        fid = self.decode_fid(feature_identifier)

        sel_dict = {
            0:  "Current",
            1:  "Default",
            2:  "Saved",
            3:  "Supported Capabilities",
            # 04-07: Reserved
        }

        sel = sel_dict.get(int(select), f"[Unknown SEL: ({select})]")

        decoded_text_line = (
            ", FID = " + fid +
            ", SEL = " + sel +
            ", UUID = " + uuid_index +
            ", (dw11 is Feature Specific)"
        )
        return decoded_text_line

    def decode_asynchronous_event_request(self):                                                # Admin cmd 0Ch

        decoded_text_line = ("AER - All command specific fields are reserved.")

        return decoded_text_line

    def decode_namespace_management(self, cdw10, cdw11):                                        # Admin cmd 0Dh
        select                  = self.decode_bits_value(cdw10, 0, 3)
        command_set_identifier  = self.decode_bits_value(cdw11, 24, 31)

        sel_dict = {
            0:  "Create",
            1:  "Delete",
            # 02-15: Reserved
        }

        sel = sel_dict.get(int(select), f"[Unknown SEL: ({select})]")
        csi = self.decode_csi(command_set_identifier)

        decoded_text_line = (
            ", SEL = " + sel +
            ", CSI = " + csi
        )
        return decoded_text_line

    def decode_firmware_commit(self, cdw10):                                                    # Admin cmd 10h
        firmware_slot       = self.decode_bits_value(cdw10, 0, 2)
        commit_action       = self.decode_bits_value(cdw10, 3, 5)
        boot_partition_id   = self.decode_bits_value(cdw10, 31, 31)

        ca_dict = {
            0: "Downloaded image replaces the existing image, if any, in the specified Firmware Slot. The newly placed image is not activated.",
            1: "Downloaded image replaces the existing image, if any, in the specified Firmware Slot. The newly placed image is activated at the next Controller Level Reset.",
            2: "The existing image in the specified Firmware Slot is activated at the next Controller Level Reset.",
            3: "Downloaded image replaces the existing image, if any, in the specified Firmware Slot and is then activated immediately.",
            # 04-05: Reserved
            6: "Downloaded image replaces the Boot Partition specified by the Boot Partition ID field.",
            7: "Mark the Boot Partition specified in the BPID field as active and update BPINFO.ABPID"
        }

        ca = ca_dict.get(int(commit_action), f"[Unknown CA: ({commit_action})]")                # 'Unknown CA' can only occur when setting a Reserved value

        decoded_text_line = (
            ", FS = " + firmware_slot +
            ", CA = " + ca +
            ", BPID = " + boot_partition_id
        )
        return decoded_text_line

    def decode_firmware_download(self, cdw10, cdw11):                                           # Admin cmd 11h
        numd       = self.decode_bits_value(cdw10, 0, 31)
        offset     = self.decode_bits_value(cdw11, 0, 31)

        decoded_text_line = (
            ", NUMD = " + numd +
            ", OFFSET = " + offset
        )
        return decoded_text_line

    def decode_device_self_test(self, cdw10):                                                   # Admin cmd 14h
        self_test_code = self.decode_bits_value(cdw10, 0, 3)

        stc_dict = {
            # 0:  Reserved,
            1:  "Short DST operation",
            2:  "Extended DST operation",
            # 03-13:  Reserved,
            14:  "Vendor Specific operation",
            15:  "Abort DST",
        }

        stc = stc_dict.get(int(self_test_code), f"[Unknown STC: ({self_test_code})]")

        decoded_text_line = (
            ", STC = " + stc
        )

        return decoded_text_line

    def decode_namespace_attachment(self, cdw10):                                               # Admin cmd 15h
        select = int(self.decode_bits_value(cdw10, 0, 3))

        sel_dict = {
            0:  "Controller Attach",
            1:  "Controller Detach",
            # 02-15:  Reserved
        }

        sel = sel_dict.get(select, f"[Unknown SEL: ({select})]")

        decoded_text_line = (
            ", SEL = " + sel
        )

        return decoded_text_line

    def decode_directive_send_or_receive(self, cdw10, cdw11, cdw12, cdw13):                     # Admin cmd 19h & 1Ah
        number_of_dwords    = self.decode_bits_value(cdw10, 0, 31)
        directive_operation = self.decode_bits_value(cdw11, 0, 7)
        directive_type      = int(self.decode_bits_value(cdw11, 8, 15))
        directive_specific  = self.decode_bits_value(cdw11, 16, 31)
        # Command Dword 12 and Command Dword 13 may be used based on the Directive Type field and the Directive Operation field

        dtype_dict = {
            0:  "Identify",
            1:  "Streams",
            2:  "Data Placement",
            # 3-14:  Reserved
            15: "Vendor Specific"
        }

        dtype = dtype_dict.get(directive_type, f"[Unknown DTYPE: ({directive_type})]")

        decoded_text_line = (
            ", NUMD = " + number_of_dwords +
            ", DOPER = " + directive_operation +
            ", DTYPE = " + dtype +
            ", DSPEC = " + directive_specific
        )

        return decoded_text_line

    def decode_virtualization_management(self, cdw10, cdw11):                                   # Admin cmd 1Ch
        action                          = self.decode_bits_value(cdw10, 0, 3)
        resource_type                   = self.decode_bits_value(cdw10, 8, 10)
        controller_identifier           = self.decode_bits_value(cdw10, 16, 31)
        number_of_controller_resources  = self.decode_bits_value(cdw11, 0, 15)

        act_dict = {
            # 0:  Reserved,
            1:  "Primary Controller Flexible Allocation",
            # 2-6: Reserved
            7:  "Secondary Controller Offline",
            8:  "Secondary Controller Assign",
            9:  "Secondary Controller Online",
            # 10-15:  Reserved,
        }

        rt_dict = {
            0:  "VQ Resources",
            1:  "VI Resources",
            # 2-7: Reserved
        }

        act = act_dict.get(int(action), f"[Unknown ACT: ({action})]")
        rt = rt_dict.get(int(resource_type), f"[Unknown RT: ({resource_type})]")

        decoded_text_line = (
            ", ACT = " + act +
            ", RT = " + rt +
            ", CNTLID = " + controller_identifier +
            ", NR = " + number_of_controller_resources
        )

        return decoded_text_line

    def decode_format_nvm(self, cdw10):                                                         # Admin cmd 80h
        metadata_settings                   = self.decode_bits_value(cdw10, 4, 4)
        protection_information              = self.decode_bits_value(cdw10, 5, 7)
        protection_information_location     = self.decode_bits_value(cdw10, 8, 8)
        secure_erase_settings               = self.decode_bits_value(cdw10, 9, 11)

        ses_dict = {
            0:  "No Secure Erase",
            1:  "User Data Erase",
            2:  "Cryptographic Erase",
            # 03-07:  Reserved
        }

        lbafl_bits = cdw10[0:4]
        lbafu_bits = cdw10[12:14]
        lbaf_bits = lbafl_bits + lbafu_bits
        lba_format = self.decode_bits_value(lbaf_bits, 0, 5)

        ses = ses_dict.get(int(secure_erase_settings), f"[Unknown SES: ({secure_erase_settings})]")

        decoded_text_line = (
            ", LBAF = " + lba_format +
            ", MSET = " + metadata_settings +
            ", PI = " + protection_information +
            ", PIL = " + protection_information_location +
            ", SES = " + ses
        )

        return decoded_text_line

    def decode_sanitize(self, cdw10, cdw11):                                                    # Admin cmd 84h
        sanitize_action                         = self.decode_bits_value(cdw10, 0, 2)
        allow_unrestricted_sanitize_exit        = self.decode_bits_value(cdw10, 3, 3)
        overwrite_pass_count                    = self.decode_bits_value(cdw10, 4, 7)
        overwrite_invert_pattern_between_passes = self.decode_bits_value(cdw10, 8, 8)
        no_deallocate_after_sanitize            = self.decode_bits_value(cdw10, 9, 9)
        enter_media_verification_state          = self.decode_bits_value(cdw10, 10, 10)
        overwrite_pattern                       = self.decode_bits_value(cdw11, 0, 31)

        sanact_dict = {
            # 0:  "Reserved",
            1:  "Exit Failure Mode",
            2:  "Start a Block Erase sanitize operation",
            3:  "Start an Overwrite sanitize operation",
            4:  "Start a Crypto Erase sanitize operation",
            5:  "Exit Media Verification State",
            # 06-15:  Reserved
        }

        sanact = sanact_dict.get(int(sanitize_action), f"[Unknown SANACT: ({sanitize_action})]")

        decoded_text_line = (
            ", SANACT = " + sanact +
            ", AUSE = " + allow_unrestricted_sanitize_exit +
            ", OWPASS = " + overwrite_pass_count +
            ", OIPBP = " + overwrite_invert_pattern_between_passes +
            ", NDAS = " + no_deallocate_after_sanitize +
            ", EMVS = " + enter_media_verification_state +
            ", OVRPAT = " + overwrite_pattern
        )

        return decoded_text_line

    def get_sct_sc_dict(self):
        """Return the embedded SCT/SC mapping (cached after first build)."""
        # Cache the mapping so we don't rebuild this large dict on every call
        cached = getattr(self, "_SCT_SC_DICT_CACHE", None)
        if cached:
            return cached

        _SCT_SC_DICT = {
            '0h': {
                '00h': 'Successful Completion',
                '01h': 'Invalid Command Opcode',
                '02h': 'Invalid Field in Command',
                '03h': 'Command ID Conflict',
                '04h': 'Data Transfer Error',
                '05h': 'Aborted due to Power Loss Notification',
                '06h': 'Internal Error',
                '07h': 'Command Abort Requested',
                '08h': 'Command Aborted due to SQ Deletion',
                '09h': 'Command Aborted due to Failed Fused Command',
                '0Ah': 'Command Aborted due to Missing Fused Command',
                '0Bh': 'Invalid Namespace or Format',
                '0Ch': 'Command Sequence Error',
                '0Dh': 'Invalid SGL Segment Descriptor',
                '0Eh': 'Invalid Number of SGL Descriptors',
                '0Fh': 'Data SGL Length Invalid',
                '10h': 'Metadata SGL Length Invalid',
                '11h': 'SGL Descriptor Type Invalid',
                '12h': 'Invalid Use of Controller Memory Buffer',
                '13h': 'PRP Offset Invalid',
                '14h': 'Atomic Write Unit Exceeded',
                '15h': 'Operation Denied',
                '16h': 'SGL Offset Invalid',
                '17h': 'Status Code is Reserved',
                '18h': 'Host Identifier Inconsistent Format',
                '19h': 'Keep Alive Timer Expired',
                '1Ah': 'Keep Alive Timeout Invalid',
                '1Bh': 'Command Aborted due to Preempt and Abort',
                '1Ch': 'Sanitize Failed',
                '1Dh': 'Sanitize In Progress',
                '1Eh': 'SGL Data Block Granularity Invalid',
                '1Fh': 'Command Not Supported for Queue in CMB',
                '20h': 'Namespace is Write Protected',
                '21h': 'Command Interrupted',
                '22h': 'Transient Transport Error',
                '23h': 'Command Prohibited by Command and Feature Lockdown',
                '24h': 'Admin Command Media Not Ready',
                '25h': 'Invalid Key Tag',
                '26h': 'Host Dispersed Namespace Support Not Enabled',
                '27h': 'Host Identifier Not Initialized',
                '28h': 'Incorrect Key',
                '29h': 'FDP Disabled',
                '2Ah': 'Invalid Placement Handle List',
                '80h': 'LBA Out of Range',
                '81h': 'Capacity Exceeded',
                '82h': 'Namespace Not Ready',
                '83h': 'Reservation Conflict',
                '84h': 'Format In Progress',
                '85h': 'Invalid Value Size',
                '86h': 'Invalid Key Size',
                '87h': 'KV Key Does Not Exist',
                '88h': 'Unrecovered Error',
                '89h': 'Key Exists'},
            '1h': {'00h': 'Completion Queue Invalid',
                '01h': 'Invalid Queue Identifier',
                '02h': 'Invalid Queue Size',
                '03h': 'Abort Command Limit Exceeded',
                '05h': 'Asynchronous Event Request Limit Exceeded',
                '06h': 'Invalid Firmware Slot',
                '07h': 'Invalid Firmware Image',
                '08h': 'Invalid Interrupt Vector',
                '09h': 'Invalid Log Page',
                '0Ah': 'Invalid Format',
                '0Bh': 'Firmware Activation Requires Conventional Reset',
                '0Ch': 'Invalid Queue Deletion',
                '0Dh': 'Feature Identifier Not Saveable',
                '0Eh': 'Feature Not Changeable',
                '0Fh': 'Feature Not Namespace Specific',
                '10h': 'Firmware Activation Requires NVM Subsystem Reset',
                '11h': 'Firmware Activation Requires Controller Level Reset',
                '12h': 'Firmware Activation Requires Maximum Time Violation',
                '13h': 'Firmware Activation Prohibited',
                '14h': 'Overlapping Range',
                '15h': 'Namespace Insufficient Capacity',
                '16h': 'Namespace Identifier Unavailable',
                '18h': 'Namespace Already Attached',
                '19h': 'Namespace Is Private',
                '1Ah': 'Namespace Not Attached',
                '1Bh': 'Thin Provisioning Not Supported',
                '1Ch': 'Controller List Invalid',
                '1Dh': 'Device Self-test In Progress',
                '1Eh': 'Boot Partition Write Prohibited',
                '1Fh': 'Invalid Controller Identifier',
                '20h': 'Invalid Secondary Controller State',
                '21h': 'Invalid Number of Controller Resources',
                '22h': 'Invalid Resource Identifier',
                '23h': 'Sanitize Prohibited While Persistent Memory Region is Enabled',
                '24h': 'ANA Group Identifier Invalid',
                '25h': 'ANA Attach Failed',
                '26h': 'Insufficient Capacity',
                '27h': 'Namespace Attachment Limit Exceeded',
                '28h': 'Prohibition of Command Execution Not Supported',
                '29h': 'I/O Command Set Not Supported',
                '2Ah': 'I/O Command Set Not Enabled',
                '2Bh': 'I/O Command Set Combination Rejected',
                '2Ch': 'Invalid I/O Command Set',
                '2Dh': 'Identifier Unavailable',
                '2Eh': 'Namespace Is Dispersed',
                '2Fh': 'Invalid Discovery Information',
                '30h': 'Zoning Data Structure Locked',
                '31h': 'Zoning Data Structure Not Found',
                '32h': 'Insufficient Discovery Resources',
                '33h': 'Requested Function Disabled',
                '34h': 'ZoneGroup Originator Invalid',
                '35h': 'Invalid Host',
                '36h': 'Invalid NVM Subsystem',
                '37h': 'Invalid Controller Data Queue',
                '38h': 'Not Enough Resources',
                '39h': 'Controller Suspended',
                '3Ah': 'Controller Not Suspended',
                '3Bh': 'Controller Data Queue Full',
                '80h': 'Conflicting Attributes',
                '81h': 'Invalid Protection Information',
                '82h': 'Attempted Write to Read Only Range',
                '83h': 'Command Size Limit Exceeded',
                '84h': 'Invalid Command ID',
                '85h': 'Incompatible Namespace or Format',
                '86h': 'Fast Copy Not Possible',
                '87h': 'Overlapping I/O Range',
                '88h': 'Namespace Not Reachable',
                '89h': 'Insufficient Resources',
                '8Ah': 'Insufficient Program Resources',
                '8Bh': 'Invalid Memory Namespace',
                '8Ch': 'Invalid Memory Range Set',
                '8Dh': 'Invalid Memory Range Set Identifier',
                '8Eh': 'Invalid Program Data',
                '8Fh': 'Invalid Program Index',
                '90h': 'Invalid Program Type',
                '91h': 'Maximum Memory Ranges Exceeded',
                '92h': 'Maximum Memory Range Sets Exceeded',
                '93h': 'Maximum Programs Activated',
                '94h': 'Maximum Program Bytes Exceeded',
                '95h': 'Memory Range Set In Use',
                '96h': 'No Program',
                '97h': 'Overlapping Memory Ranges',
                '98h': 'Program Not Activated',
                '99h': 'Program In Use',
                '9Ah': 'Program Index Not Downloadable',
                '9Bh': 'Program Too Big',
                '9Ch': 'Successful Media Verification Read',
                'B8h': 'Zoned Boundary Error',
                'B9h': 'Zone Is Full',
                'BAh': 'Zone Is Read Only',
                'BBh': 'Zone Is Offline',
                'BCh': 'Zone Invalid Write',
                'BDh': 'Too Many Active Zones',
                'BEh': 'Too Many Open Zones',
                'BFh': 'Invalid Zone State Transition'},
            '2h': {'80h': 'Write Fault',
                '81h': 'Unrecovered Read Error',
                '82h': 'End-to-end Guard Check Error',
                '83h': 'End-to-end Application Tag Check Error',
                '84h': 'End-to-end Reference Tag Check Error',
                '85h': 'Compare Failure',
                '86h': 'Access Denied',
                '87h': 'Deallocated or Unwritten Logical Block',
                '88h': 'End-to-End Storage Tag Check Error'},
            '3h': {'00h': 'Internal Path Error',
                '01h': 'Asymmetric Access Persistent Loss',
                '02h': 'Asymmetric Access Inaccessible',
                '03h': 'Asymmetric Access Transition',
                '60h': 'Controller Pathing Error',
                '70h': 'Host Pathing Error',
                '71h': 'Command Aborted By Host'}}

        self._SCT_SC_DICT_CACHE = _SCT_SC_DICT
        return _SCT_SC_DICT

if __name__ == "__main__":
    # Prefer secondary monitor
    monitor = None
    try:
        monitors = get_monitors()
        for m in monitors:
            if not getattr(m, "is_primary", False):
                monitor = m
                break
        # Fallback to primary
        if monitor is None and monitors:
            monitor = monitors[0]
    except Exception:
        monitor = None

    root = tk.Tk()

    if monitor is not None:
        root.geometry(f"{monitor.width}x{monitor.height}+{monitor.x}+{monitor.y}")      # start the program always in Maximized mode
        root.state("zoomed")
    else:
        # Fallback: let Tk decide, or use screen width/height
        w = root.winfo_screenwidth()
        h = root.winfo_screenheight()
        root.geometry(f"{w}x{h}+0+0")
        root.state("zoomed")

    app = TextSearchApp(root)
    root.mainloop()
