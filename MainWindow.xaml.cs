using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Media;
using System.Net.Http;
using System.Text.Json;
using System.Runtime.InteropServices;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Interop;
using System.Windows.Media;
using System.Windows.Media.Animation;
using System.Windows.Media.Effects;
using System.Windows.Media.Imaging;
using System.Windows.Threading;
using Windows.Media.Control;
using Windows.Storage.Streams;

namespace Dynamic_Island_Win
{
    public partial class MainWindow : Window
    {
        private DispatcherTimer _tickTimer;
        private DispatcherTimer _musicPauseDelayTimer;
        private DispatcherTimer _collapseDelayTimer;
        private DispatcherTimer _hoverDelayTimer;
        private GlobalSystemMediaTransportControlsSessionManager _mediaSessionManager;
        private GlobalSystemMediaTransportControlsSession _currentSession;

        private bool _isShowingMusic;
        private bool _isPlaying;
        private bool _isExpanded;
        private bool _isSettingsOpen;
        private FrameworkElement _currentPanel;
        private FrameworkElement[] _allPanels;
        private string _lastTrackKey;

        private enum ExpandedTab { Widgets, Tray }
        private ExpandedTab _expandedTab = ExpandedTab.Widgets;

        private enum AppTheme { Light, Dark, DarkBlue, Purple, Green, Red }
        private AppTheme _currentTheme = AppTheme.Dark;

        private enum IslandMode { Floating, Sticky }
        private IslandMode _currentMode = IslandMode.Floating;

        private int _musicRefreshCounter;
        private const int MusicRefreshEveryNTicks = 2;

        private const int HoverDelayMs = 400;
        private const int CollapseDelayMs = 140;

        private static readonly Thickness FloatingMargin = new Thickness(0, 18, 0, 18);
        private static readonly Thickness StickyMargin = new Thickness(0, 0, 0, 18);

        private static readonly CornerRadius FloatingRadius = new CornerRadius(19);
        private static readonly CornerRadius StickyRadius = new CornerRadius(0, 0, 19, 19);

        private const double CompactWidth = 260;
        private const double CompactHeight = 38;
        private const double ExpandedWidgetsWidth = 440;
        private const double ExpandedWidgetsHeight = 312;
        private const double ExpandedSettingsWidth = 480;
        private const double ExpandedSettingsHeight = 340;

        private const double WindowFixedWidth = 560;
        private const double WindowFixedHeight = 400;

        private const string PlayIconData = "M8,5 19,12 8,19 Z";
        private const string PauseIconData = "M6,5 H9 V19 H6 Z M14,5 H17 V19 H14 Z";

        private const int GWL_EXSTYLE = -20;
        private const int WS_EX_TOOLWINDOW = 0x00000080;
        private const int WS_EX_APPWINDOW = 0x00040000;

        [DllImport("user32.dll")]
        private static extern int GetWindowLong(IntPtr hwnd, int index);

        [DllImport("user32.dll")]
        private static extern int SetWindowLong(IntPtr hwnd, int index, int newStyle);

        // ══════════════ GLOBAL MOUSE HOOK ══════════════
        private const int WH_MOUSE_LL = 14;
        private const int WM_LBUTTONDOWN = 0x0201;
        private const int WM_RBUTTONDOWN = 0x0204;

        private delegate IntPtr LowLevelMouseProc(int nCode, IntPtr wParam, IntPtr lParam);

        [DllImport("user32.dll", CharSet = CharSet.Auto, SetLastError = true)]
        private static extern IntPtr SetWindowsHookEx(int idHook, LowLevelMouseProc lpfn, IntPtr hMod, uint dwThreadId);

        [DllImport("user32.dll", CharSet = CharSet.Auto, SetLastError = true)]
        [return: MarshalAs(UnmanagedType.Bool)]
        private static extern bool UnhookWindowsHookEx(IntPtr hhk);

        [DllImport("user32.dll", CharSet = CharSet.Auto, SetLastError = true)]
        private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

        [DllImport("kernel32.dll", CharSet = CharSet.Auto, SetLastError = true)]
        private static extern IntPtr GetModuleHandle(string lpModuleName);

        [StructLayout(LayoutKind.Sequential)]
        private struct POINT { public int X; public int Y; }

        [StructLayout(LayoutKind.Sequential)]
        private struct MSLLHOOKSTRUCT
        {
            public POINT pt;
            public uint mouseData;
            public uint flags;
            public uint time;
            public IntPtr dwExtraInfo;
        }

        private IntPtr _mouseHookId = IntPtr.Zero;
        private LowLevelMouseProc _mouseHookProc;

        // ══════════════ GLOBAL HOTKEY ══════════════
        private const int WM_HOTKEY = 0x0312;
        private const int HOTKEY_ID = 0xD1A1;
        private const uint MOD_ALT = 0x0001;
        private const uint MOD_CONTROL = 0x0002;
        private const uint MOD_SHIFT = 0x0004;
        private const uint MOD_WIN = 0x0008;

        [DllImport("user32.dll")]
        private static extern bool RegisterHotKey(IntPtr hWnd, int id, uint fsModifiers, uint vk);

        [DllImport("user32.dll")]
        private static extern bool UnregisterHotKey(IntPtr hWnd, int id);

        private HwndSource _hwndSource;
        private uint _hotkeyModifiers = MOD_CONTROL | MOD_SHIFT;
        private uint _hotkeyVirtualKey = 0x48; // 'H'
        private bool _isHidden;
        private bool _isCapturingHotkey;

        // ══════════════ ÇOKLU MONİTÖR ══════════════
        [StructLayout(LayoutKind.Sequential)]
        private struct RECT { public int Left, Top, Right, Bottom; }

        [StructLayout(LayoutKind.Sequential)]
        private struct MONITORINFO
        {
            public int cbSize;
            public RECT rcMonitor;
            public RECT rcWork;
            public uint dwFlags;
        }

        private delegate bool MonitorEnumProc(IntPtr hMonitor, IntPtr hdc, ref RECT lprcMonitor, IntPtr dwData);

        [DllImport("user32.dll")]
        private static extern bool EnumDisplayMonitors(IntPtr hdc, IntPtr lprcClip, MonitorEnumProc lpfnEnum, IntPtr dwData);

        [DllImport("user32.dll")]
        private static extern bool GetMonitorInfo(IntPtr hMonitor, ref MONITORINFO lpmi);

        private class MonitorInfo
        {
            public int WorkLeft, WorkTop, WorkRight, WorkBottom;
            public bool IsPrimary;
        }

        private List<MonitorInfo> _monitors = new List<MonitorInfo>();
        private int _currentMonitorIndex = 0;

        // ══════════════ ZAMANLAYICI / WIDGET DURUMU ══════════════
        private TimeSpan _timerDuration = TimeSpan.FromMinutes(5);
        private DateTime _timerEndTime;
        private bool _timerRunning;
        private bool? _timerUiRunning;

        private static readonly CultureInfo TrCulture = new CultureInfo("tr-TR");

        private enum AlarmKind { Timer, PomodoroBreak, PomodoroWork }
        private readonly Dictionary<AlarmKind, SoundPlayer> _alarmPlayers = new Dictionary<AlarmKind, SoundPlayer>();
        private readonly object _alarmLock = new object();

        private const string StopIconData = "M7,7 H17 V17 H7 Z";

        private readonly string[] _slotPaths = new string[4];
        private readonly List<string> _trayItems = new List<string>();
        private bool _suspendOutsideClose;
        private bool _musicIdleShown;

        private string _weatherCity = "";
        private double? _wLat, _wLon;
        private string _wName;
        private DispatcherTimer _weatherTimer;
        private bool _weatherBusy;
        private static readonly HttpClient Http = CreateHttp();

        // Widget düzeni: 4 hücre (sol üst, sağ üst, sol alt, sağ alt). "" = boş
        private static readonly string[] WidgetIds = { "timer", "slots", "music", "weather" };
        private static readonly string[] WidgetNames = { "Zamanlayıcı", "Uygulamalar", "Müzik", "Hava Durumu" };
        private string[] _cells = { "timer", "slots", "music", "weather" };

        // Dosya / uygulama ikonları
        private readonly Dictionary<string, ImageSource> _iconCache =
            new Dictionary<string, ImageSource>(StringComparer.OrdinalIgnoreCase);

        [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
        private struct SHFILEINFO
        {
            public IntPtr hIcon;
            public int iIcon;
            public uint dwAttributes;
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 260)] public string szDisplayName;
            [MarshalAs(UnmanagedType.ByValTStr, SizeConst = 80)] public string szTypeName;
        }

        [DllImport("shell32.dll", CharSet = CharSet.Unicode)]
        private static extern IntPtr SHGetFileInfo(string pszPath, uint dwFileAttributes, ref SHFILEINFO psfi, uint cbFileInfo, uint uFlags);

        [DllImport("user32.dll")]
        private static extern bool DestroyIcon(IntPtr hIcon);

        private const uint SHGFI_ICON = 0x100;
        private const uint SHGFI_LARGEICON = 0x0;

        public MainWindow()
        {
            InitializeComponent();

            _tickTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(250) };
            _tickTimer.Tick += TickTimer_Tick;
            _tickTimer.Start();

            _musicPauseDelayTimer = new DispatcherTimer { Interval = TimeSpan.FromSeconds(1) };
            _musicPauseDelayTimer.Tick += MusicPauseDelayTimer_Tick;

            _collapseDelayTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(CollapseDelayMs) };
            _collapseDelayTimer.Tick += CollapseDelayTimer_Tick;

            _hoverDelayTimer = new DispatcherTimer { Interval = TimeSpan.FromMilliseconds(HoverDelayMs) };
            _hoverDelayTimer.Tick += HoverDelayTimer_Tick;

            UpdateClock();
        }

        protected override void OnSourceInitialized(EventArgs e)
        {
            base.OnSourceInitialized(e);

            var helper = new WindowInteropHelper(this);
            _hwndSource = HwndSource.FromHwnd(helper.Handle);
            _hwndSource?.AddHook(WndProc);
        }

        private async void Window_Loaded(object sender, RoutedEventArgs e)
        {
            _allPanels = new FrameworkElement[]
            {
                CompactClockPanel,
                CompactMusicPanel,
                ExpandedPanel
            };

            _currentPanel = CompactClockPanel;
            ApplyTheme(_currentTheme);
            ApplyMode();
            ApplyExpandedTabVisuals(false);
            UpdateExpandedContent(false);

            _monitors = EnumerateMonitors();
            BuildMonitorButtons();
            PickPrimaryMonitorAsDefault();

            PositionWindowTopCenter();
            HideFromAltTab();
            AnimateIslandIn();

            InstallMouseHook();
            RegisterGlobalHotkey();
            UpdateHotkeyDisplay();

            LoadSettings();
            BuildSlotsUI();
            RebuildTray();
            ApplyLayout();
            if (WeatherCityInput != null) WeatherCityInput.Text = _weatherCity;
            PrepareAlarmSounds();
            UpdateClock();
            StartWeather();

            try
            {
                _mediaSessionManager = await GlobalSystemMediaTransportControlsSessionManager.RequestAsync();
            }
            catch
            {
                _mediaSessionManager = null;
            }
        }

        protected override void OnClosed(EventArgs e)
        {
            UninstallMouseHook();
            UnregisterGlobalHotkey();
            StopHotkeyCapture();
            _hwndSource?.RemoveHook(WndProc);
            _tickTimer?.Stop();
            base.OnClosed(e);
        }

        // ===================== WNDPROC =====================

        private IntPtr WndProc(IntPtr hwnd, int msg, IntPtr wParam, IntPtr lParam, ref bool handled)
        {
            if (msg == WM_HOTKEY && wParam.ToInt32() == HOTKEY_ID)
            {
                ToggleHideShow();
                handled = true;
            }
            return IntPtr.Zero;
        }

        private void ToggleHideShow()
        {
            _isHidden = !_isHidden;
            if (_isHidden)
            {
                _isSettingsOpen = false;
                _isExpanded = false;
                ApplyExpandedTabVisuals(false);
                UpdateExpandedContent(false);
                UpdateVisualState();

                Visibility = Visibility.Hidden;
            }
            else
            {
                Visibility = Visibility.Visible;
                Activate();
            }
        }

        // ===================== HOTKEY KAYIT =====================

        private void RegisterGlobalHotkey()
        {
            if (_hwndSource == null) return;
            UnregisterGlobalHotkey();
            try
            {
                RegisterHotKey(_hwndSource.Handle, HOTKEY_ID, _hotkeyModifiers, _hotkeyVirtualKey);
            }
            catch { }
        }

        private void UnregisterGlobalHotkey()
        {
            if (_hwndSource == null) return;
            try { UnregisterHotKey(_hwndSource.Handle, HOTKEY_ID); } catch { }
        }

        private string GetHotkeyDisplay()
        {
            var parts = new List<string>();
            if ((_hotkeyModifiers & MOD_CONTROL) != 0) parts.Add("Ctrl");
            if ((_hotkeyModifiers & MOD_SHIFT) != 0) parts.Add("Shift");
            if ((_hotkeyModifiers & MOD_ALT) != 0) parts.Add("Alt");
            if ((_hotkeyModifiers & MOD_WIN) != 0) parts.Add("Win");

            var key = KeyInterop.KeyFromVirtualKey((int)_hotkeyVirtualKey);
            parts.Add(FormatKeyName(key));
            return string.Join(" + ", parts);
        }

        private static string FormatKeyName(Key key)
        {
            switch (key)
            {
                case Key.OemPlus: return "=";
                case Key.OemMinus: return "-";
                case Key.OemComma: return ",";
                case Key.OemPeriod: return ".";
                case Key.OemQuestion: return "/";
                case Key.OemSemicolon: return ";";
                case Key.OemQuotes: return "'";
                case Key.OemOpenBrackets: return "[";
                case Key.OemCloseBrackets: return "]";
                case Key.OemPipe: return "\\";
                case Key.OemTilde: return "`";
                case Key.Space: return "Space";
                case Key.Return: return "Enter";
                case Key.Back: return "Backspace";
                case Key.Delete: return "Delete";
                case Key.Insert: return "Insert";
                case Key.Home: return "Home";
                case Key.End: return "End";
                case Key.PageUp: return "PageUp";
                case Key.PageDown: return "PageDown";
                case Key.Up: return "↑";
                case Key.Down: return "↓";
                case Key.Left: return "←";
                case Key.Right: return "→";
                default: return key.ToString();
            }
        }

        private void UpdateHotkeyDisplay()
        {
            if (HotkeyText == null) return;
            HotkeyText.Text = GetHotkeyDisplay();
            HotkeyText.SetResourceReference(TextBlock.ForegroundProperty, "PrimaryTextBrush");
        }

        private void HotkeyField_MouseLeftButtonDown(object sender, MouseButtonEventArgs e)
        {
            e.Handled = true;
            StartHotkeyCapture();
        }

        private void StartHotkeyCapture()
        {
            if (_isCapturingHotkey) return;
            _isCapturingHotkey = true;

            if (HotkeyText != null)
            {
                HotkeyText.Text = "Tuşa bas… (Esc = iptal)";
                HotkeyText.SetResourceReference(TextBlock.ForegroundProperty, "AccentBrush");
            }

            PreviewKeyDown -= Window_HotkeyCapture_PreviewKeyDown;
            PreviewKeyDown += Window_HotkeyCapture_PreviewKeyDown;
            Deactivated -= Window_HotkeyCapture_Deactivated;
            Deactivated += Window_HotkeyCapture_Deactivated;
        }

        private void StopHotkeyCapture()
        {
            if (!_isCapturingHotkey) return;
            _isCapturingHotkey = false;

            PreviewKeyDown -= Window_HotkeyCapture_PreviewKeyDown;
            Deactivated -= Window_HotkeyCapture_Deactivated;

            UpdateHotkeyDisplay();
        }

        private void Window_HotkeyCapture_Deactivated(object sender, EventArgs e)
        {
            StopHotkeyCapture();
        }

        private void Window_HotkeyCapture_PreviewKeyDown(object sender, KeyEventArgs e)
        {
            if (!_isCapturingHotkey) return;

            e.Handled = true;

            var key = e.Key == Key.System ? e.SystemKey : e.Key;

            if (key == Key.Escape)
            {
                StopHotkeyCapture();
                return;
            }

            bool modifierOnly =
                key == Key.LeftCtrl || key == Key.RightCtrl ||
                key == Key.LeftShift || key == Key.RightShift ||
                key == Key.LeftAlt || key == Key.RightAlt ||
                key == Key.LWin || key == Key.RWin ||
                key == Key.None;

            if (modifierOnly)
            {
                var preview = new List<string>();
                if (Keyboard.Modifiers.HasFlag(ModifierKeys.Control)) preview.Add("Ctrl");
                if (Keyboard.Modifiers.HasFlag(ModifierKeys.Shift)) preview.Add("Shift");
                if (Keyboard.Modifiers.HasFlag(ModifierKeys.Alt)) preview.Add("Alt");
                if (Keyboard.Modifiers.HasFlag(ModifierKeys.Windows)) preview.Add("Win");

                string text = preview.Count > 0
                    ? string.Join(" + ", preview) + " + …"
                    : "Tuşa bas… (Esc = iptal)";

                if (HotkeyText != null)
                {
                    HotkeyText.Text = text;
                    HotkeyText.SetResourceReference(TextBlock.ForegroundProperty, "AccentBrush");
                }
                return;
            }

            uint mods = 0;
            if (Keyboard.Modifiers.HasFlag(ModifierKeys.Control)) mods |= MOD_CONTROL;
            if (Keyboard.Modifiers.HasFlag(ModifierKeys.Shift)) mods |= MOD_SHIFT;
            if (Keyboard.Modifiers.HasFlag(ModifierKeys.Alt)) mods |= MOD_ALT;
            if (Keyboard.Modifiers.HasFlag(ModifierKeys.Windows)) mods |= MOD_WIN;

            bool isFunctionKey = key >= Key.F1 && key <= Key.F24;

            if (mods == 0 && !isFunctionKey)
            {
                if (HotkeyText != null)
                {
                    HotkeyText.Text = "En az bir modifier gerekli (Ctrl/Shift/Alt)";
                    HotkeyText.SetResourceReference(TextBlock.ForegroundProperty, "AccentBrush");
                }
                return;
            }

            uint vk = (uint)KeyInterop.VirtualKeyFromKey(key);
            if (vk == 0) return;

            _hotkeyModifiers = mods;
            _hotkeyVirtualKey = vk;

            RegisterGlobalHotkey();
            StopHotkeyCapture();
        }

        // ===================== MONİTÖR =====================

        private List<MonitorInfo> EnumerateMonitors()
        {
            var list = new List<MonitorInfo>();
            try
            {
                MonitorEnumProc callback = (IntPtr hMon, IntPtr hdc, ref RECT rect, IntPtr data) =>
                {
                    var mi = new MONITORINFO { cbSize = Marshal.SizeOf<MONITORINFO>() };
                    if (GetMonitorInfo(hMon, ref mi))
                    {
                        list.Add(new MonitorInfo
                        {
                            WorkLeft = mi.rcWork.Left,
                            WorkTop = mi.rcWork.Top,
                            WorkRight = mi.rcWork.Right,
                            WorkBottom = mi.rcWork.Bottom,
                            IsPrimary = (mi.dwFlags & 1) != 0,
                        });
                    }
                    return true;
                };
                EnumDisplayMonitors(IntPtr.Zero, IntPtr.Zero, callback, IntPtr.Zero);
            }
            catch { }
            if (list.Count == 0)
            {
                list.Add(new MonitorInfo
                {
                    WorkLeft = 0,
                    WorkTop = 0,
                    WorkRight = (int)SystemParameters.PrimaryScreenWidth,
                    WorkBottom = (int)SystemParameters.PrimaryScreenHeight,
                    IsPrimary = true,
                });
            }
            return list;
        }

        private void PickPrimaryMonitorAsDefault()
        {
            for (int i = 0; i < _monitors.Count; i++)
            {
                if (_monitors[i].IsPrimary) { _currentMonitorIndex = i; break; }
            }
            UpdateMonitorSelectionVisuals();
        }

        private void BuildMonitorButtons()
        {
            if (MonitorButtonsPanel == null) return;
            MonitorButtonsPanel.Children.Clear();

            for (int i = 0; i < _monitors.Count; i++)
            {
                var btn = new Button
                {
                    Content = "Ekran " + (i + 1),
                    Style = (Style)FindResource("OptBtn"),
                    Tag = i,
                    Margin = new Thickness(i == 0 ? 0 : 5, 0, 0, 0),
                };
                btn.Click += MonitorButton_Click;
                MonitorButtonsPanel.Children.Add(btn);
            }
            UpdateMonitorSelectionVisuals();
        }

        private void MonitorButton_Click(object sender, RoutedEventArgs e)
        {
            var btn = sender as Button;
            if (btn == null) return;
            int idx = (int)btn.Tag;
            if (idx < 0 || idx >= _monitors.Count) return;
            _currentMonitorIndex = idx;
            UpdateMonitorSelectionVisuals();
            PositionWindowOnMonitor(_currentMonitorIndex, true);
        }

        private void UpdateMonitorSelectionVisuals()
        {
            if (MonitorButtonsPanel == null) return;
            var accent = (Brush)FindResource("AccentBrush");
            foreach (var child in MonitorButtonsPanel.Children)
            {
                var b = child as Button;
                if (b == null) continue;
                int idx = (int)b.Tag;
                b.BorderBrush = (idx == _currentMonitorIndex) ? accent : Brushes.Transparent;
            }
        }

        private void PositionWindowOnMonitor(int index, bool animate)
        {
            if (_monitors.Count == 0) { PositionWindowTopCenter(); return; }
            if (index < 0) index = 0;
            if (index >= _monitors.Count) index = _monitors.Count - 1;

            var mon = _monitors[index];
            double workWidth = mon.WorkRight - mon.WorkLeft;

            Width = WindowFixedWidth;
            Height = WindowFixedHeight;

            double newLeft = mon.WorkLeft + (workWidth - WindowFixedWidth) / 2.0;
            double newTop = mon.WorkTop;

            if (!animate || !IsLoaded)
            {
                Left = newLeft;
                Top = newTop;
                return;
            }

            var ease = new CubicEase { EasingMode = EasingMode.EaseInOut };
            var dur = TimeSpan.FromMilliseconds(340);

            var fromLeft = double.IsNaN(Left) ? newLeft : Left;
            var fromTop = double.IsNaN(Top) ? newTop : Top;

            var la = new DoubleAnimation(fromLeft, newLeft, dur) { EasingFunction = ease };
            var ta = new DoubleAnimation(fromTop, newTop, dur) { EasingFunction = ease };

            la.Completed += (s, e) => { BeginAnimation(LeftProperty, null); Left = newLeft; };
            ta.Completed += (s, e) => { BeginAnimation(TopProperty, null); Top = newTop; };

            BeginAnimation(LeftProperty, la);
            BeginAnimation(TopProperty, ta);
        }

        // ===================== GLOBAL MOUSE HOOK =====================

        private void InstallMouseHook()
        {
            _mouseHookProc = MouseHookCallback;
            using (var curProcess = Process.GetCurrentProcess())
            using (var curModule = curProcess.MainModule)
            {
                _mouseHookId = SetWindowsHookEx(
                    WH_MOUSE_LL,
                    _mouseHookProc,
                    GetModuleHandle(curModule.ModuleName),
                    0);
            }
        }

        private void UninstallMouseHook()
        {
            if (_mouseHookId != IntPtr.Zero)
            {
                UnhookWindowsHookEx(_mouseHookId);
                _mouseHookId = IntPtr.Zero;
            }
        }

        private IntPtr MouseHookCallback(int nCode, IntPtr wParam, IntPtr lParam)
        {
            if (nCode >= 0 && (_isSettingsOpen || _isExpanded))
            {
                int msg = wParam.ToInt32();
                if (msg == WM_LBUTTONDOWN || msg == WM_RBUTTONDOWN)
                {
                    var hs = Marshal.PtrToStructure<MSLLHOOKSTRUCT>(lParam);
                    int x = hs.pt.X;
                    int y = hs.pt.Y;

                    Dispatcher.BeginInvoke(
                        new Action(() => CheckClickOutside(x, y)),
                        DispatcherPriority.Normal);
                }
            }

            return CallNextHookEx(_mouseHookId, nCode, wParam, lParam);
        }

        private void CheckClickOutside(int screenX, int screenY)
        {
            if (!_isSettingsOpen && !_isExpanded) return;
            if (_suspendOutsideClose) return;
            if (!IsLoaded) return;
            if (IslandContainer.ActualWidth <= 0 || IslandContainer.ActualHeight <= 0) return;

            try
            {
                var topLeft = IslandContainer.PointToScreen(new Point(0, 0));
                var bottomRight = IslandContainer.PointToScreen(
                    new Point(IslandContainer.ActualWidth, IslandContainer.ActualHeight));

                bool inside =
                    screenX >= topLeft.X && screenX <= bottomRight.X &&
                    screenY >= topLeft.Y && screenY <= bottomRight.Y;

                if (inside) return;

                _collapseDelayTimer.Stop();
                _hoverDelayTimer.Stop();

                if (_isCapturingHotkey) StopHotkeyCapture();

                // Metin kutusundaki odağı bırak (aksi halde kapanmayı engeller)
                Keyboard.ClearFocus();

                _isSettingsOpen = false;
                _isExpanded = false;

                ApplyExpandedTabVisuals(false);
                UpdateExpandedContent(false);
                UpdateVisualState();
            }
            catch { }
        }

        private void PositionWindowTopCenter()
        {
            if (_monitors.Count > 0)
            {
                PositionWindowOnMonitor(_currentMonitorIndex, false);
                return;
            }

            Width = WindowFixedWidth;
            Height = WindowFixedHeight;
            Left = (SystemParameters.PrimaryScreenWidth - WindowFixedWidth) / 2;
            Top = 0;
        }

        private void HideFromAltTab()
        {
            var hwnd = new WindowInteropHelper(this).Handle;
            int exStyle = GetWindowLong(hwnd, GWL_EXSTYLE);
            exStyle |= WS_EX_TOOLWINDOW;
            exStyle &= ~WS_EX_APPWINDOW;
            SetWindowLong(hwnd, GWL_EXSTYLE, exStyle);
        }

        private void AnimateIslandIn()
        {
            var dur = TimeSpan.FromMilliseconds(320);
            var ease = new CubicEase { EasingMode = EasingMode.EaseOut };
            var fade = new DoubleAnimation(0, 1, dur) { EasingFunction = ease };
            IslandContainer.BeginAnimation(OpacityProperty, fade);
        }

        // ===================== HOVER =====================

        private void Island_MouseEnter(object sender, MouseEventArgs e)
        {
            _collapseDelayTimer.Stop();
            if (_isExpanded) return;
            _hoverDelayTimer.Stop();
            _hoverDelayTimer.Start();
        }

        private void Island_MouseLeave(object sender, MouseEventArgs e)
        {
            _hoverDelayTimer.Stop();
            _collapseDelayTimer.Stop();
            _collapseDelayTimer.Start();
        }

        private void HoverDelayTimer_Tick(object sender, EventArgs e)
        {
            _hoverDelayTimer.Stop();
            if (!IslandContainer.IsMouseOver) return;
            if (_isSettingsOpen) return;
            SetExpanded(true);
        }

        private void CollapseDelayTimer_Tick(object sender, EventArgs e)
        {
            _collapseDelayTimer.Stop();
            if (_isSettingsOpen) return;
            if (IslandContainer.IsMouseOver) return;

            // Diyalog açıkken ya da metin kutusunda yazılırken kapatma
            if (_suspendOutsideClose) return;
            if (WeatherCityInput != null && WeatherCityInput.IsKeyboardFocusWithin) return;

            SetExpanded(false);
        }

        private void SetExpanded(bool expanded)
        {
            if (_isExpanded == expanded) return;
            _isExpanded = expanded;

            if (expanded)
            {
                ApplyExpandedTabVisuals(false);
                UpdateExpandedContent(false);
            }

            UpdateVisualState();
        }

        // ===================== SEKMELER + AYARLAR =====================

        private void WidgetsTabButton_Click(object sender, RoutedEventArgs e)
        {
            _isSettingsOpen = false;
            _expandedTab = ExpandedTab.Widgets;
            ApplyExpandedTabVisuals(true);
            UpdateExpandedContent(true);
            UpdateVisualState();
        }

        private void TrayTabButton_Click(object sender, RoutedEventArgs e)
        {
            _isSettingsOpen = false;
            _expandedTab = ExpandedTab.Tray;
            ApplyExpandedTabVisuals(true);
            UpdateExpandedContent(true);
            UpdateVisualState();
        }

        private void SettingsButton_Click(object sender, RoutedEventArgs e)
        {
            _isSettingsOpen = !_isSettingsOpen;
            ApplyExpandedTabVisuals(true);
            UpdateExpandedContent(true);
            UpdateVisualState();
        }

        private void ThemeButton_Click(object sender, RoutedEventArgs e)
        {
            var btn = sender as Button;
            if (btn == null) return;

            var tag = btn.Tag as string;
            AppTheme theme = AppTheme.Dark;
            if (tag == "Light") theme = AppTheme.Light;
            else if (tag == "DarkBlue") theme = AppTheme.DarkBlue;
            else if (tag == "Purple") theme = AppTheme.Purple;
            else if (tag == "Green") theme = AppTheme.Green;
            else if (tag == "Red") theme = AppTheme.Red;

            if (_currentTheme == theme) return;
            ApplyTheme(theme);
        }

        private void ModeButton_Click(object sender, RoutedEventArgs e)
        {
            var btn = sender as Button;
            if (btn == null) return;
            var tag = btn.Tag as string;
            IslandMode mode = tag == "Sticky" ? IslandMode.Sticky : IslandMode.Floating;
            if (_currentMode == mode) return;
            _currentMode = mode;
            ApplyMode(true);
        }

        private void ApplyExpandedTabVisuals(bool animate)
        {
            bool clockActive = !_isSettingsOpen && _expandedTab == ExpandedTab.Widgets;
            bool musicActive = !_isSettingsOpen && _expandedTab == ExpandedTab.Tray;

            var activeBg = (Brush)FindResource("ActiveTabBgBrush");
            var activeFg = (Brush)FindResource("ActiveTabFgBrush");
            var inactiveFg = (Brush)FindResource("InactiveTabFgBrush");

            WidgetsTabButton.Background = clockActive ? activeBg : Brushes.Transparent;
            WidgetsTabButton.Foreground = clockActive ? activeFg : inactiveFg;

            TrayTabButton.Background = musicActive ? activeBg : Brushes.Transparent;
            TrayTabButton.Foreground = musicActive ? activeFg : inactiveFg;

            SettingsButton.Background = _isSettingsOpen ? activeBg : Brushes.Transparent;

            UpdateSettingsNavVisuals();
        }

        // ===================== AYARLAR SAYFALARI =====================

        private int _settingsPage = 0;

        private void SettingsNav_Click(object sender, RoutedEventArgs e)
        {
            var btn = sender as Button;
            int idx;
            if (btn == null || !int.TryParse(btn.Tag as string, out idx)) return;
            SetSettingsPage(idx, true);
        }

        private void SetSettingsPage(int idx, bool animate)
        {
            var pages = new FrameworkElement[] { SettingsPageGeneral, SettingsPageWidgets, SettingsPageTheme };
            if (idx < 0 || idx >= pages.Length) return;

            for (int i = 0; i < pages.Length; i++)
            {
                if (i == idx)
                {
                    bool wasHidden = pages[i].Visibility != Visibility.Visible;
                    pages[i].Visibility = Visibility.Visible;
                    if (animate && wasHidden) SlideFadeIn(pages[i], 0, 12, 220, 20);
                }
                else
                {
                    pages[i].BeginAnimation(OpacityProperty, null);
                    pages[i].Visibility = Visibility.Collapsed;
                }
            }

            _settingsPage = idx;
            UpdateSettingsNavVisuals();
        }

        private void UpdateSettingsNavVisuals()
        {
            if (SettingsNav0Btn == null) return;

            var activeBg = (Brush)FindResource("ActiveTabBgBrush");
            var activeFg = (Brush)FindResource("ActiveTabFgBrush");
            var inactiveFg = (Brush)FindResource("InactiveTabFgBrush");

            var navs = new[] { SettingsNav0Btn, SettingsNav1Btn, SettingsNav2Btn };
            for (int i = 0; i < navs.Length; i++)
            {
                bool active = i == _settingsPage;
                navs[i].Background = active ? activeBg : Brushes.Transparent;
                navs[i].Foreground = active ? activeFg : inactiveFg;
            }
        }

        private int _lastExpandedPanelIndex = 0;

        private void UpdateExpandedContent(bool animate)
        {
            FrameworkElement showPanel;
            int newIndex;
            if (_isSettingsOpen) { showPanel = SettingsPanel; newIndex = 2; }
            else if (_expandedTab == ExpandedTab.Widgets) { showPanel = WidgetsPanel; newIndex = 0; }
            else { showPanel = TrayPanel; newIndex = 1; }

            double fromX = newIndex >= _lastExpandedPanelIndex ? 28 : -28;
            if (newIndex == _lastExpandedPanelIndex) fromX = 0;
            _lastExpandedPanelIndex = newIndex;

            FrameworkElement[] panels = { WidgetsPanel, TrayPanel, SettingsPanel };

            foreach (var p in panels)
            {
                p.BeginAnimation(OpacityProperty, null);

                if (p == showPanel)
                {
                    p.Visibility = Visibility.Visible;
                    if (animate)
                        SlideFadeIn(p, fromX, 0, 260, 40);
                    else
                    {
                        p.RenderTransform = Transform.Identity;
                        p.Opacity = 1;
                    }
                }
                else
                {
                    p.Visibility = Visibility.Collapsed;
                    p.Opacity = 0;
                }
            }
        }

        /// <summary>Öğeyi (fromX, fromY) konumundan yerine kaydırarak ve solma ile gösterir.</summary>
        private static void SlideFadeIn(FrameworkElement el, double fromX, double fromY, int durMs, int delayMs)
        {
            var ease = new CubicEase { EasingMode = EasingMode.EaseOut };
            var tt = new TranslateTransform(fromX, fromY);
            el.RenderTransform = tt;

            var begin = TimeSpan.FromMilliseconds(delayMs);
            var dur = TimeSpan.FromMilliseconds(durMs);

            el.Opacity = 0;
            el.BeginAnimation(OpacityProperty,
                new DoubleAnimation(0, 1, dur) { BeginTime = begin, EasingFunction = ease, FillBehavior = FillBehavior.HoldEnd });

            if (fromX != 0)
            {
                var xa = new DoubleAnimation(fromX, 0, dur) { BeginTime = begin, EasingFunction = ease };
                xa.Completed += (s, e) => { tt.BeginAnimation(TranslateTransform.XProperty, null); tt.X = 0; };
                tt.BeginAnimation(TranslateTransform.XProperty, xa);
            }
            if (fromY != 0)
            {
                var ya = new DoubleAnimation(fromY, 0, dur) { BeginTime = begin, EasingFunction = ease };
                ya.Completed += (s, e) => { tt.BeginAnimation(TranslateTransform.YProperty, null); tt.Y = 0; };
                tt.BeginAnimation(TranslateTransform.YProperty, ya);
            }
        }

        // ===================== TEMA =====================

        private static Color C(byte a, byte r, byte g, byte b) => Color.FromArgb(a, r, g, b);

        private static SolidColorBrush SB(byte a, byte r, byte g, byte b)
        {
            var br = new SolidColorBrush(C(a, r, g, b));
            br.Freeze();
            return br;
        }

        private static LinearGradientBrush GradV(Color c1, Color c2, Color c3, Color c4)
        {
            var g = new LinearGradientBrush { StartPoint = new Point(0.5, 0), EndPoint = new Point(0.5, 1) };
            g.GradientStops.Add(new GradientStop(c1, 0));
            g.GradientStops.Add(new GradientStop(c2, 0.4));
            g.GradientStops.Add(new GradientStop(c3, 0.75));
            g.GradientStops.Add(new GradientStop(c4, 1));
            g.Freeze();
            return g;
        }

        private static LinearGradientBrush GradHairline(Color c1, Color c2, Color c3)
        {
            var g = new LinearGradientBrush { StartPoint = new Point(0.5, 0), EndPoint = new Point(0.5, 1) };
            g.GradientStops.Add(new GradientStop(c1, 0));
            g.GradientStops.Add(new GradientStop(c2, 0.3));
            g.GradientStops.Add(new GradientStop(c3, 1));
            g.Freeze();
            return g;
        }

        private void ApplyTheme(AppTheme theme)
        {
            _currentTheme = theme;

            switch (theme)
            {
                case AppTheme.Light: ApplyLightTheme(); break;
                case AppTheme.DarkBlue: ApplyDarkBlueTheme(); break;
                case AppTheme.Purple: ApplyPurpleTheme(); break;
                case AppTheme.Green: ApplyGreenTheme(); break;
                case AppTheme.Red: ApplyRedTheme(); break;
                default: ApplyDarkTheme(); break;
            }

            Resources["CardBgBrush"] = theme == AppTheme.Light
                ? SB(0x12, 0x00, 0x00, 0x00)
                : SB(0x14, 0xFF, 0xFF, 0xFF);

            Resources["OnAccentBrush"] = theme == AppTheme.Light
                ? SB(0xFF, 0xFF, 0xFF, 0xFF)
                : SB(0xFF, 0x0A, 0x0A, 0x0C);

            UpdateThemeSelectionVisuals();
            UpdateShadowForTheme();
            UpdateNotchEarBrush();

            if (_isExpanded) ApplyExpandedTabVisuals(false);
        }

        private void ApplyDarkTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0x07, 0x07, 0x07), C(0xFF, 0x0C, 0x0C, 0x0E),
                C(0xFF, 0x10, 0x10, 0x12), C(0xFF, 0x07, 0x07, 0x07));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0xF0, 0xF0, 0xF2);
            Resources["SecondaryTextBrush"] = SB(0x8A, 0x8E, 0x8E, 0x93);
            Resources["TertiaryTextBrush"] = SB(0x7A, 0x8E, 0x8E, 0x93);
            Resources["TabBarBgBrush"] = SB(0x0C, 0xFF, 0xFF, 0xFF);
            Resources["TabBarBorderBrush"] = SB(0x14, 0xFF, 0xFF, 0xFF);
            Resources["ActiveTabBgBrush"] = SB(0x24, 0xFF, 0xFF, 0xFF);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0xF5, 0xF5, 0xF7);
            Resources["InactiveTabFgBrush"] = SB(0x7A, 0x8E, 0x8E, 0x93);
            Resources["ProgressTrackBrush"] = SB(0x1A, 0xFF, 0xFF, 0xFF);
            Resources["ArtBorderBrush"] = SB(0x1E, 0xFF, 0xFF, 0xFF);
            Resources["PlayBtnBgBrush"] = SB(0x20, 0xFF, 0xFF, 0xFF);
            Resources["PlayBtnHoverBrush"] = SB(0x38, 0xFF, 0xFF, 0xFF);
            Resources["PlayBtnPressedBrush"] = SB(0x55, 0xFF, 0xFF, 0xFF);
            Resources["IconBtnHoverBrush"] = SB(0x22, 0xFF, 0xFF, 0xFF);
            Resources["IconBtnPressedBrush"] = SB(0x3A, 0xFF, 0xFF, 0xFF);
            Resources["IconGlyphBrush"] = SB(0xFF, 0xF0, 0xF0, 0xF2);
            Resources["AccentBrush"] = SB(0xFF, 0x60, 0xAA, 0xFF);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0x2A, 0x2A, 0x2C), C(0xFF, 0x1C, 0x1C, 0x1E),
                C(0xFF, 0x1C, 0x1C, 0x1E), C(0xFF, 0x2A, 0x2A, 0x2C));
            Resources["HairlineBrush"] = GradHairline(
                C(0x2A, 0xFF, 0xFF, 0xFF), C(0x08, 0xFF, 0xFF, 0xFF), C(0x00, 0xFF, 0xFF, 0xFF));
        }

        private void ApplyLightTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0xFA, 0xFA, 0xFC), C(0xFF, 0xF4, 0xF4, 0xF6),
                C(0xFF, 0xEE, 0xEE, 0xF1), C(0xFF, 0xFA, 0xFA, 0xFC));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0x1A, 0x1A, 0x1C);
            Resources["SecondaryTextBrush"] = SB(0xFF, 0x5A, 0x5A, 0x60);
            Resources["TertiaryTextBrush"] = SB(0xFF, 0x80, 0x80, 0x88);
            Resources["TabBarBgBrush"] = SB(0x0A, 0x00, 0x00, 0x00);
            Resources["TabBarBorderBrush"] = SB(0x18, 0x00, 0x00, 0x00);
            Resources["ActiveTabBgBrush"] = SB(0x1E, 0x00, 0x00, 0x00);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0x1A, 0x1A, 0x1C);
            Resources["InactiveTabFgBrush"] = SB(0x8A, 0x5A, 0x5A, 0x60);
            Resources["ProgressTrackBrush"] = SB(0x14, 0x00, 0x00, 0x00);
            Resources["ArtBorderBrush"] = SB(0x22, 0x00, 0x00, 0x00);
            Resources["PlayBtnBgBrush"] = SB(0x14, 0x00, 0x00, 0x00);
            Resources["PlayBtnHoverBrush"] = SB(0x24, 0x00, 0x00, 0x00);
            Resources["PlayBtnPressedBrush"] = SB(0x38, 0x00, 0x00, 0x00);
            Resources["IconBtnHoverBrush"] = SB(0x15, 0x00, 0x00, 0x00);
            Resources["IconBtnPressedBrush"] = SB(0x25, 0x00, 0x00, 0x00);
            Resources["IconGlyphBrush"] = SB(0xFF, 0x1A, 0x1A, 0x1C);
            Resources["AccentBrush"] = SB(0xFF, 0x00, 0x7A, 0xFF);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0xE8, 0xE8, 0xEC), C(0xFF, 0xD8, 0xD8, 0xDE),
                C(0xFF, 0xD8, 0xD8, 0xDE), C(0xFF, 0xE8, 0xE8, 0xEC));
            Resources["HairlineBrush"] = GradHairline(
                C(0x28, 0x00, 0x00, 0x00), C(0x08, 0x00, 0x00, 0x00), C(0x00, 0x00, 0x00, 0x00));
        }

        private void ApplyDarkBlueTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0x0A, 0x14, 0x28), C(0xFF, 0x0D, 0x18, 0x30),
                C(0xFF, 0x10, 0x1E, 0x3C), C(0xFF, 0x0A, 0x14, 0x28));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0xE8, 0xF0, 0xFF);
            Resources["SecondaryTextBrush"] = SB(0xFF, 0x7A, 0x8E, 0xB0);
            Resources["TertiaryTextBrush"] = SB(0xFF, 0x6A, 0x7E, 0xA0);
            Resources["TabBarBgBrush"] = SB(0x10, 0x2A, 0x4A, 0x80);
            Resources["TabBarBorderBrush"] = SB(0x28, 0x64, 0xA0, 0xFF);
            Resources["ActiveTabBgBrush"] = SB(0x30, 0x3D, 0x7A, 0xF0);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0xE8, 0xF0, 0xFF);
            Resources["InactiveTabFgBrush"] = SB(0x9A, 0x7A, 0x8E, 0xB0);
            Resources["ProgressTrackBrush"] = SB(0x20, 0x64, 0xA0, 0xFF);
            Resources["ArtBorderBrush"] = SB(0x30, 0x5B, 0x8F, 0xD8);
            Resources["PlayBtnBgBrush"] = SB(0x2A, 0x64, 0xA0, 0xFF);
            Resources["PlayBtnHoverBrush"] = SB(0x40, 0x64, 0xA0, 0xFF);
            Resources["PlayBtnPressedBrush"] = SB(0x58, 0x64, 0xA0, 0xFF);
            Resources["IconBtnHoverBrush"] = SB(0x20, 0x64, 0xA0, 0xFF);
            Resources["IconBtnPressedBrush"] = SB(0x35, 0x64, 0xA0, 0xFF);
            Resources["IconGlyphBrush"] = SB(0xFF, 0xE8, 0xF0, 0xFF);
            Resources["AccentBrush"] = SB(0xFF, 0x3D, 0x7A, 0xF0);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0x10, 0x1E, 0x3C), C(0xFF, 0x16, 0x28, 0x4E),
                C(0xFF, 0x16, 0x28, 0x4E), C(0xFF, 0x10, 0x1E, 0x3C));
            Resources["HairlineBrush"] = GradHairline(
                C(0x40, 0x80, 0xB8, 0xFF), C(0x20, 0x64, 0xA0, 0xFF), C(0x00, 0x00, 0x00, 0x00));
        }

        private void ApplyPurpleTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0x14, 0x08, 0x28), C(0xFF, 0x1C, 0x0E, 0x38),
                C(0xFF, 0x24, 0x12, 0x48), C(0xFF, 0x14, 0x08, 0x28));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0xEC, 0xE0, 0xFF);
            Resources["SecondaryTextBrush"] = SB(0xFF, 0x9A, 0x80, 0xC8);
            Resources["TertiaryTextBrush"] = SB(0xFF, 0x80, 0x6A, 0xA8);
            Resources["TabBarBgBrush"] = SB(0x14, 0xA8, 0x55, 0xF7);
            Resources["TabBarBorderBrush"] = SB(0x2A, 0xA8, 0x55, 0xF7);
            Resources["ActiveTabBgBrush"] = SB(0x38, 0xA8, 0x55, 0xF7);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0xEC, 0xE0, 0xFF);
            Resources["InactiveTabFgBrush"] = SB(0x9A, 0x9A, 0x80, 0xC8);
            Resources["ProgressTrackBrush"] = SB(0x20, 0xA8, 0x55, 0xF7);
            Resources["ArtBorderBrush"] = SB(0x30, 0xA8, 0x55, 0xF7);
            Resources["PlayBtnBgBrush"] = SB(0x2C, 0xA8, 0x55, 0xF7);
            Resources["PlayBtnHoverBrush"] = SB(0x44, 0xA8, 0x55, 0xF7);
            Resources["PlayBtnPressedBrush"] = SB(0x5A, 0xA8, 0x55, 0xF7);
            Resources["IconBtnHoverBrush"] = SB(0x24, 0xA8, 0x55, 0xF7);
            Resources["IconBtnPressedBrush"] = SB(0x38, 0xA8, 0x55, 0xF7);
            Resources["IconGlyphBrush"] = SB(0xFF, 0xEC, 0xE0, 0xFF);
            Resources["AccentBrush"] = SB(0xFF, 0xA8, 0x55, 0xF7);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0x24, 0x12, 0x48), C(0xFF, 0x2A, 0x18, 0x56),
                C(0xFF, 0x2A, 0x18, 0x56), C(0xFF, 0x24, 0x12, 0x48));
            Resources["HairlineBrush"] = GradHairline(
                C(0x40, 0xC0, 0x88, 0xFF), C(0x20, 0xA8, 0x55, 0xF7), C(0x00, 0x00, 0x00, 0x00));
        }

        private void ApplyGreenTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0x06, 0x1E, 0x12), C(0xFF, 0x08, 0x2A, 0x18),
                C(0xFF, 0x0C, 0x36, 0x22), C(0xFF, 0x06, 0x1E, 0x12));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0xE0, 0xFF, 0xE8);
            Resources["SecondaryTextBrush"] = SB(0xFF, 0x7A, 0xB8, 0x8E);
            Resources["TertiaryTextBrush"] = SB(0xFF, 0x6A, 0xA0, 0x7E);
            Resources["TabBarBgBrush"] = SB(0x14, 0x10, 0xB9, 0x81);
            Resources["TabBarBorderBrush"] = SB(0x2A, 0x10, 0xB9, 0x81);
            Resources["ActiveTabBgBrush"] = SB(0x38, 0x10, 0xB9, 0x81);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0xE0, 0xFF, 0xE8);
            Resources["InactiveTabFgBrush"] = SB(0x9A, 0x7A, 0xB8, 0x8E);
            Resources["ProgressTrackBrush"] = SB(0x20, 0x10, 0xB9, 0x81);
            Resources["ArtBorderBrush"] = SB(0x30, 0x10, 0xB9, 0x81);
            Resources["PlayBtnBgBrush"] = SB(0x2C, 0x10, 0xB9, 0x81);
            Resources["PlayBtnHoverBrush"] = SB(0x44, 0x10, 0xB9, 0x81);
            Resources["PlayBtnPressedBrush"] = SB(0x5A, 0x10, 0xB9, 0x81);
            Resources["IconBtnHoverBrush"] = SB(0x24, 0x10, 0xB9, 0x81);
            Resources["IconBtnPressedBrush"] = SB(0x38, 0x10, 0xB9, 0x81);
            Resources["IconGlyphBrush"] = SB(0xFF, 0xE0, 0xFF, 0xE8);
            Resources["AccentBrush"] = SB(0xFF, 0x10, 0xB9, 0x81);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0x0C, 0x36, 0x22), C(0xFF, 0x10, 0x42, 0x2A),
                C(0xFF, 0x10, 0x42, 0x2A), C(0xFF, 0x0C, 0x36, 0x22));
            Resources["HairlineBrush"] = GradHairline(
                C(0x40, 0x40, 0xE0, 0xA0), C(0x20, 0x10, 0xB9, 0x81), C(0x00, 0x00, 0x00, 0x00));
        }

        private void ApplyRedTheme()
        {
            Resources["IslandBgBrush"] = GradV(
                C(0xFF, 0x20, 0x08, 0x0A), C(0xFF, 0x2A, 0x0C, 0x10),
                C(0xFF, 0x36, 0x10, 0x18), C(0xFF, 0x20, 0x08, 0x0A));
            Resources["PrimaryTextBrush"] = SB(0xFF, 0xFF, 0xE0, 0xE4);
            Resources["SecondaryTextBrush"] = SB(0xFF, 0xC0, 0x80, 0x88);
            Resources["TertiaryTextBrush"] = SB(0xFF, 0xA8, 0x70, 0x78);
            Resources["TabBarBgBrush"] = SB(0x14, 0xEF, 0x44, 0x44);
            Resources["TabBarBorderBrush"] = SB(0x2A, 0xEF, 0x44, 0x44);
            Resources["ActiveTabBgBrush"] = SB(0x38, 0xEF, 0x44, 0x44);
            Resources["ActiveTabFgBrush"] = SB(0xFF, 0xFF, 0xE0, 0xE4);
            Resources["InactiveTabFgBrush"] = SB(0x9A, 0xC0, 0x80, 0x88);
            Resources["ProgressTrackBrush"] = SB(0x20, 0xEF, 0x44, 0x44);
            Resources["ArtBorderBrush"] = SB(0x30, 0xEF, 0x44, 0x44);
            Resources["PlayBtnBgBrush"] = SB(0x2C, 0xEF, 0x44, 0x44);
            Resources["PlayBtnHoverBrush"] = SB(0x44, 0xEF, 0x44, 0x44);
            Resources["PlayBtnPressedBrush"] = SB(0x5A, 0xEF, 0x44, 0x44);
            Resources["IconBtnHoverBrush"] = SB(0x24, 0xEF, 0x44, 0x44);
            Resources["IconBtnPressedBrush"] = SB(0x38, 0xEF, 0x44, 0x44);
            Resources["IconGlyphBrush"] = SB(0xFF, 0xFF, 0xE0, 0xE4);
            Resources["AccentBrush"] = SB(0xFF, 0xEF, 0x44, 0x44);
            Resources["ArtFallbackBrush"] = GradV(
                C(0xFF, 0x36, 0x10, 0x18), C(0xFF, 0x40, 0x14, 0x1E),
                C(0xFF, 0x40, 0x14, 0x1E), C(0xFF, 0x36, 0x10, 0x18));
            Resources["HairlineBrush"] = GradHairline(
                C(0x40, 0xFF, 0x80, 0x88), C(0x20, 0xEF, 0x44, 0x44), C(0x00, 0x00, 0x00, 0x00));
        }

        private void UpdateThemeSelectionVisuals()
        {
            var accent = (Brush)FindResource("AccentBrush");
            var transparent = Brushes.Transparent;

            ThemeLightBtn.BorderBrush = _currentTheme == AppTheme.Light ? accent : transparent;
            ThemeDarkBtn.BorderBrush = _currentTheme == AppTheme.Dark ? accent : transparent;
            ThemeDarkBlueBtn.BorderBrush = _currentTheme == AppTheme.DarkBlue ? accent : transparent;
            ThemePurpleBtn.BorderBrush = _currentTheme == AppTheme.Purple ? accent : transparent;
            ThemeGreenBtn.BorderBrush = _currentTheme == AppTheme.Green ? accent : transparent;
            ThemeRedBtn.BorderBrush = _currentTheme == AppTheme.Red ? accent : transparent;
        }

        private void UpdateShadowForTheme()
        {
            if (IslandShadowEffect == null) return;

            switch (_currentTheme)
            {
                case AppTheme.Light:
                    IslandShadowEffect.Color = Colors.Black;
                    IslandShadowEffect.Opacity = 0.18;
                    IslandShadowEffect.BlurRadius = 22;
                    break;
                case AppTheme.DarkBlue:
                case AppTheme.Purple:
                case AppTheme.Green:
                case AppTheme.Red:
                    IslandShadowEffect.Color = Colors.Black;
                    IslandShadowEffect.Opacity = 0.85;
                    IslandShadowEffect.BlurRadius = 20;
                    break;
                default:
                    IslandShadowEffect.Color = Colors.Black;
                    IslandShadowEffect.Opacity = 0.75;
                    IslandShadowEffect.BlurRadius = 18;
                    break;
            }
        }

        // ===================== MOD =====================

        private const int ModeTransitionMs = 420;

        public static readonly DependencyProperty ModeProgressProperty =
            DependencyProperty.Register(
                nameof(ModeProgress), typeof(double), typeof(MainWindow),
                new PropertyMetadata(0.0, OnModeProgressChanged));

        public double ModeProgress
        {
            get => (double)GetValue(ModeProgressProperty);
            set => SetValue(ModeProgressProperty, value);
        }

        private static void OnModeProgressChanged(DependencyObject d, DependencyPropertyChangedEventArgs e)
        {
            ((MainWindow)d).ApplyModeProgress((double)e.NewValue);
        }

        private DoubleAnimation _modeAnim;

        private void ApplyMode(bool animate = false)
        {
            double target = _currentMode == IslandMode.Sticky ? 1.0 : 0.0;

            double from = ModeProgress;
            _modeAnim = null;
            BeginAnimation(ModeProgressProperty, null);
            ModeProgress = from;

            if (!animate || !IsLoaded || Math.Abs(from - target) < 0.0001)
            {
                ModeProgress = target;
                ApplyModeProgress(target);
            }
            else
            {
                IEasingFunction ease = target > from
                    ? new CubicEase { EasingMode = EasingMode.EaseInOut }
                    : (IEasingFunction)new BackEase { EasingMode = EasingMode.EaseOut, Amplitude = 0.35 };

                var anim = new DoubleAnimation(from, target, TimeSpan.FromMilliseconds(ModeTransitionMs))
                {
                    EasingFunction = ease,
                    FillBehavior = FillBehavior.HoldEnd
                };
                _modeAnim = anim;

                anim.Completed += (s, e) =>
                {
                    if (_modeAnim != anim) return;
                    _modeAnim = null;
                    BeginAnimation(ModeProgressProperty, null);
                    ModeProgress = target;
                };

                BeginAnimation(ModeProgressProperty, anim);
            }

            UpdateModeSelectionVisuals();
        }

        private void ApplyModeProgress(double t)
        {
            if (IslandContainer == null || ShadowLayer == null || NotchEarLeft == null) return;

            double c = Math.Max(0, Math.Min(1, t));
            double cm = Math.Min(1, t);

            double top = FloatingMargin.Top + (StickyMargin.Top - FloatingMargin.Top) * cm;
            IslandContainer.Margin = new Thickness(0, Math.Max(0, top), 0, FloatingMargin.Bottom);

            double topRadius = FloatingRadius.TopLeft * (1 - c);
            var radius = new CornerRadius(topRadius, topRadius, FloatingRadius.BottomRight, FloatingRadius.BottomLeft);
            ShadowLayer.CornerRadius = radius;
            ContentLayer.CornerRadius = radius;
            HairlineBorder.CornerRadius = radius;

            HairlineBorder.Opacity = 1 - c;

            double ear = Math.Max(0, t);
            NotchEarLeftScale.ScaleX = NotchEarLeftScale.ScaleY = ear;
            NotchEarRightScale.ScaleX = NotchEarRightScale.ScaleY = ear;
            var earVis = ear > 0.001 ? Visibility.Visible : Visibility.Collapsed;
            NotchEarLeft.Visibility = earVis;
            NotchEarRight.Visibility = earVis;
        }

        private void UpdateModeSelectionVisuals()
        {
            var accent = (Brush)FindResource("AccentBrush");
            var transparent = Brushes.Transparent;

            if (ModeFloatingBtn != null)
                ModeFloatingBtn.BorderBrush = _currentMode == IslandMode.Floating ? accent : transparent;

            if (ModeStickyBtn != null)
                ModeStickyBtn.BorderBrush = _currentMode == IslandMode.Sticky ? accent : transparent;
        }

        private void UpdateNotchEarBrush()
        {
            if (NotchEarLeft == null || NotchEarRight == null) return;

            Brush fill = Brushes.Black;
            if (TryFindResource("IslandBgBrush") is LinearGradientBrush g && g.GradientStops.Count > 0)
            {
                var top = g.GradientStops[0].Color;
                var sb = new SolidColorBrush(top);
                sb.Freeze();
                fill = sb;
            }
            else if (TryFindResource("IslandBgBrush") is SolidColorBrush s)
            {
                fill = s;
            }

            NotchEarLeft.Fill = fill;
            NotchEarRight.Fill = fill;
        }

        // ===================== SAAT & ZAMANLAYICI =====================

        private async void TickTimer_Tick(object sender, EventArgs e)
        {
            UpdateClock();
            _musicRefreshCounter++;
            if (_musicRefreshCounter >= MusicRefreshEveryNTicks)
            {
                _musicRefreshCounter = 0;
                await RefreshMusicStateAsync();
            }
        }

        private void UpdateClock()
        {
            var now = DateTime.Now;

            bool finished = false;
            if (_timerRunning && now >= _timerEndTime)
            {
                _timerRunning = false;
                finished = true;
            }

            UpdateTimerWidget(now);
            if (finished) PlayFinishAnimation(AlarmKind.Timer);

            string compactText = now.ToString("HH:mm");
            bool showSpecial = false;

            if (_timerRunning)
            {
                var rem = _timerEndTime - now;
                if (rem < TimeSpan.Zero) rem = TimeSpan.Zero;
                compactText = FormatTimerDisplay(rem);
                showSpecial = true;
            }

            ClockText.Text = compactText;

            if (showSpecial)
                ClockText.SetResourceReference(TextBlock.ForegroundProperty, "AccentBrush");
            else
                ClockText.SetResourceReference(TextBlock.ForegroundProperty, "PrimaryTextBrush");
        }

        private static string FormatTimerDisplay(TimeSpan ts)
        {
            if (ts < TimeSpan.Zero) ts = TimeSpan.Zero;
            int totalSec = (int)Math.Ceiling(ts.TotalSeconds);
            int h = totalSec / 3600, m = (totalSec % 3600) / 60, sec = totalSec % 60;
            return h > 0 ? $"{h}:{m:D2}:{sec:D2}" : $"{m:D2}:{sec:D2}";
        }

        // ─── Bitiş animasyonu (görsel) + SESLİ UYARI ───

        private void PlayFinishAnimation(AlarmKind kind)
        {
            if (IslandContainer == null) return;

            // Sesli uyarı (arka planda, UI'yi bloklamaz)
            PlayAlarmSound(kind);

            var st = IslandContainer.RenderTransform as ScaleTransform;
            if (st == null)
            {
                st = new ScaleTransform(1, 1);
                IslandContainer.RenderTransform = st;
            }
            IslandContainer.RenderTransformOrigin = new Point(0.5, 0.5);

            var ease = new CubicEase { EasingMode = EasingMode.EaseOut };
            var pulse = new DoubleAnimationUsingKeyFrames();
            pulse.KeyFrames.Add(new EasingDoubleKeyFrame(1.0, KeyTime.FromTimeSpan(TimeSpan.Zero)));
            pulse.KeyFrames.Add(new EasingDoubleKeyFrame(1.10, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(140))) { EasingFunction = ease });
            pulse.KeyFrames.Add(new EasingDoubleKeyFrame(0.96, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(280))) { EasingFunction = ease });
            pulse.KeyFrames.Add(new EasingDoubleKeyFrame(1.04, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(420))) { EasingFunction = ease });
            pulse.KeyFrames.Add(new EasingDoubleKeyFrame(1.0, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(560))) { EasingFunction = ease });

            st.BeginAnimation(ScaleTransform.ScaleXProperty, pulse);
            st.BeginAnimation(ScaleTransform.ScaleYProperty, pulse);

            var glow = new DoubleAnimationUsingKeyFrames();
            glow.KeyFrames.Add(new EasingDoubleKeyFrame(0.75, KeyTime.FromTimeSpan(TimeSpan.Zero)));
            glow.KeyFrames.Add(new EasingDoubleKeyFrame(1.0, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(200))) { EasingFunction = ease });
            glow.KeyFrames.Add(new EasingDoubleKeyFrame(0.75, KeyTime.FromTimeSpan(TimeSpan.FromMilliseconds(560))) { EasingFunction = ease });
            if (IslandShadowEffect != null)
                IslandShadowEffect.BeginAnimation(System.Windows.Media.Effects.DropShadowEffect.OpacityProperty, glow);
        }

        // ─── Sesli uyarı: sentezlenmiş çan sesi (harici dosya gerekmez) ───

        private void PrepareAlarmSounds()
        {
            System.Threading.Tasks.Task.Run(() =>
            {
                try
                {
                    foreach (AlarmKind kind in Enum.GetValues(typeof(AlarmKind)))
                        GetAlarmPlayer(kind);
                }
                catch { }
            });
        }

        private SoundPlayer GetAlarmPlayer(AlarmKind kind)
        {
            lock (_alarmLock)
            {
                SoundPlayer player;
                if (_alarmPlayers.TryGetValue(kind, out player)) return player;

                var wav = BuildAlarmWav(kind);
                player = new SoundPlayer(new MemoryStream(wav));
                player.Load();
                _alarmPlayers[kind] = player;
                return player;
            }
        }

        private void PlayAlarmSound(AlarmKind kind)
        {
            System.Threading.Tasks.Task.Run(() =>
            {
                try
                {
                    GetAlarmPlayer(kind).Play();
                }
                catch
                {
                    try { SystemSounds.Exclamation.Play(); } catch { }
                }
            });
        }

        // Nota frekansları (Hz)
        private const double N_C4 = 261.63, N_C5 = 523.25, N_E5 = 659.25, N_G5 = 783.99,
                             N_C6 = 1046.50, N_E6 = 1318.51, N_G6 = 1567.98;

        private static byte[] BuildAlarmWav(AlarmKind kind)
        {
            const int sampleRate = 44100;

            // (frekans, başlangıç sn, genlik)
            var notes = new List<Tuple<double, double, double>>();
            double totalSec;

            switch (kind)
            {
                case AlarmKind.PomodoroBreak:
                    // Çalışma bitti: sakin, alçalan üçlü
                    notes.Add(Tuple.Create(N_G5, 0.00, 0.85));
                    notes.Add(Tuple.Create(N_E5, 0.24, 0.85));
                    notes.Add(Tuple.Create(N_C5, 0.48, 0.95));
                    notes.Add(Tuple.Create(N_C4, 0.48, 0.55));
                    totalSec = 2.6;
                    break;

                case AlarmKind.PomodoroWork:
                    // Mola bitti: canlı, yükselen dörtlü
                    notes.Add(Tuple.Create(N_C5, 0.00, 0.80));
                    notes.Add(Tuple.Create(N_G5, 0.13, 0.85));
                    notes.Add(Tuple.Create(N_C6, 0.26, 0.90));
                    notes.Add(Tuple.Create(N_E6, 0.39, 0.95));
                    notes.Add(Tuple.Create(N_G6, 0.39, 0.45));
                    totalSec = 2.4;
                    break;

                default:
                    // Zamanlayıcı: iki tur yükselen arpej, dikkat çekici ama tatlı
                    for (int round = 0; round < 2; round++)
                    {
                        double t0 = round * 1.15;
                        notes.Add(Tuple.Create(N_E5, t0 + 0.00, 0.80));
                        notes.Add(Tuple.Create(N_G5, t0 + 0.14, 0.85));
                        notes.Add(Tuple.Create(N_C6, t0 + 0.28, 0.90));
                        notes.Add(Tuple.Create(N_E6, t0 + 0.42, 1.00));
                    }
                    totalSec = 3.3;
                    break;
            }

            int n = (int)(totalSec * sampleRate);
            var buf = new double[n];

            foreach (var note in notes)
            {
                double f = note.Item1;
                int s0 = (int)(note.Item2 * sampleRate);
                int len = Math.Min(n - s0, (int)(1.8 * sampleRate));

                for (int i = 0; i < len; i++)
                {
                    double t = i / (double)sampleRate;
                    double env = (1.0 - Math.Exp(-t / 0.003)) * Math.Exp(-t / 0.55);
                    double ph = 2.0 * Math.PI * f * t;

                    // Çan benzeri tını: temel + harmonikler + hafif uyumsuz parça
                    double v = Math.Sin(ph)
                             + 0.30 * Math.Sin(2.0 * ph) * Math.Exp(-t / 0.30)
                             + 0.12 * Math.Sin(3.0 * ph) * Math.Exp(-t / 0.15)
                             + 0.06 * Math.Sin(4.2 * ph) * Math.Exp(-t / 0.08);

                    buf[s0 + i] += v * env * note.Item3;
                }
            }

            // Hafif yankı (geri beslemeli gecikme) ile ses derinliği
            int delay = (int)(0.19 * sampleRate);
            for (int i = delay; i < n; i++)
                buf[i] += buf[i - delay] * 0.28;

            double peak = 0;
            for (int i = 0; i < n; i++) peak = Math.Max(peak, Math.Abs(buf[i]));
            double scale = peak > 0 ? 0.85 / peak : 1.0;

            int fade = (int)(0.06 * sampleRate);
            var pcm = new short[n];
            for (int i = 0; i < n; i++)
            {
                double v = buf[i] * scale;
                if (i > n - fade) v *= (n - i) / (double)fade;
                pcm[i] = (short)Math.Round(Math.Max(-1.0, Math.Min(1.0, v)) * 32767);
            }

            using (var ms = new MemoryStream())
            using (var bw = new BinaryWriter(ms))
            {
                int dataLen = n * 2;
                bw.Write(new[] { 'R', 'I', 'F', 'F' });
                bw.Write(36 + dataLen);
                bw.Write(new[] { 'W', 'A', 'V', 'E' });
                bw.Write(new[] { 'f', 'm', 't', ' ' });
                bw.Write(16);
                bw.Write((short)1);
                bw.Write((short)1);
                bw.Write(sampleRate);
                bw.Write(sampleRate * 2);
                bw.Write((short)2);
                bw.Write((short)16);
                bw.Write(new[] { 'd', 'a', 't', 'a' });
                bw.Write(dataLen);
                for (int i = 0; i < n; i++) bw.Write(pcm[i]);
                bw.Flush();
                return ms.ToArray();
            }
        }

        // ===================== ZAMANLAYICI WIDGET'I =====================

        private static int Wrap(int v, int mod) { return ((v % mod) + mod) % mod; }

        private void TimerAdjust_Click(object sender, RoutedEventArgs e)
        {
            if (_timerRunning) return;
            var btn = sender as Button;
            var tag = btn == null ? null : btn.Tag as string;
            if (string.IsNullOrEmpty(tag) || tag.Length < 2) return;

            int sign = tag[1] == '+' ? 1 : -1;
            int h = (int)_timerDuration.TotalHours, m = _timerDuration.Minutes, sec = _timerDuration.Seconds;

            switch (tag[0])
            {
                case 'H': h = Wrap(h + sign, 24); break;
                case 'M': m = Wrap(m + sign, 60); break;
                case 'S': sec = Wrap(sec + 5 * sign, 60); break;
            }

            _timerDuration = new TimeSpan(h, m, sec);
            UpdateTimerWidget(DateTime.Now);
        }

        private void TimerPlayStopBtn_Click(object sender, RoutedEventArgs e)
        {
            if (_timerRunning)
            {
                _timerRunning = false;
            }
            else
            {
                if (_timerDuration <= TimeSpan.Zero) return;
                _timerEndTime = DateTime.Now + _timerDuration;
                _timerRunning = true;
            }
            UpdateTimerWidget(DateTime.Now);
        }

        private void UpdateTimerWidget(DateTime now)
        {
            if (TimerHText == null) return;

            TimeSpan shown = _timerRunning ? _timerEndTime - now : _timerDuration;
            if (shown < TimeSpan.Zero) shown = TimeSpan.Zero;
            int totalSec = _timerRunning ? (int)Math.Ceiling(shown.TotalSeconds) : (int)shown.TotalSeconds;

            TimerHText.Text = (totalSec / 3600).ToString("00");
            TimerMText.Text = ((totalSec % 3600) / 60).ToString("00");
            TimerSText.Text = (totalSec % 60).ToString("00");

            if (_timerUiRunning == _timerRunning) return;
            _timerUiRunning = _timerRunning;

            var vis = _timerRunning ? Visibility.Hidden : Visibility.Visible;
            foreach (var b in new[] { TimerHUp, TimerHDown, TimerMUp, TimerMDown, TimerSUp, TimerSDown })
                b.Visibility = vis;

            string brushKey = _timerRunning ? "AccentBrush" : "PrimaryTextBrush";
            foreach (var t in new[] { TimerHText, TimerMText, TimerSText })
                t.SetResourceReference(TextBlock.ForegroundProperty, brushKey);

            TimerPlayStopIcon.Data = Geometry.Parse(_timerRunning ? StopIconData : PlayIconData);
        }

        // ===================== AYARLARI KAYDET / YÜKLE =====================

        private static string SettingsFilePath
        {
            get
            {
                return System.IO.Path.Combine(
                    Environment.GetFolderPath(Environment.SpecialFolder.ApplicationData),
                    "DynamicIslandWin", "settings.txt");
            }
        }

        private void LoadSettings()
        {
            try
            {
                if (!File.Exists(SettingsFilePath)) return;
                foreach (var line in File.ReadAllLines(SettingsFilePath))
                {
                    int eq = line.IndexOf('=');
                    if (eq <= 0) continue;
                    string key = line.Substring(0, eq).Trim();
                    string val = line.Substring(eq + 1).Trim();

                    if (key == "city") _weatherCity = val;
                    else if (key == "layout")
                    {
                        var parts = val.Split(',');
                        if (parts.Length == 4)
                        {
                            var tmp = new string[4];
                            bool ok = true;
                            for (int i = 0; i < 4; i++)
                            {
                                string p = parts[i].Trim();
                                if (p == "-" || p == "") tmp[i] = "";
                                else if (Array.IndexOf(WidgetIds, p) >= 0 && Array.IndexOf(tmp, p) < 0) tmp[i] = p;
                                else ok = false;
                            }
                            if (ok) _cells = tmp;
                        }
                    }
                    else if (key.StartsWith("slot") && key.Length == 5)
                    {
                        int i = key[4] - '0';
                        if (i >= 0 && i < _slotPaths.Length && val.Length > 0) _slotPaths[i] = val;
                    }
                }
            }
            catch { }
        }

        private void SaveSettings()
        {
            try
            {
                Directory.CreateDirectory(System.IO.Path.GetDirectoryName(SettingsFilePath));
                var lines = new List<string> { "city=" + _weatherCity };
                var cellParts = new string[4];
                for (int i = 0; i < 4; i++) cellParts[i] = string.IsNullOrEmpty(_cells[i]) ? "-" : _cells[i];
                lines.Add("layout=" + string.Join(",", cellParts));
                for (int i = 0; i < _slotPaths.Length; i++)
                    lines.Add("slot" + i + "=" + (_slotPaths[i] ?? ""));
                File.WriteAllLines(SettingsFilePath, lines);
            }
            catch { }
        }

        // ===================== KISAYOL YUVALARI =====================

        private Button[] SlotButtons { get { return new[] { Slot0Btn, Slot1Btn, Slot2Btn, Slot3Btn }; } }

        private void BuildSlotsUI()
        {
            var btns = SlotButtons;
            for (int i = 0; i < btns.Length; i++) SetSlotVisual(btns[i], _slotPaths[i]);
        }

        private void SetSlotVisual(Button btn, string path)
        {
            if (string.IsNullOrEmpty(path))
            {
                btn.Tag = null;
                var plus = new System.Windows.Shapes.Path
                {
                    Data = Geometry.Parse("M12,5 V19 M5,12 H19"),
                    StrokeThickness = 2,
                    StrokeStartLineCap = PenLineCap.Round,
                    StrokeEndLineCap = PenLineCap.Round,
                    Width = 12,
                    Height = 12,
                    Stretch = Stretch.Uniform,
                    Opacity = 0.45
                };
                plus.SetResourceReference(System.Windows.Shapes.Shape.StrokeProperty, "SecondaryTextBrush");
                btn.Content = plus;
                btn.ToolTip = "Uygulama veya dosya ekle (tıkla ya da sürükle-bırak)";
                return;
            }

            btn.Tag = path;

            var sp = new StackPanel { HorizontalAlignment = HorizontalAlignment.Center, VerticalAlignment = VerticalAlignment.Center };

            var icon = GetFileIcon(path);
            if (icon != null)
            {
                var img = new Image { Source = icon, Width = 26, Height = 26, HorizontalAlignment = HorizontalAlignment.Center };
                RenderOptions.SetBitmapScalingMode(img, BitmapScalingMode.HighQuality);
                sp.Children.Add(img);
            }

            var tb = new TextBlock
            {
                Text = System.IO.Path.GetFileNameWithoutExtension(path),
                FontFamily = new FontFamily("Segoe UI"),
                FontSize = icon != null ? 10 : 11,
                FontWeight = FontWeights.SemiBold,
                TextTrimming = TextTrimming.CharacterEllipsis,
                MaxWidth = 78,
                Margin = new Thickness(0, icon != null ? 2 : 0, 0, 0),
                HorizontalAlignment = HorizontalAlignment.Center
            };
            tb.SetResourceReference(TextBlock.ForegroundProperty, "PrimaryTextBrush");
            sp.Children.Add(tb);

            btn.Content = sp;
            btn.ToolTip = path + "\nSağ tık: kaldır";
        }

        /// <summary>Dosya/uygulamanın Windows ikonunu döndürür (önbellekli).</summary>
        private ImageSource GetFileIcon(string path)
        {
            if (string.IsNullOrEmpty(path)) return null;

            ImageSource cached;
            if (_iconCache.TryGetValue(path, out cached)) return cached;

            ImageSource result = null;
            try
            {
                var info = new SHFILEINFO();
                IntPtr ok = SHGetFileInfo(path, 0, ref info, (uint)Marshal.SizeOf(typeof(SHFILEINFO)), SHGFI_ICON | SHGFI_LARGEICON);
                if (ok != IntPtr.Zero && info.hIcon != IntPtr.Zero)
                {
                    var bs = Imaging.CreateBitmapSourceFromHIcon(info.hIcon, Int32Rect.Empty, BitmapSizeOptions.FromEmptyOptions());
                    bs.Freeze();
                    result = bs;
                    DestroyIcon(info.hIcon);
                }
            }
            catch { }

            _iconCache[path] = result;
            return result;
        }

        private void Slot_DragOver(object sender, DragEventArgs e)
        {
            e.Effects = e.Data.GetDataPresent(DataFormats.FileDrop) ? DragDropEffects.Link : DragDropEffects.None;
            e.Handled = true;
        }

        private void SlotBtn_Drop(object sender, DragEventArgs e)
        {
            e.Handled = true;
            var btn = sender as Button;
            int idx = Array.IndexOf(SlotButtons, btn);
            var files = e.Data.GetData(DataFormats.FileDrop) as string[];
            if (idx < 0 || files == null || files.Length == 0) return;

            _slotPaths[idx] = files[0];
            SetSlotVisual(btn, files[0]);
            SaveSettings();
        }

        private void SlotBtn_Click(object sender, RoutedEventArgs e)
        {
            var btn = sender as Button;
            int idx = Array.IndexOf(SlotButtons, btn);
            if (idx < 0) return;

            if (string.IsNullOrEmpty(_slotPaths[idx])) PickSlotApp(idx);
            else LaunchPath(_slotPaths[idx]);
        }

        private void SlotBtn_RightClick(object sender, MouseButtonEventArgs e)
        {
            var btn = sender as Button;
            int idx = Array.IndexOf(SlotButtons, btn);
            if (idx < 0 || string.IsNullOrEmpty(_slotPaths[idx])) return;

            _slotPaths[idx] = null;
            SetSlotVisual(btn, null);
            SaveSettings();
            e.Handled = true;
        }

        private void PickSlotApp(int idx)
        {
            _suspendOutsideClose = true;
            try
            {
                var dlg = new Microsoft.Win32.OpenFileDialog
                {
                    Title = "Yuvaya eklenecek uygulama veya dosyayı seç",
                    Filter = "Uygulamalar ve kısayollar (*.exe;*.lnk)|*.exe;*.lnk|Tüm dosyalar (*.*)|*.*"
                };
                if (dlg.ShowDialog(this) == true)
                {
                    _slotPaths[idx] = dlg.FileName;
                    SetSlotVisual(SlotButtons[idx], dlg.FileName);
                    SaveSettings();
                }
            }
            catch { }
            finally { _suspendOutsideClose = false; }
        }

        private void LaunchPath(string path)
        {
            try
            {
                Process.Start(new ProcessStartInfo(path) { UseShellExecute = true });
            }
            catch { }
        }

        // ===================== TRAY (DOSYA RAFI) =====================

        private void Island_DragEnter(object sender, DragEventArgs e)
        {
            if (!e.Data.GetDataPresent(DataFormats.FileDrop)) return;

            _collapseDelayTimer.Stop();
            if (_isExpanded) return;
            _hoverDelayTimer.Stop();
            _isSettingsOpen = false;
            _expandedTab = ExpandedTab.Tray;

            if (!_isExpanded)
            {
                SetExpanded(true);
            }
            else
            {
                ApplyExpandedTabVisuals(true);
                UpdateExpandedContent(true);
                UpdateVisualState();
            }
        }

        private void Tray_DragEnter(object sender, DragEventArgs e)
        {
            e.Effects = e.Data.GetDataPresent(DataFormats.FileDrop) ? DragDropEffects.Copy : DragDropEffects.None;
            TrayDropZone.SetResourceReference(Border.BorderBrushProperty, "AccentBrush");
            e.Handled = true;
        }

        private void Tray_DragLeave(object sender, DragEventArgs e)
        {
            TrayDropZone.SetResourceReference(Border.BorderBrushProperty, "TabBarBorderBrush");
        }

        private void Tray_Drop(object sender, DragEventArgs e)
        {
            TrayDropZone.SetResourceReference(Border.BorderBrushProperty, "TabBarBorderBrush");
            e.Handled = true;

            var files = e.Data.GetData(DataFormats.FileDrop) as string[];
            if (files == null) return;

            foreach (var f in files)
                if (!_trayItems.Contains(f)) _trayItems.Add(f);

            RebuildTray();
        }

        private void RebuildTray()
        {
            if (TrayItemsPanel == null) return;

            TrayItemsPanel.Children.Clear();
            TrayEmptyHint.Visibility = _trayItems.Count == 0 ? Visibility.Visible : Visibility.Collapsed;

            foreach (var path in _trayItems.ToArray())
            {
                string p = path;

                var chip = new Border
                {
                    CornerRadius = new CornerRadius(10),
                    Padding = new Thickness(8, 6, 6, 6),
                    Margin = new Thickness(0, 0, 6, 6),
                    Cursor = Cursors.Hand,
                    ToolTip = p + "\nBaşka bir klasöre sürükleyerek taşı / kopyala"
                };
                chip.SetResourceReference(Border.BackgroundProperty, "ActiveTabBgBrush");

                var sp = new StackPanel { Orientation = Orientation.Horizontal };

                var icon = GetFileIcon(p);
                if (icon != null)
                {
                    var img = new Image { Source = icon, Width = 18, Height = 18, Margin = new Thickness(0, 0, 7, 0), IsHitTestVisible = false };
                    RenderOptions.SetBitmapScalingMode(img, BitmapScalingMode.HighQuality);
                    sp.Children.Add(img);
                }

                string fileName = System.IO.Path.GetFileName(p);
                var name = new TextBlock
                {
                    Text = fileName.Length > 0 ? fileName : p,
                    FontFamily = new FontFamily("Segoe UI"),
                    FontSize = 11.5,
                    MaxWidth = 120,
                    TextTrimming = TextTrimming.CharacterEllipsis,
                    VerticalAlignment = VerticalAlignment.Center,
                    IsHitTestVisible = false
                };
                name.SetResourceReference(TextBlock.ForegroundProperty, "PrimaryTextBrush");

                var close = new TextBlock
                {
                    Text = "×",
                    FontFamily = new FontFamily("Segoe UI"),
                    FontSize = 14,
                    Margin = new Thickness(8, -2, 0, 0),
                    Padding = new Thickness(3, 0, 3, 0),
                    Cursor = Cursors.Hand,
                    VerticalAlignment = VerticalAlignment.Center
                };
                close.SetResourceReference(TextBlock.ForegroundProperty, "SecondaryTextBrush");
                close.MouseLeftButtonDown += (s, e) => { e.Handled = true; };
                close.MouseLeftButtonUp += (s, e) => { _trayItems.Remove(p); RebuildTray(); e.Handled = true; };

                sp.Children.Add(name);
                sp.Children.Add(close);
                chip.Child = sp;

                // Tıkla = aç, sürükle = taşı/kopyala
                Point? dragStart = null;
                bool dragging = false;

                chip.MouseLeftButtonDown += (s, e) => { dragStart = e.GetPosition(null); dragging = false; };
                chip.MouseMove += (s, e) =>
                {
                    if (e.LeftButton != MouseButtonState.Pressed || !dragStart.HasValue || dragging) return;
                    var pos = e.GetPosition(null);
                    if (Math.Abs(pos.X - dragStart.Value.X) < SystemParameters.MinimumHorizontalDragDistance &&
                        Math.Abs(pos.Y - dragStart.Value.Y) < SystemParameters.MinimumVerticalDragDistance) return;

                    dragging = true;
                    StartTrayDrag(chip, p);
                };
                chip.MouseLeftButtonUp += (s, e) =>
                {
                    bool wasDrag = dragging;
                    dragStart = null;
                    dragging = false;
                    if (!wasDrag) LaunchPath(p);
                };
                chip.MouseRightButtonUp += (s, e) => { _trayItems.Remove(p); RebuildTray(); e.Handled = true; };

                TrayItemsPanel.Children.Add(chip);
            }
        }

        /// <summary>Raftaki öğeyi Explorer'a / başka bir klasöre sürüklemeyi başlatır.</summary>
        private void StartTrayDrag(DependencyObject source, string path)
        {
            if (!File.Exists(path) && !Directory.Exists(path))
            {
                _trayItems.Remove(path);
                RebuildTray();
                return;
            }

            var data = new DataObject(DataFormats.FileDrop, new[] { path });

            _suspendOutsideClose = true;
            try
            {
                DragDrop.DoDragDrop(source, data, DragDropEffects.Copy | DragDropEffects.Move | DragDropEffects.Link);
            }
            catch { }
            finally
            {
                _suspendOutsideClose = false;
            }

            // Dosya taşındıysa (artık eski yerinde yoksa) raftan da düş
            if (!File.Exists(path) && !Directory.Exists(path))
                _trayItems.Remove(path);

            RebuildTray();
        }

        // ===================== WIDGET DÜZENİ =====================

        private FrameworkElement WidgetElement(string id)
        {
            switch (id)
            {
                case "timer": return TimerCard;
                case "slots": return SlotsCard;
                case "music": return MusicCard;
                case "weather": return WeatherCard;
                default: return null;
            }
        }

        private static string WidgetDisplayName(string id)
        {
            int i = Array.IndexOf(WidgetIds, id);
            return i >= 0 ? WidgetNames[i] : "Boş";
        }

        private void ApplyLayout()
        {
            if (TimerCard == null) return;

            var all = new FrameworkElement[] { TimerCard, SlotsCard, MusicCard, WeatherCard };
            foreach (var el in all) el.Visibility = Visibility.Collapsed;

            var empties = new[] { EmptyCell0Btn, EmptyCell1Btn, EmptyCell2Btn, EmptyCell3Btn };
            var layoutBtns = new[] { LayoutCell0Btn, LayoutCell1Btn, LayoutCell2Btn, LayoutCell3Btn };

            for (int i = 0; i < 4; i++)
            {
                int col = (i % 2 == 0) ? 0 : 2;
                int row = (i < 2) ? 0 : 2;

                var el = WidgetElement(_cells[i]);
                if (el != null)
                {
                    Grid.SetColumn(el, col);
                    Grid.SetRow(el, row);
                    el.Visibility = Visibility.Visible;
                    empties[i].Visibility = Visibility.Collapsed;
                }
                else
                {
                    Grid.SetColumn(empties[i], col);
                    Grid.SetRow(empties[i], row);
                    empties[i].Visibility = Visibility.Visible;
                }

                SetTileVisual(layoutBtns[i], _cells[i]);
            }
        }

        private static readonly string[] WidgetSubs = { "Geri sayım", "Hızlı başlatma", "Şimdi çalan", "Anlık hava durumu" };

        private static string WidgetIconData(string id)
        {
            switch (id)
            {
                case "timer": return "M4,12 A8,8 0 1 0 20,12 A8,8 0 1 0 4,12 Z M12,7.5 V12 L15,14";
                case "slots": return "M4,4 H10 V10 H4 Z M14,4 H20 V10 H14 Z M4,14 H10 V20 H4 Z M14,14 H20 V20 H14 Z";
                case "music": return "M9,18 V6 L19,4 V16 M9,18 A2.5,2.5 0 1 1 4,18 A2.5,2.5 0 1 1 9,18 Z M19,16 A2.5,2.5 0 1 1 14,16 A2.5,2.5 0 1 1 19,16 Z";
                case "weather": return WeatherIconData("cloud");
                default: return "";
            }
        }

        /// <summary>Ayarlardaki düzen kutusunun içeriğini (ikon + ad + açıklama) oluşturur.</summary>
        private void SetTileVisual(Button btn, string id)
        {
            if (string.IsNullOrEmpty(id))
            {
                btn.Tag = null;
                var empty = new TextBlock
                {
                    Text = "+  Boş  ·  eklemek için tıkla",
                    FontFamily = new FontFamily("Segoe UI"),
                    FontSize = 11,
                    FontWeight = FontWeights.SemiBold,
                    HorizontalAlignment = HorizontalAlignment.Center
                };
                empty.SetResourceReference(TextBlock.ForegroundProperty, "SecondaryTextBrush");
                btn.Content = empty;
                return;
            }

            btn.Tag = id;
            int k = Array.IndexOf(WidgetIds, id);

            var iconBox = new Border
            {
                Width = 32,
                Height = 32,
                CornerRadius = new CornerRadius(9),
                Margin = new Thickness(0, 0, 10, 0),
                VerticalAlignment = VerticalAlignment.Center
            };
            iconBox.SetResourceReference(Border.BackgroundProperty, "TabBarBgBrush");

            var icon = new System.Windows.Shapes.Path
            {
                Data = Geometry.Parse(WidgetIconData(id)),
                StrokeThickness = 1.8,
                StrokeStartLineCap = PenLineCap.Round,
                StrokeEndLineCap = PenLineCap.Round,
                StrokeLineJoin = PenLineJoin.Round,
                Stretch = Stretch.Uniform,
                Width = 16,
                Height = 16,
                HorizontalAlignment = HorizontalAlignment.Center,
                VerticalAlignment = VerticalAlignment.Center
            };
            icon.SetResourceReference(System.Windows.Shapes.Shape.StrokeProperty, "AccentBrush");
            iconBox.Child = icon;

            var name = new TextBlock
            {
                Text = WidgetNames[k],
                FontFamily = new FontFamily("Segoe UI"),
                FontSize = 12,
                FontWeight = FontWeights.SemiBold,
                TextTrimming = TextTrimming.CharacterEllipsis
            };
            name.SetResourceReference(TextBlock.ForegroundProperty, "PrimaryTextBrush");

            var sub = new TextBlock
            {
                Text = WidgetSubs[k],
                FontFamily = new FontFamily("Segoe UI"),
                FontSize = 10,
                Margin = new Thickness(0, 1, 0, 0),
                TextTrimming = TextTrimming.CharacterEllipsis
            };
            sub.SetResourceReference(TextBlock.ForegroundProperty, "TertiaryTextBrush");

            var texts = new StackPanel { VerticalAlignment = VerticalAlignment.Center };
            texts.Children.Add(name);
            texts.Children.Add(sub);

            var row = new StackPanel { Orientation = Orientation.Horizontal, Margin = new Thickness(12, 0, 8, 0) };
            row.Children.Add(iconBox);
            row.Children.Add(texts);
            btn.Content = row;
        }

        private void AssignWidget(int cell, string id)
        {
            if (string.IsNullOrEmpty(id))
            {
                _cells[cell] = "";
            }
            else
            {
                int other = Array.IndexOf(_cells, id);
                string previous = _cells[cell];
                _cells[cell] = id;
                if (other >= 0 && other != cell) _cells[other] = previous ?? "";   // yer değiştir
            }

            ApplyLayout();
            SaveSettings();
        }

        private void ShowWidgetPicker(FrameworkElement anchor, int cell)
        {
            WidgetPickerPanel.Children.Clear();

            for (int k = 0; k < WidgetIds.Length; k++)
            {
                string id = WidgetIds[k];
                bool current = _cells[cell] == id;
                bool placedElsewhere = !current && Array.IndexOf(_cells, id) >= 0;

                string label = (current ? "✓  " : "") + WidgetNames[k] + (placedElsewhere ? "  (taşı)" : "");
                WidgetPickerPanel.Children.Add(MakePickerItem(label, () => { WidgetPickerPopup.IsOpen = false; AssignWidget(cell, id); }));
            }

            if (!string.IsNullOrEmpty(_cells[cell]))
                WidgetPickerPanel.Children.Add(MakePickerItem("Kaldır (boş bırak)", () => { WidgetPickerPopup.IsOpen = false; AssignWidget(cell, ""); }));

            WidgetPickerPopup.PlacementTarget = anchor;
            WidgetPickerPopup.IsOpen = true;
        }

        private Button MakePickerItem(string text, Action onClick)
        {
            var b = new Button
            {
                Content = text,
                Height = 28,
                Margin = new Thickness(0, 2, 0, 2),
                Style = (Style)FindResource("GhostBtn"),
                HorizontalContentAlignment = HorizontalAlignment.Left
            };
            b.Click += (s, e) => onClick();
            return b;
        }

        private void WidgetPicker_Opened(object sender, EventArgs e) { _suspendOutsideClose = true; }
        private void WidgetPicker_Closed(object sender, EventArgs e) { _suspendOutsideClose = false; }

        private void LayoutCell_Click(object sender, RoutedEventArgs e)
        {
            var btns = new[] { LayoutCell0Btn, LayoutCell1Btn, LayoutCell2Btn, LayoutCell3Btn };
            int idx = Array.IndexOf(btns, sender as Button);
            if (idx >= 0) ShowWidgetPicker((FrameworkElement)sender, idx);
        }

        private void EmptyCell_Click(object sender, RoutedEventArgs e)
        {
            var btns = new[] { EmptyCell0Btn, EmptyCell1Btn, EmptyCell2Btn, EmptyCell3Btn };
            int idx = Array.IndexOf(btns, sender as Button);
            if (idx >= 0) ShowWidgetPicker((FrameworkElement)sender, idx);
        }

        private void LayoutReset_Click(object sender, RoutedEventArgs e)
        {
            _cells = new[] { "timer", "slots", "music", "weather" };
            ApplyLayout();
            SaveSettings();
        }

        // ===================== HAVA DURUMU =====================

        private static HttpClient CreateHttp()
        {
            var c = new HttpClient { Timeout = TimeSpan.FromSeconds(10) };
            c.DefaultRequestHeaders.UserAgent.ParseAdd("DynamicIslandWin/1.0");
            return c;
        }

        private void StartWeather()
        {
            _weatherTimer = new DispatcherTimer { Interval = TimeSpan.FromMinutes(20) };
            _weatherTimer.Tick += async (s, e) => await RefreshWeatherAsync(false);
            _weatherTimer.Start();
            var ignored = RefreshWeatherAsync(false);
        }

        private void WeatherCityInput_KeyDown(object sender, KeyEventArgs e)
        {
            if (e.Key == Key.Enter)
            {
                e.Handled = true;
                ApplyWeatherCity();
            }
        }

        private void WeatherCityInput_LostFocus(object sender, RoutedEventArgs e)
        {
            ApplyWeatherCity();
        }

        private void ApplyWeatherCity()
        {
            if (WeatherCityInput == null) return;
            string c = (WeatherCityInput.Text ?? "").Trim();
            if (c == _weatherCity) return;

            _weatherCity = c;
            SaveSettings();
            _wLat = null;
            Keyboard.ClearFocus();
            var ignored = RefreshWeatherAsync(true);
        }

        private async System.Threading.Tasks.Task ResolveLocationAsync()
        {
            _wLat = null; _wLon = null; _wName = null;

            if (!string.IsNullOrWhiteSpace(_weatherCity))
            {
                string url = "https://geocoding-api.open-meteo.com/v1/search?name=" +
                             Uri.EscapeDataString(_weatherCity) + "&count=1&language=tr&format=json";
                using (var doc = JsonDocument.Parse(await Http.GetStringAsync(url)))
                {
                    JsonElement results;
                    if (doc.RootElement.TryGetProperty("results", out results) && results.GetArrayLength() > 0)
                    {
                        var r = results[0];
                        _wLat = r.GetProperty("latitude").GetDouble();
                        _wLon = r.GetProperty("longitude").GetDouble();
                        JsonElement nm;
                        _wName = r.TryGetProperty("name", out nm) ? nm.GetString() : _weatherCity;
                    }
                }
            }
            else
            {
                using (var doc = JsonDocument.Parse(await Http.GetStringAsync("https://ipwho.is/")))
                {
                    var root = doc.RootElement;
                    JsonElement ok;
                    if (root.TryGetProperty("success", out ok) && ok.ValueKind == JsonValueKind.False) return;

                    _wLat = root.GetProperty("latitude").GetDouble();
                    _wLon = root.GetProperty("longitude").GetDouble();
                    JsonElement city;
                    _wName = root.TryGetProperty("city", out city) ? city.GetString() : "Konum";
                }
            }
        }

        private async System.Threading.Tasks.Task RefreshWeatherAsync(bool relocate)
        {
            if (_weatherBusy) return;
            _weatherBusy = true;

            try
            {
                if (!_wLat.HasValue || relocate) await ResolveLocationAsync();

                if (!_wLat.HasValue || !_wLon.HasValue)
                {
                    ShowWeatherError(string.IsNullOrWhiteSpace(_weatherCity) ? "Konum bulunamadı" : "Şehir bulunamadı");
                    return;
                }

                string url = "https://api.open-meteo.com/v1/forecast?latitude=" +
                             _wLat.Value.ToString(CultureInfo.InvariantCulture) +
                             "&longitude=" + _wLon.Value.ToString(CultureInfo.InvariantCulture) +
                             "&current=temperature_2m,weather_code,is_day&timezone=auto";

                using (var doc = JsonDocument.Parse(await Http.GetStringAsync(url)))
                {
                    var cur = doc.RootElement.GetProperty("current");
                    double temp = cur.GetProperty("temperature_2m").GetDouble();
                    int code = cur.GetProperty("weather_code").GetInt32();
                    bool day = cur.GetProperty("is_day").GetInt32() == 1;

                    string desc, kind;
                    DescribeWeather(code, day, out desc, out kind);

                    WeatherCityText.Text = _wName ?? "";
                    WeatherDescText.Text = desc;
                    WeatherTempText.Text = temp.ToString("0.0", TrCulture) + "°C";

                    var geo = Geometry.Parse(WeatherIconData(kind));
                    WeatherBigIcon.Data = geo;
                    WeatherSmallIcon.Data = geo;
                }

                _weatherTimer.Interval = TimeSpan.FromMinutes(20);
            }
            catch
            {
                ShowWeatherError("Bağlantı yok");
                if (_weatherTimer != null) _weatherTimer.Interval = TimeSpan.FromMinutes(2);
            }
            finally
            {
                _weatherBusy = false;
            }
        }

        private void ShowWeatherError(string message)
        {
            WeatherCityText.Text = _wName ?? "Hava durumu";
            WeatherDescText.Text = message;
            WeatherTempText.Text = "--°C";
            var geo = Geometry.Parse(WeatherIconData("cloud"));
            WeatherBigIcon.Data = geo;
            WeatherSmallIcon.Data = geo;
        }

        private static void DescribeWeather(int code, bool day, out string desc, out string kind)
        {
            switch (code)
            {
                case 0: desc = "Açık"; kind = day ? "sun" : "moon"; break;
                case 1: desc = "Çoğunlukla açık"; kind = day ? "sun" : "moon"; break;
                case 2: desc = "Parçalı bulutlu"; kind = "cloud"; break;
                case 3: desc = "Kapalı"; kind = "cloud"; break;
                case 45: case 48: desc = "Sisli"; kind = "fog"; break;
                case 51: case 53: case 55: case 56: case 57: desc = "Çiseleme"; kind = "rain"; break;
                case 61: case 63: case 65: case 66: case 67: desc = "Yağmurlu"; kind = "rain"; break;
                case 71: case 73: case 75: case 77: desc = "Karlı"; kind = "snow"; break;
                case 80: case 81: case 82: desc = "Sağanak yağış"; kind = "rain"; break;
                case 85: case 86: desc = "Kar sağanağı"; kind = "snow"; break;
                case 95: case 96: case 99: desc = "Gök gürültülü fırtına"; kind = "storm"; break;
                default: desc = "Bulutlu"; kind = "cloud"; break;
            }
        }

        private const string CloudPath = "M7,18 H17.5 A4,4 0 0 0 18,10.1 A6,6 0 0 0 6.5,9.2 A4.5,4.5 0 0 0 7,18 Z";

        private static string WeatherIconData(string kind)
        {
            switch (kind)
            {
                case "sun":
                    return "M8,12 A4,4 0 1 0 16,12 A4,4 0 1 0 8,12 Z M12,2 V4 M12,20 V22 M2,12 H4 M20,12 H22 M4.9,4.9 L6.3,6.3 M17.7,17.7 L19.1,19.1 M4.9,19.1 L6.3,17.7 M17.7,6.3 L19.1,4.9";
                case "moon":
                    return "M20,14.5 A8,8 0 1 1 9.5,4 A6.5,6.5 0 0 0 20,14.5 Z";
                case "rain":
                    return CloudPath + " M8,20 L7,22.5 M12,20 L11,22.5 M16,20 L15,22.5";
                case "snow":
                    return CloudPath + " M8,21 H8.01 M12,21 H12.01 M16,21 H16.01 M10,23 H10.01 M14,23 H14.01";
                case "storm":
                    return CloudPath + " M13,18.5 L10,22 H13.5 L11,24.5";
                case "fog":
                    return "M4,8 H20 M3,12 H21 M5,16 H19 M8,20 H16";
                default:
                    return CloudPath;
            }
        }

        // ===================== MÜZİK DURAKLATMA =====================

        private void MusicPauseDelayTimer_Tick(object sender, EventArgs e)
        {
            _musicPauseDelayTimer.Stop();

            if (_currentSession != null)
            {
                try
                {
                    var info = _currentSession.GetPlaybackInfo();
                    if (info?.PlaybackStatus == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing)
                        return;
                }
                catch { }
            }

            SetMusicState(false);
            UpdateEqualizerMotion(false);
        }

        // ===================== MÜZİK ALGILAMA =====================

        private async System.Threading.Tasks.Task RefreshMusicStateAsync()
        {
            if (_mediaSessionManager == null) { HandleNoMusic(); return; }

            GlobalSystemMediaTransportControlsSession session;
            try { session = _mediaSessionManager.GetCurrentSession(); }
            catch { HandleNoMusic(); return; }

            if (session == null) { HandleNoMusic(); return; }

            GlobalSystemMediaTransportControlsSessionPlaybackInfo playbackInfo;
            try { playbackInfo = session.GetPlaybackInfo(); }
            catch { HandleNoMusic(); return; }

            var status = playbackInfo?.PlaybackStatus;
            bool hasMusicSession = status == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing ||
                                   status == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Paused;

            if (!hasMusicSession) { HandleNoMusic(); return; }

            if (status == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing)
            {
                _musicPauseDelayTimer.Stop();
            }
            else
            {
                if (!_isShowingMusic && !_musicPauseDelayTimer.IsEnabled) return;
                if (!_musicPauseDelayTimer.IsEnabled) _musicPauseDelayTimer.Start();
            }

            _currentSession = session;
            bool nowPlaying = status == GlobalSystemMediaTransportControlsSessionPlaybackStatus.Playing;

            GlobalSystemMediaTransportControlsSessionMediaProperties props;
            try { props = await session.TryGetMediaPropertiesAsync(); }
            catch { props = null; }

            _musicIdleShown = false;
            SetMusicState(true);
            UpdateEqualizerMotion(nowPlaying);
            UpdatePlayPauseIcon(nowPlaying);
            UpdateProgressUI(session);

            if (props != null)
            {
                string trackKey = props.Title + "|" + props.Artist;
                bool trackChanged = trackKey != _lastTrackKey;
                _lastTrackKey = trackKey;

                var displayTitle = string.IsNullOrWhiteSpace(props.Title) ? "Bilinmeyen Şarkı" : props.Title;

                CompactTitleText.Text = displayTitle;
                ExpandedSongTitleText.Text = displayTitle;
                ExpandedArtistText.Text = props.Artist ?? "";

                if (trackChanged)
                {
                    BitmapImage art = null;
                    if (props.Thumbnail != null)
                        art = await TryLoadThumbnailAsync(props.Thumbnail);

                    if (art != null)
                    {
                        AlbumArtImage.Source = art;
                        AlbumArtImage.Visibility = Visibility.Visible;
                        FallbackNoteIcon.Visibility = Visibility.Collapsed;

                        ExpandedAlbumArtImage.Source = art;
                        ExpandedAlbumArtImage.Visibility = Visibility.Visible;
                        ExpandedFallbackNoteIcon.Visibility = Visibility.Collapsed;
                    }
                    else
                    {
                        AlbumArtImage.Visibility = Visibility.Collapsed;
                        FallbackNoteIcon.Visibility = Visibility.Visible;

                        ExpandedAlbumArtImage.Visibility = Visibility.Collapsed;
                        ExpandedFallbackNoteIcon.Visibility = Visibility.Visible;
                    }
                }
            }
        }

        private void HandleNoMusic()
        {
            _musicPauseDelayTimer.Stop();
            _currentSession = null;
            _lastTrackKey = null;
            SetMusicState(false);
            UpdateEqualizerMotion(false);

            if (!_musicIdleShown)
            {
                _musicIdleShown = true;
                ExpandedSongTitleText.Text = "Müzik çalmıyor";
                ExpandedArtistText.Text = "";
                ExpandedAlbumArtImage.Visibility = Visibility.Collapsed;
                ExpandedFallbackNoteIcon.Visibility = Visibility.Visible;
                ProgressFilledColumn.Width = new GridLength(0, GridUnitType.Star);
                ProgressRemainingColumn.Width = new GridLength(1, GridUnitType.Star);
                UpdatePlayPauseIcon(false);
            }
        }

        private void UpdateProgressUI(GlobalSystemMediaTransportControlsSession session)
        {
            try
            {
                var timeline = session.GetTimelineProperties();
                var elapsed = timeline.Position - timeline.StartTime;
                var total = timeline.EndTime - timeline.StartTime;

                if (total.TotalSeconds > 0 && elapsed.TotalSeconds >= 0)
                {
                    double elapsedSec = Math.Min(elapsed.TotalSeconds, total.TotalSeconds);
                    double remainingSec = Math.Max(total.TotalSeconds - elapsedSec, 0.01);

                    ProgressFilledColumn.Width = new GridLength(elapsedSec, GridUnitType.Star);
                    ProgressRemainingColumn.Width = new GridLength(remainingSec, GridUnitType.Star);
                    ProgressTimeText.Text = $"{FormatTime(elapsed)} / {FormatTime(total)}";
                }
                else
                {
                    ProgressFilledColumn.Width = new GridLength(0, GridUnitType.Star);
                    ProgressRemainingColumn.Width = new GridLength(1, GridUnitType.Star);
                    ProgressTimeText.Text = "--:--";
                }
            }
            catch
            {
                ProgressFilledColumn.Width = new GridLength(0, GridUnitType.Star);
                ProgressRemainingColumn.Width = new GridLength(1, GridUnitType.Star);
                ProgressTimeText.Text = "--:--";
            }
        }

        private static string FormatTime(TimeSpan ts)
        {
            if (ts < TimeSpan.Zero) ts = TimeSpan.Zero;
            int totalMinutes = (int)ts.TotalMinutes;
            int seconds = ts.Seconds;
            return $"{totalMinutes}:{seconds:D2}";
        }

        private void UpdatePlayPauseIcon(bool playing)
        {
            PlayPauseIcon.Data = System.Windows.Media.Geometry.Parse(playing ? PauseIconData : PlayIconData);
        }

        private async System.Threading.Tasks.Task<BitmapImage> TryLoadThumbnailAsync(IRandomAccessStreamReference thumbnailRef)
        {
            try
            {
                using IRandomAccessStreamWithContentType stream = await thumbnailRef.OpenReadAsync();
                using var netStream = stream.AsStreamForRead();
                using var memoryStream = new MemoryStream();

                await netStream.CopyToAsync(memoryStream);
                memoryStream.Position = 0;

                var bitmap = new BitmapImage();
                bitmap.BeginInit();
                bitmap.CacheOption = BitmapCacheOption.OnLoad;
                bitmap.StreamSource = memoryStream;
                bitmap.EndInit();
                bitmap.Freeze();
                return bitmap;
            }
            catch { return null; }
        }

        // ===================== KONTROL BUTONLARI =====================

        private async void PlayPauseButton_Click(object sender, RoutedEventArgs e)
        {
            if (_currentSession == null) return;
            try
            {
                if (_isPlaying) await _currentSession.TryPauseAsync();
                else await _currentSession.TryPlayAsync();
            }
            catch { }
            await RefreshMusicStateAsync();
        }

        private async void NextButton_Click(object sender, RoutedEventArgs e)
        {
            if (_currentSession == null) return;
            try { await _currentSession.TrySkipNextAsync(); } catch { }
            await RefreshMusicStateAsync();
        }

        private async void PreviousButton_Click(object sender, RoutedEventArgs e)
        {
            if (_currentSession == null) return;
            try { await _currentSession.TrySkipPreviousAsync(); } catch { }
            await RefreshMusicStateAsync();
        }

        // ===================== DURUM / GÖRÜNÜM =====================

        private void SetMusicState(bool show)
        {
            if (_isShowingMusic == show) return;
            _isShowingMusic = show;
            UpdateVisualState();
        }

        private void UpdateVisualState()
        {
            FrameworkElement targetPanel;
            double targetWidth, targetHeight;

            if (_isExpanded)
            {
                targetPanel = ExpandedPanel;
                if (_isSettingsOpen)
                {
                    targetWidth = ExpandedSettingsWidth;
                    targetHeight = ExpandedSettingsHeight;
                }
                else
                {
                    targetWidth = ExpandedWidgetsWidth;
                    targetHeight = ExpandedWidgetsHeight;
                }
            }
            else
            {
                targetPanel = _isShowingMusic ? CompactMusicPanel : CompactClockPanel;
                targetWidth = CompactWidth;
                targetHeight = CompactHeight;
            }

            if (targetPanel != _currentPanel)
            {
                var previousPanel = _currentPanel;
                _currentPanel = targetPanel;
                CrossFadePanels(previousPanel, targetPanel);
            }

            AnimateIslandSize(targetWidth, targetHeight);
        }

        private void CrossFadePanels(FrameworkElement from, FrameworkElement to)
        {
            if (from == to) return;

            var easeOut = new CubicEase { EasingMode = EasingMode.EaseOut };
            var easeIn = new CubicEase { EasingMode = EasingMode.EaseIn };

            foreach (var p in _allPanels) p.BeginAnimation(OpacityProperty, null);

            // Çıkan panel: hızlıca solar ve hafifçe küçülür
            if (from != null && from.Visibility == Visibility.Visible)
            {
                var outScale = new ScaleTransform(1, 1);
                from.RenderTransformOrigin = new Point(0.5, 0.5);
                from.RenderTransform = outScale;

                var dur = TimeSpan.FromMilliseconds(130);
                var fadeOut = new DoubleAnimation(from.Opacity, 0, dur) { EasingFunction = easeIn, FillBehavior = FillBehavior.HoldEnd };
                fadeOut.Completed += (s, e) => { from.Visibility = Visibility.Collapsed; };
                from.BeginAnimation(OpacityProperty, fadeOut);

                var sx = new DoubleAnimation(1, 0.94, dur) { EasingFunction = easeIn };
                outScale.BeginAnimation(ScaleTransform.ScaleXProperty, sx);
                outScale.BeginAnimation(ScaleTransform.ScaleYProperty, sx);
            }

            // Gelen panel: ada büyürken gecikmeli olarak belirir, yerine oturur
            var inScale = new ScaleTransform(0.92, 0.92);
            to.RenderTransformOrigin = new Point(0.5, 0.5);
            to.RenderTransform = inScale;
            to.Visibility = Visibility.Visible;
            to.Opacity = 0;

            var inDur = TimeSpan.FromMilliseconds(260);
            var inBegin = TimeSpan.FromMilliseconds(90);

            to.BeginAnimation(OpacityProperty,
                new DoubleAnimation(0, 1, inDur) { BeginTime = inBegin, EasingFunction = easeOut, FillBehavior = FillBehavior.HoldEnd });

            var grow = new DoubleAnimation(0.92, 1, inDur) { BeginTime = inBegin, EasingFunction = easeOut };
            grow.Completed += (s, e) =>
            {
                inScale.BeginAnimation(ScaleTransform.ScaleXProperty, null);
                inScale.BeginAnimation(ScaleTransform.ScaleYProperty, null);
                inScale.ScaleX = 1; inScale.ScaleY = 1;
            };
            inScale.BeginAnimation(ScaleTransform.ScaleXProperty, grow);
            inScale.BeginAnimation(ScaleTransform.ScaleYProperty, grow);

            foreach (var p in _allPanels)
            {
                if (p != from && p != to)
                {
                    p.Visibility = Visibility.Collapsed;
                    p.Opacity = 0;
                }
            }
        }

        private void AnimateIslandSize(double targetWidth, double targetHeight)
        {
            double currentWidth = IslandContainer.ActualWidth > 0 ? IslandContainer.ActualWidth : IslandContainer.Width;
            double currentHeight = IslandContainer.ActualHeight > 0 ? IslandContainer.ActualHeight : IslandContainer.Height;

            bool growing = targetWidth * targetHeight > currentWidth * currentHeight;

            IEasingFunction widthEase, heightEase;
            TimeSpan duration;
            if (growing)
            {
                // Genişlik hafif yaylanır; yükseklik pencere sınırını aşmasın diye taşmadan oturur
                widthEase = new BackEase { EasingMode = EasingMode.EaseOut, Amplitude = 0.45 };
                heightEase = new QuinticEase { EasingMode = EasingMode.EaseOut };
                duration = TimeSpan.FromMilliseconds(420);
            }
            else
            {
                widthEase = new CubicEase { EasingMode = EasingMode.EaseInOut };
                heightEase = new CubicEase { EasingMode = EasingMode.EaseInOut };
                duration = TimeSpan.FromMilliseconds(300);
            }

            var wAnim = new DoubleAnimation(currentWidth, targetWidth, duration) { EasingFunction = widthEase };
            var hAnim = new DoubleAnimation(currentHeight, targetHeight, duration) { EasingFunction = heightEase };

            wAnim.Completed += (s, e) =>
            {
                IslandContainer.BeginAnimation(WidthProperty, null);
                IslandContainer.Width = targetWidth;
            };
            hAnim.Completed += (s, e) =>
            {
                IslandContainer.BeginAnimation(HeightProperty, null);
                IslandContainer.Height = targetHeight;
            };

            IslandContainer.BeginAnimation(WidthProperty, wAnim);
            IslandContainer.BeginAnimation(HeightProperty, hAnim);
        }

        // ===================== EŞİTLEYİCİ =====================

        private void UpdateEqualizerMotion(bool playing)
        {
            if (_isPlaying == playing) return;
            _isPlaying = playing;

            if (playing)
            {
                AnimateBar(Bar1Scale, 0.25, 1.0, 340, 0);
                AnimateBar(Bar2Scale, 0.35, 1.0, 260, 60);
                AnimateBar(Bar3Scale, 0.20, 1.0, 300, 130);
                AnimateBar(Bar4Scale, 0.40, 1.0, 230, 30);
            }
            else
            {
                DecelerateBar(Bar1Scale);
                DecelerateBar(Bar2Scale);
                DecelerateBar(Bar3Scale);
                DecelerateBar(Bar4Scale);
            }
        }

        private void AnimateBar(ScaleTransform target, double minScale, double maxScale, int durationMs, int beginDelayMs)
        {
            var anim = new DoubleAnimation
            {
                From = minScale,
                To = maxScale,
                Duration = TimeSpan.FromMilliseconds(durationMs),
                AutoReverse = true,
                RepeatBehavior = RepeatBehavior.Forever,
                BeginTime = TimeSpan.FromMilliseconds(beginDelayMs),
                EasingFunction = new SineEase { EasingMode = EasingMode.EaseInOut }
            };
            target.BeginAnimation(ScaleTransform.ScaleYProperty, anim);
        }

        private void DecelerateBar(ScaleTransform target)
        {
            double currentValue = target.ScaleY;
            target.BeginAnimation(ScaleTransform.ScaleYProperty, null);
            target.ScaleY = currentValue;

            var settle = new DoubleAnimation
            {
                To = 0.2,
                Duration = TimeSpan.FromMilliseconds(400),
                EasingFunction = new QuadraticEase { EasingMode = EasingMode.EaseOut }
            };
            target.BeginAnimation(ScaleTransform.ScaleYProperty, settle);
        }
    }
}