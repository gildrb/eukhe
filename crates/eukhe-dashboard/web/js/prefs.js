// Dashboard preferences: persisted in localStorage, mirrored in
// `state.prefs`. The theme also lives under `theme` (read by theme.js
// before first paint).

import { store, PREFS_KEY } from './store.js';

const THEME_COLOR = { dark: '#000000', light: '#ffffff' };
const systemDark = matchMedia('(prefers-color-scheme: dark)');

/** The theme in effect: the forced one, else the OS preference. */
export function effectiveTheme(theme = store.get().prefs.theme) {
  if (theme === 'dark' || theme === 'light') return theme;
  return systemDark.matches ? 'dark' : 'light';
}

function applyTheme(theme) {
  const root = document.documentElement;
  root.classList.remove('theme-dark', 'theme-light');
  if (theme === 'dark' || theme === 'light') root.classList.add(`theme-${theme}`);
  const color = THEME_COLOR[effectiveTheme(theme)];
  for (const meta of document.querySelectorAll('meta[name="theme-color"]')) meta.setAttribute('content', color);
  try {
    if (theme === 'system') localStorage.removeItem('theme');
    else localStorage.setItem('theme', theme);
  } catch {
    // Private mode: the choice lasts for this tab.
  }
}

/** True when this context can show notifications at all. */
export function notificationsSupported() {
  return window.isSecureContext && 'Notification' in window;
}

/**
 * Set one preference (`theme`, `enterSendsOnTouch`, `notify`). Resolves
 * false when the value could not take effect (notification permission
 * denied or unsupported).
 */
export async function setPref(key, value) {
  let effective = value;
  if (key === 'notify' && value) {
    if (!notificationsSupported()) effective = false;
    else if (Notification.permission !== 'granted') effective = (await Notification.requestPermission()) === 'granted';
  }
  if (key === 'theme') applyTheme(value);
  const prefs = { ...store.get().prefs, [key]: effective };
  store.set({ prefs });
  try {
    const { theme: _theme, ...rest } = prefs;
    localStorage.setItem(PREFS_KEY, JSON.stringify(rest));
  } catch {
    // Private mode.
  }
  return effective === value;
}
