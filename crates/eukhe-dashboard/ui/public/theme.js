// No-flash theme bootstrap, loaded blocking in <head> (the CSP forbids
// inline scripts). Every color is `light-dark()`, so the root's
// `color-scheme` picks the palette: a forced theme lives in
// localStorage.theme, otherwise the OS preference applies. The app keeps
// both in sync afterwards (src/lib/actions.ts, applyTheme).
{
  const root = document.documentElement;
  let theme = null;
  try {
    theme = localStorage.getItem('theme');
  } catch {
    // Storage blocked: follow the OS.
  }
  const forced = theme === 'dark' || theme === 'light' ? theme : null;
  root.style.colorScheme = forced || 'light dark';
  const dark = forced ? forced === 'dark' : matchMedia('(prefers-color-scheme: dark)').matches;
  for (const meta of document.querySelectorAll('meta[name="theme-color"]')) {
    meta.setAttribute('content', dark ? '#212121' : '#ffffff');
  }
}
