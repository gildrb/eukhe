// No-flash theme bootstrap (gildrb themeScript), loaded blocking in <head>
// because the CSP forbids inline scripts. A forced theme lives in
// localStorage.theme; otherwise the OS preference applies. Keeps
// <meta name="theme-color"> in sync with the scheme in effect.
{
  const classes = { dark: 'theme-dark', light: 'theme-light' };
  const colors = { dark: '#000000', light: '#ffffff' };
  const root = document.documentElement;
  const query = matchMedia('(prefers-color-scheme: dark)');
  try {
    const theme = localStorage.getItem('theme');
    if (theme === 'dark' || theme === 'light') root.classList.add(classes[theme]);
  } catch {
    // Storage blocked: follow the OS.
  }
  const sync = () => {
    const forced = ['dark', 'light'].find((theme) => root.classList.contains(classes[theme]));
    const color = colors[forced || (query.matches ? 'dark' : 'light')];
    for (const meta of document.querySelectorAll('meta[name="theme-color"]')) meta.setAttribute('content', color);
  };
  sync();
  query.addEventListener('change', sync);
}
