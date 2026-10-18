// Stands in for `react-style-singleton` (vite.config.ts aliases it here).
// Radix's scroll lock (react-remove-scroll) uses it to insert a <style>
// element that hides the page's scrollbar while a dialog or menu is open;
// the dashboard's CSP (`style-src 'self'`) refuses inline <style>, and the
// page never scrolls anyway (html and body are `overflow: hidden`, only
// inner panes scroll). The lock's event handling stays; only the sheet goes.

type Sheet = { add: (css: string) => void; remove: () => void };

export function stylesheetSingleton(): Sheet {
  return { add() {}, remove() {} };
}

export function styleHookSingleton(): (styles: string, isDynamic?: boolean) => void {
  return () => {};
}

export function styleSingleton(): (props: { styles: string; dynamic?: boolean }) => null {
  return () => null;
}
