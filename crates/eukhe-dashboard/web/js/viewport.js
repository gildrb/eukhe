// The visual viewport (iOS ignores interactive-widget): `--vvh` is the
// visible height, `--keyboard` the on-screen keyboard's height, and
// `data-kb="open"` hides the nav row and lane bar while typing. JS writes
// only custom properties through CSSOM (the CSP allows that).

const KEYBOARD_THRESHOLD_PX = 120;
const root = document.documentElement;
let frame = 0;
// Android Chrome resizes the layout viewport with the keyboard
// (resizes-content), so compare against the tallest height seen at this
// width as well as against innerHeight (iOS).
let tallest = 0;
let tallestWidth = 0;

function editing() {
  const active = document.activeElement;
  return Boolean(active && (active.tagName === 'TEXTAREA' || (active.tagName === 'INPUT' && !['checkbox', 'radio', 'button'].includes(active.type)) || active.isContentEditable));
}

function measure() {
  frame = 0;
  const viewport = window.visualViewport;
  const height = viewport ? viewport.height : window.innerHeight;
  if (window.innerWidth !== tallestWidth) {
    tallestWidth = window.innerWidth;
    tallest = 0;
  }
  if (!editing()) tallest = Math.max(tallest, height);
  const covered = Math.max(window.innerHeight - height, tallest - height);
  const open = editing() && covered > KEYBOARD_THRESHOLD_PX;
  root.style.setProperty('--vvh', `${Math.round(height)}px`);
  root.style.setProperty('--keyboard', `${Math.round(open ? Math.max(0, window.innerHeight - height) : 0)}px`);
  if (open) root.dataset.kb = 'open';
  else delete root.dataset.kb;
  // iOS scrolls the layout viewport under the keyboard; pin it back.
  if (viewport && viewport.offsetTop > 0 && open) window.scrollTo(0, 0);
}

function schedule() {
  if (!frame) frame = requestAnimationFrame(measure);
}

/** Start tracking the viewport. */
export function watchViewport() {
  measure();
  if (window.visualViewport) {
    window.visualViewport.addEventListener('resize', schedule);
    window.visualViewport.addEventListener('scroll', schedule);
  }
  window.addEventListener('resize', schedule);
  document.addEventListener('focusin', schedule);
  document.addEventListener('focusout', schedule);
}

/** Keep `--dock-h` equal to `element`'s height (toasts and Latest sit above it). */
export function trackDockHeight(element) {
  const observer = new ResizeObserver(([entry]) => {
    const height = entry.borderBoxSize && entry.borderBoxSize[0] ? entry.borderBoxSize[0].blockSize : entry.contentRect.height;
    root.style.setProperty('--dock-h', `${Math.round(height)}px`);
  });
  observer.observe(element);
  return () => observer.disconnect();
}
