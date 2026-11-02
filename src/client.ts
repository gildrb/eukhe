/**
 * The terminal the Bend editor (vim/vim.bend) runs in. It decides nothing: it turns browser events
 * into `Ev`s for `Vim.step`, runs the `Act` it gets back (open a URL, copy the install command), and
 * paints `Vim.frame` as a grid of rows x cols cells over the whole window, as a terminal does. The
 * first screen is in the page already (render.tsx paints it at build with the same code, paint.ts):
 * the editor takes it over without a visible change.
 */
import type { EditorFile, Run } from "./markdown.tsx";
import { type CopyAt, cells, floatRows, gutterRows, list, statusParts, textRows } from "./paint.ts";
import Vim, { type BendList, type Buf, type Ev, type Frame, type St } from "./vim.mjs";

/** A touch screen (a phone): no keyboard, a smaller font, the finger scrolls. */
const touch = window.matchMedia("(pointer: coarse)").matches;

function element<T extends Element>(selector: string, type: new () => T): T {
  const found = document.querySelector(selector);
  if (!(found instanceof type)) throw new Error(`${selector} is missing`);
  return found;
}

function cons<T>(items: readonly T[]): BendList<T> {
  return items.reduceRight<BendList<T>>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
}

function isRun(value: unknown): value is Run {
  if (typeof value !== "object" || value === null) return false;
  if (!("from" in value) || typeof value.from !== "number") return false;
  if (!("to" in value) || typeof value.to !== "number") return false;
  if ("href" in value && typeof value.href !== "string") return false;
  if (!("hl" in value) || typeof value.hl !== "string") return false;
  return ["title", "muted", "heading", "link"].includes(value.hl);
}

function isStrings(value: unknown): value is string[] {
  return Array.isArray(value) && value.every((item: unknown) => typeof item === "string");
}

/** files.json, as render.tsx writes it. */
function isEditorFile(value: unknown): value is EditorFile {
  if (typeof value !== "object" || value === null) return false;
  if (!("path" in value) || typeof value.path !== "string") return false;
  if (!("lines" in value) || !isStrings(value.lines)) return false;
  if (!("runs" in value) || !Array.isArray(value.runs)) return false;
  if (!value.runs.every((row: unknown) => Array.isArray(row) && row.every(isRun))) return false;
  return "copy" in value && (value.copy === null || typeof value.copy === "number");
}

async function loadFiles(text: Promise<string>): Promise<EditorFile[]> {
  const data: unknown = JSON.parse(await text);
  if (!Array.isArray(data) || !data.every(isEditorFile))
    throw new Error("/files.json is malformed");
  return data;
}

const term = element("[data-term]", HTMLElement);
const cursor = element("[data-cursor]", HTMLElement);

/** Ghostty's window padding. */
const pad = 2;
/** A cell (render.tsx sets it in CSS: 0.6em of the font by its line height). */
let cw = 9;
let lh = 18;

function measure() {
  const style = getComputedStyle(term);
  cw = Number.parseFloat(style.getPropertyValue("--cw"));
  lh = Number.parseFloat(style.getPropertyValue("--lh"));
  if (!(cw > 0 && lh > 0)) throw new Error(`cell ${cw}x${lh}`);
}

/** The window in cells, less the padding. */
function size(): { rows: number; cols: number } {
  return {
    rows: Math.max(3, Math.floor((window.innerHeight - 2 * pad) / lh)),
    cols: Math.max(12, Math.floor((window.innerWidth - 2 * pad) / cw)),
  };
}

/** Vim key notation for a key event; null for keys the editor leaves to the browser. */
function keyName(event: KeyboardEvent): string | null {
  if (event.metaKey || event.altKey || event.isComposing) return null;
  if (event.ctrlKey) {
    if (event.key === "[") return "<Esc>";
    if (event.key === "^" || event.key === "6") return "<C-^>";
    return event.key.length === 1 ? `<C-${event.key.toLowerCase()}>` : null;
  }
  switch (event.key) {
    case "Escape":
      return "<Esc>";
    case "Enter":
      return "<CR>";
    case "Backspace":
      return "<BS>";
    case "Tab":
      return event.shiftKey ? "<S-Tab>" : "<Tab>";
    case "ArrowUp":
      return "<Up>";
    case "ArrowDown":
      return "<Down>";
    case "ArrowLeft":
      return "<Left>";
    case "ArrowRight":
      return "<Right>";
    case "Home":
      return "<Home>";
    case "End":
      return "<End>";
    case "PageUp":
      return "<PageUp>";
    case "PageDown":
      return "<PageDown>";
    case "Delete":
      return "<Del>";
    case " ":
      return "<Space>";
    default:
      return event.key.length === 1 ? event.key : null;
  }
}

let state: St | null = null;
let files: EditorFile[] = [];

/** Virtual text on screen this frame (`[copy]`), for clicks. */
let copyAt: CopyAt | null = null;

/**
 * Rows of cells in an element, one <div> each: a row is written only when its HTML changed, so a
 * key that moves the cursor rewrites a row or two, not the screen. The rows painted at build count
 * as painted.
 */
type Layer = { element: HTMLElement; painted: string[] };

function layer(selector: string): Layer {
  const box = element(selector, HTMLElement);
  return { element: box, painted: Array.from(box.children, (row) => row.innerHTML) };
}

function show(target: Layer, htmls: readonly string[]) {
  const { element: box } = target;
  while (box.children.length < htmls.length) box.append(document.createElement("div"));
  while (box.children.length > htmls.length) box.lastElementChild?.remove();
  htmls.forEach((html, r) => {
    const row = box.children[r];
    if (target.painted[r] !== html && row instanceof HTMLElement) row.innerHTML = html;
  });
  target.painted = [...htmls];
}

const gutter = layer("[data-gutter]");
const text = layer("[data-text]");
const floatLayer = layer("[data-float]");
const statusLeft = element("[data-status-l]", HTMLElement);
const statusRight = element("[data-status-r]", HTMLElement);
const cmdline = element("[data-cmd]", HTMLElement);
let blink: Animation | undefined;

/** The cell under the mouse, for Enter on a link. */
let mouse: { row: number; col: number } | null = null;

/** The frame on screen: what a click lands on. */
let shown: Frame | null = null;

/**
 * The link under screen cell (row, col), if one is there: its URL, and a screen column on the URL
 * (gf reads it there). A Markdown link is a target whole, `[label](url)`, the label as easy to hit
 * as the URL.
 */
function linkAt(row: number, col: number): { url: string; col: number } | null {
  if (shown === null || shown.float.$ === "Some" || shown.tgt.$ !== "File") return null;
  const g = shown.gutter;
  if (row >= size().rows - 2 || col < g) return null;
  const file = files[shown.tgt.i];
  const l = shown.top + row;
  const line = file?.lines[l];
  if (file === undefined || line === undefined) return null;
  const cps = cells(line);
  const c = shown.left + col - g;
  const run = (file.runs[l] ?? []).find((r) => {
    if (r.hl !== "link") return false;
    const labelled = cps[r.from - 1] === "(" && cps[r.from - 2] === "]";
    const from = labelled ? cps.lastIndexOf("[", r.from - 3) : r.from;
    return from >= 0 && from <= c && c <= (labelled ? r.to : r.to - 1);
  });
  if (run === undefined) return null;
  return {
    url: run.href ?? cps.slice(run.from, run.to).join(""),
    col: c >= run.from ? col : run.from - shown.left + g,
  };
}

function setVar(name: string, value: number) {
  const next = String(value);
  if (term.style.getPropertyValue(name) !== next) term.style.setProperty(name, next);
}

function paint(frame: Frame) {
  shown = frame;
  const { rows } = size();
  const tgt = frame.tgt;
  const dir = tgt.$ === "Dir" && state !== null ? list(Vim["Vim.lines"](state)) : [];
  const painted = textRows(frame, tgt.$ === "File" ? files[tgt.i] : undefined, dir, rows - 2);
  copyAt = painted.copyAt;
  setVar("--g", frame.gutter);
  show(gutter, gutterRows(frame));
  show(text, painted.htmls);
  Array.from(text.element.children).forEach((row, r) => {
    row.classList.toggle("cl", frame.cl && r === frame.cur.row);
  });
  const { left, right } = statusParts(frame.status);
  if (statusLeft.textContent !== left) statusLeft.textContent = left;
  if (statusRight.textContent !== right) statusRight.textContent = right;
  if (cmdline.textContent !== frame.cmd) cmdline.textContent = frame.cmd;
  show(floatLayer, floatRows(frame));
  if (frame.float.$ === "Some") {
    const float = frame.float.value;
    setVar("--frow", float.row);
    setVar("--fcol", float.col);
    setVar("--fw", float.width);
  }
  floatLayer.element.hidden = frame.float.$ === "None";
  setVar("--crow", frame.cur.row);
  setVar("--ccol", frame.cur.col);
  setVar("--bar-start", frame.bar.row);
  setVar("--bar-len", frame.float.$ === "Some" ? 0 : frame.bar.len);
  if (cursor.textContent !== frame.char) cursor.textContent = frame.char;
  // Each key shows the cursor at once: the blink starts over.
  blink ??= cursor.getAnimations()[0];
  if (blink !== undefined) blink.currentTime = 0;
}

/** Events in a row, painted once (a finger's scroll sends many). */
function steps(events: readonly Ev[]) {
  if (state === null || events.length === 0) return;
  for (const event of events) state = Vim["Vim.step"](state, event).st;
  paint(Vim["Vim.frame"](state));
}

/** Keys for a count and a command: 12 then <C-e>. */
function counted(n: number, keys: readonly string[]): Ev[] {
  const digits = n > 1 ? Array.from(String(n)) : [];
  return [...digits, ...keys].map((name): Ev => ({ $: "EvKey", name }));
}

function step(event: Ev) {
  if (state === null) return;
  const next = Vim["Vim.step"](state, event);
  state = next.st;
  const act = next.act;
  switch (act.$) {
    case "Nothing":
      break;
    case "OpenUrl":
      location.assign(act.url);
      break;
    case "CopyText":
      void navigator.clipboard.writeText(act.text);
      break;
    default: {
      const _: never = act;
      throw new Error(`unknown act ${JSON.stringify(_)}`);
    }
  }
  paint(Vim["Vim.frame"](state));
}

/** Where the window is: a file or an Oil folder. A tap that changes it is a step in history. */
function place(frame: Frame | null): string {
  if (frame === null) return "";
  return frame.tgt.$ === "File" ? `file ${frame.tgt.i}` : `dir ${frame.tgt.path}`;
}

/**
 * The editor's own history, in the browser's: each place a tap opens is an entry (same URL), so
 * the browser's back (a swipe from the edge, a key) goes back in the editor (Ctrl-o), forward goes
 * forward (Ctrl-i). `depth` is the entry on screen.
 */
let depth = 0;

/**
 * A click or a tap on a cell: [copy] copies, and the cursor goes there. A link to one of eukhe's
 * files (`spec/rlm/`, `LICENSE`) opens it in the editor (gf); any other opens as on a page. A finger
 * has no keyboard, so a tap also moves where a key would: on an Oil entry it opens it (Enter), on
 * the statusline it opens the folder above (-).
 */
function tap(row: number, col: number, finger: boolean) {
  if (copyAt !== null && row === copyAt.row && col >= copyAt.from && col < copyAt.to) {
    void navigator.clipboard.writeText(copyAt.text);
    return;
  }
  const from = place(shown);
  const link = linkAt(row, col);
  const { rows } = size();
  const free = finger && shown !== null && shown.float.$ === "None";
  if (free && row === rows - 2) step({ $: "EvKey", name: "-" });
  else {
    step({ $: "EvClick", row, col: link?.col ?? col });
    if (link !== null && /^([a-z][a-z0-9+.-]*:|\/|#)/i.test(link.url)) {
      // In this tab, as a page link: the browser's back (a swipe, a key) returns here.
      location.assign(link.url);
      return;
    }
    if (link !== null) {
      step({ $: "EvKey", name: "g" });
      step({ $: "EvKey", name: "f" });
    } else if (free && shown?.tgt.$ === "Dir" && state !== null && row < rows - 2) {
      const entry = list(Vim["Vim.lines"](state))[shown.top + row];
      if (entry !== undefined && entry !== "") step({ $: "EvKey", name: "<CR>" });
    }
  }
  if (place(shown) !== from) {
    depth += 1;
    history.pushState({ eukhe: depth }, "");
  }
}

/** The cell under a pointer event. */
function cellAt(event: MouseEvent): { row: number; col: number } {
  return {
    row: Math.max(0, Math.floor((event.clientY - pad) / lh)),
    col: Math.max(0, Math.floor((event.clientX - pad) / cw)),
  };
}

/**
 * The editor starts at the first input (a key, a click, a touch, the wheel), not at load: the page
 * already shows its first screen, and loading stays free of long tasks. The files come over the
 * network meanwhile; inputs made while the editor starts run once it has.
 */
let filesText: Promise<string> | null = null;
let booting: Promise<void> | null = null;

async function start() {
  if (filesText === null) throw new Error("the editor starts before it listens");
  // This page's file first: the editor opens on it, as the page's first screen shows.
  const page = document.documentElement.dataset.page ?? "index.md";
  const all = await loadFiles(filesText);
  files = [
    ...all.filter((file) => file.path === page),
    ...all.filter((file) => file.path !== page),
  ];
  const { rows, cols } = size();
  const bufs = cons(
    files.map((file): Buf => ({ $: "Buf", path: file.path, lines: cons(file.lines) })),
  );
  state = Vim["Vim.init"](bufs, rows, cols);
  paint(Vim["Vim.frame"](state));
}

/** Runs fn with the editor started: now, or once it has. */
function ready(fn: () => void) {
  if (state !== null) {
    fn();
    return;
  }
  booting ??= start();
  booting.then(fn, (error: unknown) => console.error("eukhe editor:", error));
}

function listen() {
  measure();
  history.replaceState({ eukhe: depth }, "");
  window.addEventListener("popstate", (event) => {
    const entry: unknown = event.state;
    const to = typeof entry === "object" && entry !== null && "eukhe" in entry ? entry.eukhe : null;
    if (typeof to !== "number") return;
    const moves = to - depth;
    depth = to;
    if (moves !== 0)
      ready(() =>
        steps(
          Array.from({ length: Math.abs(moves) }, (): Ev => ({
            $: "EvKey",
            name: moves < 0 ? "<C-o>" : "<C-i>",
          })),
        ),
      );
  });
  filesText = fetch("/files.json").then((response) => {
    if (!response.ok) throw new Error(`/files.json: ${response.status}`);
    return response.text();
  });
  // Until the first input reads it; a failure is reported then.
  filesText.catch(() => undefined);
  document.addEventListener("keydown", (event) => {
    const name = keyName(event);
    if (name === null) return;
    event.preventDefault();
    // Enter with the mouse on a link opens it, in normal mode (no picker, no command line). The
    // editor may still be starting: the link is read once it has.
    ready(() => {
      const typing = shown !== null && shown.cur.row >= size().rows - 2;
      const at = mouse;
      if (name === "<CR>" && at !== null && !typing && linkAt(at.row, at.col) !== null)
        tap(at.row, at.col, false);
      else step({ $: "EvKey", name });
    });
  });
  term.addEventListener("mousedown", (event) => {
    if (event.button !== 0) return;
    event.preventDefault();
    const { row, col } = cellAt(event);
    ready(() => tap(row, col, false));
  });
  term.addEventListener("mouseleave", () => {
    mouse = null;
  });
  term.addEventListener("mousemove", (event) => {
    const { row, col } = cellAt(event);
    mouse = { row, col };
    const over =
      linkAt(row, col) !== null ||
      (copyAt !== null && row === copyAt.row && col >= copyAt.from && col < copyAt.to);
    term.style.cursor = over ? "pointer" : "";
  });
  // A notch is about 100px of wheel; a trackpad sends many small moves, summed until they make one.
  // Sideways, a column a cell. A gesture that starts to the left with the view already at its first
  // column is the browser's (a trackpad swipe back a page), to its end and momentum.
  let wheel = 0;
  let wheelX = 0;
  let wheelLast = Number.NEGATIVE_INFINITY;
  let wheelOwner: "page" | "browser" = "page";
  term.addEventListener(
    "wheel",
    (event) => {
      const unit = event.deltaMode === WheelEvent.DOM_DELTA_LINE ? 33 : 1;
      const dx = event.deltaX * unit;
      const dy = event.deltaY * unit;
      const sideways = Math.abs(dx) > Math.abs(dy);
      if (event.timeStamp - wheelLast > 150) {
        const atLeft = shown === null || shown.left === 0;
        wheelOwner = atLeft && dx < 0 && -dx >= Math.abs(dy) ? "browser" : "page";
      }
      wheelLast = event.timeStamp;
      if (wheelOwner === "browser") return;
      event.preventDefault();
      if (sideways) {
        wheelX += dx;
        const cols = Math.trunc(wheelX / cw);
        wheelX -= cols * cw;
        scrollCols(cols);
        return;
      }
      wheel += dy;
      const notches = Math.trunc(wheel / 100);
      if (notches === 0) return;
      wheel -= notches * 100;
      ready(() => step({ $: "EvWheel", down: notches > 0, notches: Math.abs(notches) }));
    },
    { passive: false },
  );
  if (touch) touchScroll();
  window.addEventListener("resize", () => {
    const next = size();
    step({ $: "EvSize", rows: next.rows, cols: next.cols });
  });
}

// The page's [copy] button (phones, or before the editor starts): copies the install command.
document.addEventListener("click", (event) => {
  const button = event.target instanceof Element ? event.target.closest("[data-copy]") : null;
  if (!(button instanceof HTMLElement)) return;
  const command = button.dataset.copy;
  if (command === undefined) return;
  void navigator.clipboard.writeText(command).then(() => {
    button.textContent = "[copied]";
    setTimeout(() => {
      button.textContent = "[copy]";
    }, 1500);
  });
});

/** The text n rows up (down when negative), the cursor dragged: Ctrl-e, Ctrl-y. */
function scrollRows(n: number) {
  if (n !== 0) ready(() => steps(counted(Math.abs(n), [n > 0 ? "<C-e>" : "<C-y>"])));
}

/** The view n columns right (left when negative): zl, zh. */
function scrollCols(n: number) {
  if (n !== 0) ready(() => steps(counted(Math.abs(n), ["z", n > 0 ? "l" : "h"])));
}

/** The font size a pinch may reach, in px: the cell is 0.6 of it, the line its leading. */
const fontMin = 7;
const fontMax = 28;

/**
 * The font at `px`, as a terminal app over SSH zooms: the cells shrink or grow with it and the
 * screen holds more or fewer of them (`EvSize`). Half-pixel steps; whole-pixel lines.
 */
function zoom(px: number, leading: number) {
  const font = Math.min(fontMax, Math.max(fontMin, Math.round(px * 2) / 2));
  if (`${font}px` === term.style.getPropertyValue("--fs")) return;
  term.style.setProperty("--fs", `${font}px`);
  term.style.setProperty("--cw", `${font * 0.6}px`);
  term.style.setProperty("--lh", `${Math.round(font * leading)}px`);
  measure();
  const next = size();
  ready(() => step({ $: "EvSize", rows: next.rows, cols: next.cols }));
}

/** The distance between the first two fingers; null with fewer. */
function spread(touches: TouchList): number | null {
  const a = touches[0];
  const b = touches[1];
  return a === undefined || b === undefined
    ? null
    : Math.hypot(a.clientX - b.clientX, a.clientY - b.clientY);
}

/**
 * A finger, as in a terminal over SSH on a phone: a drag scrolls the text with it (a line a row,
 * Ctrl-e and Ctrl-y; a column a cell, zl and zh), a flick keeps it going and slows down, a tap
 * puts the cursor there or opens what is under it, two fingers pinch the font smaller or larger.
 * No keyboard comes up. A drag from the screen's left edge, or to the right with the view at its
 * first column, is the browser's: back a step.
 */
function touchScroll() {
  let x = 0;
  let y = 0;
  let startX = 0;
  let startY = 0;
  let axis: "none" | "x" | "y" | "browser" = "none";
  // A drag that began before the editor listened has no start: it is left to finish untouched.
  let dragging = false;
  let rows = 0;
  let cols = 0;
  let speed = 0;
  let last = 0;
  let fling = 0;
  // Two fingers: their distance and the font at the pinch's start, and the font's line ratio.
  let pinch: { distance: number; font: number; leading: number } | null = null;
  term.addEventListener(
    "touchstart",
    (event) => {
      const t = event.touches[0];
      if (t === undefined) return;
      cancelAnimationFrame(fling);
      // The editor starts at the touch, not at the first move: a drag scrolls from its start.
      ready(() => undefined);
      const distance = spread(event.touches);
      if (distance !== null) {
        // A second finger: a pinch, never a drag or a tap.
        dragging = false;
        const font = Number.parseFloat(getComputedStyle(term).getPropertyValue("--fs"));
        if (distance > 0 && font > 0) pinch = { distance, font, leading: lh / font };
        return;
      }
      x = startX = t.clientX;
      y = startY = t.clientY;
      axis = "none";
      dragging = true;
      rows = 0;
      cols = 0;
      speed = 0;
      last = event.timeStamp;
    },
    { passive: true },
  );
  term.addEventListener(
    "touchmove",
    (event) => {
      if (pinch !== null) {
        event.preventDefault();
        const distance = spread(event.touches);
        if (distance !== null) zoom((pinch.font * distance) / pinch.distance, pinch.leading);
        return;
      }
      const t = event.touches[0];
      if (t === undefined || !dragging || axis === "browser") return;
      if (axis === "none") {
        const dx = t.clientX - startX;
        const dy = t.clientY - startY;
        if (Math.hypot(dx, dy) > 8) {
          const atLeft = shown === null || shown.left === 0;
          if (startX < 24 || (atLeft && dx > 0 && dx >= Math.abs(dy))) {
            axis = "browser";
            return;
          }
          axis = Math.abs(dx) > Math.abs(dy) ? "x" : "y";
        }
      }
      event.preventDefault();
      const dt = Math.max(1, event.timeStamp - last);
      if (axis === "y") {
        speed = (y - t.clientY) / dt;
        const total = Math.trunc((startY - t.clientY) / lh);
        scrollRows(total - rows);
        rows = total;
      } else if (axis === "x") {
        speed = (x - t.clientX) / dt;
        const total = Math.trunc((startX - t.clientX) / cw);
        scrollCols(total - cols);
        cols = total;
      }
      x = t.clientX;
      y = t.clientY;
      last = event.timeStamp;
    },
    { passive: false },
  );
  const lift = (event: TouchEvent) => {
    if (pinch !== null && event.touches.length < 2) pinch = null;
  };
  term.addEventListener("touchcancel", lift);
  term.addEventListener("touchend", (event) => {
    lift(event);
    if (!dragging) return;
    dragging = false;
    if (axis === "none") {
      event.preventDefault();
      const row = Math.max(0, Math.floor((y - pad) / lh));
      const col = Math.max(0, Math.floor((x - pad) / cw));
      ready(() => tap(row, col, true));
      return;
    }
    if (Math.abs(speed) < 0.3) return;
    // A flick: the text keeps going along the drag's axis, slowing down by 5% a frame.
    const cell = axis === "y" ? lh : cw;
    const move = axis === "y" ? scrollRows : scrollCols;
    let carry = 0;
    let then = performance.now();
    const frame = (now: number) => {
      carry += (speed * (now - then)) / cell;
      then = now;
      speed *= 0.95;
      const whole = Math.trunc(carry);
      carry -= whole;
      move(whole);
      if (Math.abs(speed) > 0.02) fling = requestAnimationFrame(frame);
    };
    fling = requestAnimationFrame(frame);
  });
}

// The page shows the terminal (html[data-vim]) unless it has no script; the 404 page stays plain.
if (document.documentElement.hasAttribute("data-vim")) listen();
