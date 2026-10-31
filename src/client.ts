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
  if (!("hl" in value)) return false;
  const hl: unknown = value.hl;
  if (typeof hl === "string") return ["title", "muted", "heading", "link"].includes(hl);
  return typeof hl === "object" && hl !== null && "color" in hl && typeof hl.color === "string";
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
  if (!("copy" in value) || !(value.copy === null || typeof value.copy === "number")) return false;
  if (!("inks" in value)) return false;
  const inks: unknown = value.inks;
  return inks === null || (Array.isArray(inks) && inks.every(isStrings));
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

/** The frame on screen: what a click lands on. */
let shown: Frame | null = null;

/** The URL of the link under screen cell (row, col), if one is there. */
function linkAt(row: number, col: number): string | null {
  if (shown === null || shown.float.$ === "Some" || shown.tgt.$ !== "File") return null;
  const g = shown.gutter;
  if (row >= size().rows - 2 || col < g) return null;
  const file = files[shown.tgt.i];
  const l = shown.top + row;
  const line = file?.lines[l];
  if (file === undefined || line === undefined) return null;
  const c = shown.left + col - g;
  const run = (file.runs[l] ?? []).find((r) => r.hl === "link" && r.from <= c && c < r.to);
  return run === undefined ? null : cells(line).slice(run.from, run.to).join("");
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
      window.open(act.url, "_blank", "noopener");
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

/** A click or a tap on a cell: [copy] copies, a link opens as on a page, and the cursor goes there. */
function tap(row: number, col: number) {
  if (copyAt !== null && row === copyAt.row && col >= copyAt.from && col < copyAt.to) {
    void navigator.clipboard.writeText(copyAt.text);
    return;
  }
  const url = linkAt(row, col);
  step({ $: "EvClick", row, col });
  if (url === null) return;
  // eukhe.com's own pages open here, as terminals too; other sites in a new tab.
  if (new URL(url, location.href).origin === location.origin) location.assign(url);
  else window.open(url, "_blank", "noopener");
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
    ready(() => step({ $: "EvKey", name }));
  });
  term.addEventListener("mousedown", (event) => {
    if (event.button !== 0) return;
    event.preventDefault();
    const { row, col } = cellAt(event);
    ready(() => tap(row, col));
  });
  term.addEventListener("mousemove", (event) => {
    const { row, col } = cellAt(event);
    const over =
      linkAt(row, col) !== null ||
      (copyAt !== null && row === copyAt.row && col >= copyAt.from && col < copyAt.to);
    term.style.cursor = over ? "pointer" : "";
  });
  // A notch is about 100px of wheel; a trackpad sends many small moves, summed until they make one.
  let wheel = 0;
  term.addEventListener(
    "wheel",
    (event) => {
      event.preventDefault();
      wheel += event.deltaMode === WheelEvent.DOM_DELTA_LINE ? event.deltaY * 33 : event.deltaY;
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

/**
 * A finger, as in a terminal over SSH on a phone: a drag scrolls the text with it (a line a row,
 * Ctrl-e and Ctrl-y; a column a cell, zl and zh), a flick keeps it going and slows down, a tap
 * puts the cursor there or opens the link under it. No keyboard comes up.
 */
function touchScroll() {
  let x = 0;
  let y = 0;
  let startX = 0;
  let startY = 0;
  let axis: "none" | "x" | "y" = "none";
  let rows = 0;
  let cols = 0;
  let speed = 0;
  let last = 0;
  let fling = 0;
  term.addEventListener(
    "touchstart",
    (event) => {
      const t = event.touches[0];
      if (t === undefined) return;
      cancelAnimationFrame(fling);
      x = startX = t.clientX;
      y = startY = t.clientY;
      axis = "none";
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
      event.preventDefault();
      const t = event.touches[0];
      if (t === undefined) return;
      if (axis === "none" && Math.hypot(t.clientX - startX, t.clientY - startY) > 8)
        axis = Math.abs(t.clientX - startX) > Math.abs(t.clientY - startY) ? "x" : "y";
      const dt = Math.max(1, event.timeStamp - last);
      if (axis === "y") {
        speed = (y - t.clientY) / dt;
        const total = Math.trunc((startY - t.clientY) / lh);
        scrollRows(total - rows);
        rows = total;
      } else if (axis === "x") {
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
  term.addEventListener("touchend", (event) => {
    if (axis === "none") {
      event.preventDefault();
      const row = Math.max(0, Math.floor((y - pad) / lh));
      const col = Math.max(0, Math.floor((x - pad) / cw));
      ready(() => tap(row, col));
      return;
    }
    if (axis !== "y" || Math.abs(speed) < 0.3) return;
    // A flick: the text keeps going, slowing down by 5% a frame.
    let carry = 0;
    let then = performance.now();
    const frame = (now: number) => {
      carry += (speed * (now - then)) / lh;
      then = now;
      speed *= 0.95;
      const whole = Math.trunc(carry);
      carry -= whole;
      scrollRows(whole);
      if (Math.abs(speed) > 0.02) fling = requestAnimationFrame(frame);
    };
    fling = requestAnimationFrame(frame);
  });
}

// The page shows the terminal (html[data-vim]) unless it has no script; the 404 page stays plain.
if (document.documentElement.hasAttribute("data-vim")) listen();
