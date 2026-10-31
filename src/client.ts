/**
 * The terminal the Bend editor (vim/vim.bend) runs in. It decides nothing: it turns browser events
 * into `Ev`s for `Vim.step`, runs the `Act` it gets back (open a URL, copy the install command), and
 * paints `Vim.frame` as a grid of rows x cols cells over the whole window, as a terminal does.
 * Screens without a fine pointer or narrower than 720px keep the page.
 */
import type { EditorFile, Run } from "./markdown.tsx";
import Vim, { type BendList, type Buf, type Ev, type Frame, type Mark, type St } from "./vim.mjs";

/** A touch screen (a phone): no keyboard, a smaller font, the finger scrolls. */
const touch = window.matchMedia("(pointer: coarse)").matches;

function element<T extends Element>(selector: string, type: new () => T): T {
  const found = document.querySelector(selector);
  if (!(found instanceof type)) throw new Error(`${selector} is missing`);
  return found;
}

function list<T>(items: BendList<T>): T[] {
  const out: T[] = [];
  for (let cell = items; cell.$ === "Con"; cell = cell.tail) out.push(cell.head);
  return out;
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

async function loadFiles(): Promise<EditorFile[]> {
  const response = await fetch("/files.json");
  if (!response.ok) throw new Error(`/files.json: ${response.status}`);
  const data: unknown = await response.json();
  if (!Array.isArray(data) || !data.every(isEditorFile))
    throw new Error("/files.json is malformed");
  return data;
}

const term = element("[data-term]", HTMLElement);
const cursor = element("[data-cursor]", HTMLElement);

/** Ghostty's window padding. */
const pad = 2;
/** A cell: one character of the font wide, the font's line high; measured once the font is in. */
let cw = 9;
let lh = 18;

/** Ghostty's 15px on a desktop; 13px on a phone, where every column counts. */
const fontSize = touch ? 13 : 15;

function measure() {
  const probe = document.createElement("span");
  probe.style.cssText = `position:absolute;visibility:hidden;white-space:pre;font-size:${fontSize}px;line-height:normal`;
  probe.textContent = "0".repeat(100);
  document.body.append(probe);
  const box = probe.getBoundingClientRect();
  probe.remove();
  if (!(box.width > 0 && box.height > 0)) throw new Error(`cell ${box.width}x${box.height}`);
  cw = box.width / 100;
  lh = Math.ceil(box.height);
  term.style.setProperty("--fs", `${fontSize}px`);
  term.style.setProperty("--cw", `${cw}px`);
  term.style.setProperty("--lh", `${lh}px`);
  term.style.setProperty("--ox", `${pad}px`);
  term.style.setProperty("--oy", `${pad}px`);
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

/** The goose of fff's prompt: two cells wide. */
const goose = "\u{1FABF}";

let state: St | null = null;
let files: EditorFile[] = [];
/** Each file's lines as code points (one per cell), split when first shown. */
const points = new Map<string, string[]>();
/** Each file's inks column: two cells right of its longest line. */
const inkCol = new Map<number, number>();

function cells(text: string): string[] {
  let found = points.get(text);
  if (found === undefined) {
    found = Array.from(text);
    points.set(text, found);
  }
  return found;
}

/** Virtual text on screen this frame (`[copy]`), for clicks. */
let copyAt: { row: number; from: number; to: number; text: string } | null = null;

/** One row being built: a character, a class list and a color ("": the class's) per cell. */
type Row = { chars: string[]; classes: string[]; colors: string[] };

function blankRow(width: number): Row {
  const blank = () => Array<string>(width).fill("");
  return { chars: Array<string>(width).fill(" "), classes: blank(), colors: blank() };
}

function put(row: Row, col: number, text: string, cls: string) {
  let at = col;
  for (const ch of cells(text)) {
    if (at >= row.chars.length) return;
    if (at >= 0) {
      row.chars[at] = ch;
      row.classes[at] = cls;
    }
    if (ch === goose) {
      at += 1;
      if (at >= 0 && at < row.chars.length) {
        row.chars[at] = "";
        row.classes[at] = cls;
      }
    }
    at += 1;
  }
}

function addClass(row: Row, from: number, to: number, cls: string) {
  for (let col = Math.max(0, from); col < Math.min(to, row.classes.length); col += 1) {
    const current = row.classes[col];
    row.classes[col] = current === undefined || current === "" ? cls : `${current} ${cls}`;
  }
}

/** A run's highlight: a group's class, or a color of its own (a swatch in the COLORS table). */
function paintRun(row: Row, from: number, to: number, run: Run) {
  if (typeof run.hl === "string") {
    addClass(row, from, to, run.hl);
    return;
  }
  for (let col = Math.max(0, from); col < Math.min(to, row.colors.length); col += 1)
    row.colors[col] = run.hl.color;
}

function markClass(mark: Mark): string {
  switch (mark.group.$) {
    case "Border":
      return "bd";
    case "Title":
      return "ti";
    case "Sel":
      return "sel";
    case "Match":
      return "match";
    case "Dim":
      return "dim";
    case "Prompt":
      return "prompt";
    case "Count":
      return "count";
    case "Number":
      return "nr";
    case "Thumb":
      return "thumb";
    default: {
      const _: never = mark.group;
      throw new Error(`unknown mark ${JSON.stringify(_)}`);
    }
  }
}

function escape(text: string): string {
  return text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
}

/** A span's attributes: its class list and its own color, if any. */
function attrs(cls: string, color: string): string {
  return `${cls === "" ? "" : ` class="${cls}"`}${color === "" ? "" : ` style="color:${color}"`}`;
}

/** A row's cells as runs of one class and color each. */
function rowHtml(row: Row): string {
  let html = "";
  let run = "";
  let cls = "";
  let color = "";
  const flush = () => {
    if (run === "") return;
    html +=
      cls === "" && color === "" ? escape(run) : `<span${attrs(cls, color)}>${escape(run)}</span>`;
    run = "";
  };
  for (let col = 0; col < row.chars.length; col += 1) {
    const ch = row.chars[col] ?? " ";
    const c = row.classes[col] ?? "";
    const k = row.colors[col] ?? "";
    if (ch === goose) {
      flush();
      html += `<span${attrs(`w2 ${c}`, k)}>${ch}</span>`;
      continue;
    }
    if (c !== cls || k !== color) {
      flush();
      cls = c;
      color = k;
    }
    run += ch;
  }
  flush();
  return html;
}

/**
 * Rows of cells in an element, one <div> each: a row is written only when its HTML changed, so a
 * key that moves the cursor rewrites a row or two, not the screen.
 */
type Layer = { element: HTMLElement; painted: string[] };

function layer(selector: string): Layer {
  return { element: element(selector, HTMLElement), painted: [] };
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

const gutter = element("[data-gutter]", HTMLElement);
const text = layer("[data-text]");
const floatLayer = layer("[data-float]");
const status = element("[data-status]", HTMLElement);
const cmdline = element("[data-cmd]", HTMLElement);
let gutterHtml = "";
let blink: Animation | undefined;

/** The text rows: the window's lines from `left`, with highlights, search hits and virtual text. */
function textRows(frame: Frame, h: number, w: number): string[] {
  if (state === null) return [];
  const tgt = frame.tgt;
  const file = tgt.$ === "File" ? files[tgt.i] : undefined;
  const dirLines = tgt.$ === "Dir" ? list(Vim["Vim.lines"](state)) : [];
  const hits = list(frame.hits);
  const g = frame.gutter;
  copyAt = null;
  const htmls: string[] = [];
  for (let r = 0; r < h; r += 1) {
    const row = blankRow(w);
    const l = frame.top + r;
    if (file !== undefined && tgt.$ === "File") {
      const line = file.lines[l];
      if (line !== undefined) {
        const cps = cells(line);
        for (let c = 0; c < w; c += 1) {
          const ch = cps[frame.left + c];
          if (ch === undefined) break;
          row.chars[c] = ch;
        }
        for (const run of file.runs[l] ?? [])
          paintRun(row, run.from - frame.left, run.to - frame.left, run);
        // Virtual text: the inks of the page, and `[copy]` after the install fence.
        const inks = file.inks?.[l];
        const ink = inkCol.get(tgt.i);
        if (inks !== undefined && ink !== undefined) {
          let at = ink - frame.left;
          for (const token of inks) {
            put(row, at, token, `ink-${token}`);
            at += token.length + 1;
          }
        }
        const command = file.lines[l + 1];
        if (file.copy === l && command !== undefined) {
          const at = cps.length + 2 - frame.left;
          if (at >= 0 && at + 6 <= w) {
            put(row, at, "[copy]", "copy");
            copyAt = { row: r, from: g + at, to: g + at + 6, text: command };
          }
        }
      }
    } else {
      const line = dirLines[l];
      if (line !== undefined) put(row, -frame.left, line, line.endsWith("/") ? "title" : "");
    }
    for (const hit of hits)
      if (hit.row === r) addClass(row, hit.col - g, hit.col - g + hit.len, "hit");
    htmls.push(rowHtml(row));
  }
  return htmls;
}

function floatRows(frame: Frame): string[] {
  if (frame.float.$ === "None") return [];
  const float = frame.float.value;
  const rows = list(float.lines).map((line) => {
    const row = blankRow(float.width);
    put(row, 0, line, "");
    return row;
  });
  for (const mark of list(float.marks)) {
    const row = rows[mark.row];
    if (row !== undefined) addClass(row, mark.col, mark.col + mark.len, markClass(mark));
  }
  return rows.map(rowHtml);
}

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

function paint(frame: Frame) {
  shown = frame;
  const { rows, cols } = size();
  const h = rows - 2;
  const g = frame.gutter;
  const style = term.style;
  style.setProperty("--cols", String(cols));
  style.setProperty("--h", String(h));
  style.setProperty("--g", String(g));
  // The number column: one write for all rows, the cursor's number in its own color.
  const nums = list(frame.nums).map((num, r) =>
    r === frame.cur.row && frame.cl ? `<span class="cnr">${escape(num)}</span>` : escape(num),
  );
  const nextGutter = nums.join("\n");
  if (nextGutter !== gutterHtml) {
    gutter.innerHTML = nextGutter;
    gutterHtml = nextGutter;
  }
  show(text, textRows(frame, h, cols - g));
  Array.from(text.element.children).forEach((row, r) => {
    row.classList.toggle("cl", frame.cl && r === frame.cur.row);
  });
  if (status.textContent !== frame.status) status.textContent = frame.status;
  if (cmdline.textContent !== frame.cmd) cmdline.textContent = frame.cmd;
  show(floatLayer, floatRows(frame));
  if (frame.float.$ === "Some") {
    const float = frame.float.value;
    style.setProperty("--frow", String(float.row));
    style.setProperty("--fcol", String(float.col));
    style.setProperty("--fw", String(float.width));
  }
  floatLayer.element.hidden = frame.float.$ === "None";
  style.setProperty("--crow", String(frame.cur.row));
  style.setProperty("--ccol", String(frame.cur.col));
  style.setProperty("--bar-start", String(frame.bar.row));
  style.setProperty("--bar-len", String(frame.float.$ === "Some" ? 0 : frame.bar.len));
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
  if (url !== null) window.open(url, "_blank", "noopener");
}

/** The cell under a pointer event. */
function cellAt(event: MouseEvent): { row: number; col: number } {
  return {
    row: Math.max(0, Math.floor((event.clientY - pad) / lh)),
    col: Math.max(0, Math.floor((event.clientX - pad) / cw)),
  };
}

async function start() {
  await document.fonts.ready;
  files = await loadFiles();
  files.forEach((file, i) => {
    if (file.inks !== null)
      inkCol.set(i, Math.max(68, ...file.lines.map((line) => cells(line).length)) + 2);
  });
  measure();
  const { rows, cols } = size();
  const bufs = cons(
    files.map((file): Buf => ({ $: "Buf", path: file.path, lines: cons(file.lines) })),
  );
  state = Vim["Vim.init"](bufs, rows, cols);
  // The page goes only once the first screen is painted.
  paint(Vim["Vim.frame"](state));
  document.documentElement.toggleAttribute("data-vim", true);

  document.addEventListener("keydown", (event) => {
    const name = keyName(event);
    if (name === null) return;
    event.preventDefault();
    step({ $: "EvKey", name });
  });
  term.addEventListener("mousedown", (event) => {
    if (event.button !== 0) return;
    event.preventDefault();
    const { row, col } = cellAt(event);
    tap(row, col);
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
      step({ $: "EvWheel", down: notches > 0, notches: Math.abs(notches) });
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
  if (n !== 0) steps(counted(Math.abs(n), [n > 0 ? "<C-e>" : "<C-y>"]));
}

/** The view n columns right (left when negative): zl, zh. */
function scrollCols(n: number) {
  if (n !== 0) steps(counted(Math.abs(n), ["z", n > 0 ? "l" : "h"]));
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
      tap(row, col);
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

// Anything that stops the editor from starting leaves the page as it is, and says why.
start().catch((error: unknown) => console.error("eukhe editor:", error));
