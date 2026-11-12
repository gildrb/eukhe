// Renders the Bend core's screens as text, cell for cell, the way a terminal shows Neovim: the
// text rows (number column, then the buffer's lines from the window's first column), the
// statusline, the command line, then the float on top. A cell holds one character; the goose of
// fff's prompt (U+1FABF) takes two, and the second is "" (as pyte's screen shows it).
//
// As a module: `screen(st, rows, cols)` and `run(files, rows, cols, keys)`. As a script, it reads
// a JSON job on stdin: {files: [{path, lines}], rows, cols, scenarios: [{name, keys: [key]}]}
// and prints {name: {lines, cur: [row, col], ms: [per-key step+frame ms, warm]}} as JSON.
import fs from "node:fs";
import { fileURLToPath } from "node:url";
import Vim from "../src/vim.mjs";

export const list = (v) => {
  const out = [];
  while (v.$ === "Con") {
    out.push(v.head);
    v = v.tail;
  }
  return out;
};

export const cons = (xs) =>
  xs.reduceRight((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });

const wide = (ch) => ch === "\u{1FABF}";

/** The cells of s: a wide character's second cell is "". */
export const cellsOf = (s) => {
  const out = [];
  for (const ch of s) {
    out.push(ch);
    if (wide(ch)) out.push("");
  }
  return out;
};

/** Writes s into row from cell col on, within cols. */
const put = (row, col, s, cols) => {
  let x = col;
  for (const c of cellsOf(s)) {
    if (x >= cols) break;
    row[x] = c;
    x += 1;
  }
};

/** The screen of editor st: rows strings (wide cells collapsed) and the cursor. */
export function screen(st, rows, cols) {
  const f = Vim["Vim.frame"](st);
  const lines = list(Vim["Vim.lines"](st));
  const nums = list(f.nums);
  const grid = Array.from({ length: rows }, () => Array(cols).fill(" "));
  const h = rows - 2;
  for (let r = 0; r < h; r++) {
    const num = nums[r] ?? "";
    put(grid[r], 0, num, cols);
    const line = lines[f.top + r];
    if (line !== undefined) {
      const text = cellsOf(line).slice(f.left).join("");
      put(grid[r], f.gutter, text, cols);
    }
  }
  put(grid[rows - 2], 0, f.status, cols);
  put(grid[rows - 1], 0, f.cmd, cols);
  if (f.float.$ === "Some") {
    const fl = f.float.value;
    list(fl.lines).forEach((s, i) => put(grid[fl.row + i], fl.col, s, cols));
  }
  return {
    lines: grid.map((row) => row.join("")),
    cur: [f.cur.row, f.cur.col],
    frame: f,
  };
}

/** The editor over files after keys, with each key's step+frame time. */
export function run(files, rows, cols, keys) {
  const bufs = cons(files.map((file) => ({ $: "Buf", path: file.path, lines: cons(file.lines) })));
  let st = Vim["Vim.init"](bufs, rows, cols);
  const ms = [];
  for (const name of keys) {
    const t0 = performance.now();
    st = Vim["Vim.step"](st, { $: "EvKey", name }).st;
    Vim["Vim.frame"](st);
    ms.push(performance.now() - t0);
  }
  return { st, ms };
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const job = JSON.parse(fs.readFileSync(0, "utf8"));
  const out = {};
  for (const sc of job.scenarios) {
    // the first run warms the JIT up; the times are the second run's
    run(job.files, job.rows, job.cols, sc.keys);
    const { st, ms } = run(job.files, job.rows, job.cols, sc.keys);
    const { lines, cur } = screen(st, job.rows, job.cols);
    out[sc.name] = { lines, cur, ms };
  }
  process.stdout.write(JSON.stringify(out));
}
