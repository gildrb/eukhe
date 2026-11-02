/**
 * Frame to HTML, shared by the build (render.tsx paints the first screen into the page) and the
 * browser (client.ts paints every later one). A row's HTML never depends on the screen's width:
 * lines run past the right edge and are clipped by CSS, so the first screen painted at build is
 * the one the browser would paint, on any screen.
 */
import type { EditorFile } from "./markdown.tsx";
import type { BendList, Frame, Mark } from "./vim.mjs";

export function list<T>(items: BendList<T>): T[] {
  const out: T[] = [];
  for (let cell = items; cell.$ === "Con"; cell = cell.tail) out.push(cell.head);
  return out;
}

/** The goose of fff's prompt: two cells wide. */
const goose = "\u{1FABF}";

/** A line as code points (one per cell), split once. */
const points = new Map<string, string[]>();

export function cells(text: string): string[] {
  let found = points.get(text);
  if (found === undefined) {
    found = Array.from(text);
    points.set(text, found);
  }
  return found;
}

/** One row being built: a character and a class list per cell. */
type Row = { chars: string[]; classes: string[] };

function blankRow(width: number): Row {
  return { chars: Array<string>(width).fill(" "), classes: Array<string>(width).fill("") };
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

export function escape(text: string): string {
  return text.replaceAll("&", "&amp;").replaceAll("<", "&lt;").replaceAll(">", "&gt;");
}

/** A span's attributes: its class list, if any. */
function attrs(cls: string): string {
  return cls === "" ? "" : ` class="${cls}"`;
}

/** A row's cells as runs of one class each; trailing plain blanks dropped. */
function rowHtml(row: Row): string {
  let end = row.chars.length;
  while (end > 0 && row.chars[end - 1] === " " && row.classes[end - 1] === "") end -= 1;
  let html = "";
  let run = "";
  let cls = "";
  const flush = () => {
    if (run === "") return;
    html += cls === "" ? escape(run) : `<span${attrs(cls)}>${escape(run)}</span>`;
    run = "";
  };
  for (let col = 0; col < end; col += 1) {
    const ch = row.chars[col] ?? " ";
    const c = row.classes[col] ?? "";
    if (ch === goose) {
      flush();
      html += `<span${attrs(`w2 ${c}`)}>${ch}</span>`;
      continue;
    }
    if (c !== cls) {
      flush();
      cls = c;
    }
    run += ch;
  }
  flush();
  return html;
}

/** `[copy]` on screen: its row and cells, and what it copies. */
export type CopyAt = { row: number; from: number; to: number; text: string };

/**
 * The h text rows: the window's lines from `left`, with highlights, search hits and virtual text
 * (`[copy]` after the install fence). `dir` holds an Oil listing's lines.
 */
export function textRows(
  frame: Frame,
  file: EditorFile | undefined,
  dir: readonly string[],
  h: number,
): { htmls: string[]; copyAt: CopyAt | null } {
  const hits = list(frame.hits);
  const g = frame.gutter;
  const left = frame.left;
  let copyAt: CopyAt | null = null;
  const htmls: string[] = [];
  for (let r = 0; r < h; r += 1) {
    const l = frame.top + r;
    let row = blankRow(0);
    if (file !== undefined) {
      const line = file.lines[l];
      if (line !== undefined) {
        const cps = cells(line);
        const command = file.lines[l + 1];
        const copy = file.copy === l && command !== undefined;
        row = blankRow(Math.max(0, cps.length + (copy ? 8 : 0) - left));
        for (let c = 0; c < row.chars.length; c += 1) {
          const ch = cps[left + c];
          if (ch === undefined) break;
          row.chars[c] = ch;
        }
        for (const run of file.runs[l] ?? []) addClass(row, run.from - left, run.to - left, run.hl);
        if (copy) {
          const at = cps.length + 2 - left;
          if (at >= 0) {
            put(row, at, "[copy]", "copy");
            // The command alone, its trailing `# comment` dropped.
            const text = command.replace(/(^|\s)#\s.*$/, "").trimEnd();
            copyAt = { row: r, from: g + at, to: g + at + 6, text };
          }
        }
      }
    } else {
      const line = dir[l];
      if (line !== undefined) {
        row = blankRow(Math.max(0, cells(line).length - left));
        put(row, -left, line, line.endsWith("/") ? "title" : "");
      }
    }
    const mine = hits.filter((hit) => hit.row === r);
    const hitEnd = Math.max(0, ...mine.map((hit) => hit.col - g + hit.len));
    if (hitEnd > row.chars.length) {
      const wider = blankRow(hitEnd);
      row.chars.forEach((ch, c) => {
        wider.chars[c] = ch;
        wider.classes[c] = row.classes[c] ?? "";
      });
      row = wider;
    }
    for (const hit of mine) addClass(row, hit.col - g, hit.col - g + hit.len, "hit");
    htmls.push(rowHtml(row));
  }
  return { htmls, copyAt };
}

/** The number column, one row each; the cursor's number in its own color. */
export function gutterRows(frame: Frame): string[] {
  return list(frame.nums).map((num, r) =>
    r === frame.cur.row && frame.cl ? `<span class="cnr">${escape(num)}</span>` : escape(num),
  );
}

/** The statusline as its two ends: " %f %m" and "%l:%c" (the padding between is the screen's). */
export function statusParts(status: string): { left: string; right: string } {
  const parts = /^(.*?)\s{2,}(\S.*?)\s*$/.exec(status);
  if (parts?.[1] === undefined || parts[2] === undefined)
    return { left: status.trimEnd(), right: "" };
  return { left: parts[1], right: parts[2] };
}

export function floatRows(frame: Frame): string[] {
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
  // A float is opaque: its rows keep every cell (rowHtml drops only plain trailing blanks).
  return rows.map((row) => rowHtml(row));
}
