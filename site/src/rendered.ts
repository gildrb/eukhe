/**
 * The home page as Neovim shows a Markdown file with its renderer on (render-markdown.nvim with
 * 'conceallevel' 2, 'wrap' and 'linebreak', images inline as snacks.nvim draws them): markers
 * hidden, prose wrapped at the text width, code in its block, links by their label, HTML tags
 * rendered, and each image in rows of its own under its line. The source stays the page's Markdown
 * (`index.md`); this is the buffer the editor shows. Pure: the build paints it at the desktop width,
 * the browser again at its own when that is narrower.
 */
import { type Copy, copied, type EditorFile, type Hl, type Run } from "./markdown.tsx";
import { escape } from "./paint.ts";

/** An image in the buffer: the rows it covers from `line`, its file, its alt text and its size. */
export type Placement = {
  line: number;
  rows: number;
  src: string;
  alt: string;
  width: number;
  height: number;
};

/** The rendered buffer: its lines, each line's highlights, its code blocks' `[copy]`, its images. */
export type Rendered = { lines: string[]; runs: Run[][]; copies: Copy[]; images: Placement[] };

/** Where Eukhe's source lives: a line under the title and the page's last line link to it; so does each image. */
export const repository = "https://github.com/gildrb/eukhe";

/** The widest the text runs, in cells ('textwidth'). */
export const textWidth = 80;

/** A README image as the site serves it, by the path the README names it by: its file and its pixels. */
export type Shown = Readonly<Record<string, { src: string; width: number; height: number }>>;

/**
 * An image named `src` at `width` px: the file the site serves for it and its height at that
 * width. One the build does not serve (another page's, a link) keeps its own path and 16:9.
 */
export function served(src: string, width: number, shown: Shown): { src: string; height: number } {
  const own = shown[src];
  if (own !== undefined)
    return { src: own.src, height: Math.round((width * own.height) / own.width) };
  const path = /^([a-z][a-z0-9+.-]*:|\/)/i.test(src) ? src : `/${src}`;
  return { src: path, height: Math.round((width * 9) / 16) };
}

/** A cell's size in CSS pixels. */
export type Cell = { cw: number; lh: number };

/** A desktop's cell (render.tsx's `--cw` and `--lh`): the width the build renders at. */
export const desktop: Cell = { cw: 9, lh: 18 };

/** A piece of inline text in one style. */
type Piece = { text: string; hl: Hl[]; href?: string };

/** An image named in a paragraph. */
type Img = { $: "Img"; src: string; alt: string; width: number };

/** A paragraph's parts in order: runs of text, a line break, an image. */
type Part = { $: "Text"; piece: Piece } | { $: "Break" } | Img;

const attr = (tag: string, name: string): string | undefined =>
  new RegExp(`\\b${name}="([^"]*)"`).exec(tag)?.[1];

/** Inline Markdown and the README's HTML (`<b>`, `<i>`, `<code>`, `<br>`, `<img>`, `<p>`). */
function parts(text: string): Part[] {
  const out: Part[] = [];
  const styles: Hl[] = [];
  const token =
    /`([^`]+)`|\[([^\]]+)\]\(([^)\s]+)\)|\*\*([^*]+)\*\*|<br\s*\/?>|<img\b[^>]*>|<\/?(b|i|code|p)\b[^>]*>/g;
  let last = 0;
  const push = (t: string, extra: Hl[] = [], href?: string) => {
    if (t === "") return;
    const hl = [...styles, ...extra];
    out.push({ $: "Text", piece: href === undefined ? { text: t, hl } : { text: t, hl, href } });
  };
  for (const match of text.matchAll(token)) {
    push(text.slice(last, match.index));
    last = match.index + match[0].length;
    const [whole, code, label, url, bold, tag] = match;
    if (code !== undefined) push(code, ["code"]);
    else if (label !== undefined && url !== undefined)
      push(label, ["link"], /^([a-z][a-z0-9+.-]*:|\/|#)/i.test(url) ? url : `/${url}`);
    else if (bold !== undefined) push(bold, ["bold"]);
    else if (whole.startsWith("<br")) out.push({ $: "Break" });
    else if (whole.startsWith("<img")) {
      const src = attr(whole, "src");
      if (src !== undefined)
        out.push({
          $: "Img",
          src,
          alt: attr(whole, "alt") ?? "",
          width: Number(attr(whole, "width") ?? "640"),
        });
    } else if (tag !== undefined && tag !== "p") {
      const hl: Hl = tag === "b" ? "bold" : tag === "i" ? "italic" : "code";
      if (whole.startsWith("</")) styles.splice(styles.lastIndexOf(hl), 1);
      else styles.push(hl);
    }
  }
  push(text.slice(last));
  return out;
}

/** Pieces as words: each word keeps the style of each of its characters. */
type Word = { pieces: Piece[]; len: number };

function words(pieces: readonly Piece[]): Word[] {
  const out: Word[] = [];
  let current: Piece[] = [];
  let len = 0;
  const flush = () => {
    if (len > 0) out.push({ pieces: current, len });
    current = [];
    len = 0;
  };
  for (const piece of pieces) {
    for (const [i, chunk] of piece.text.split(" ").entries()) {
      if (i > 0) flush();
      if (chunk === "") continue;
      current.push({ ...piece, text: chunk });
      len += Array.from(chunk).length;
    }
  }
  flush();
  return out;
}

/** A line being built: its text and its runs. */
type Built = { text: string; runs: Run[] };

/** Words wrapped at width w ('linebreak'), each line led by `lead` and the next ones by `hang`. */
function wrap(
  ws: readonly Word[],
  w: number,
  lead: string,
  hang: string,
  center: boolean,
): Built[] {
  const lines: Word[][] = [];
  let line: Word[] = [];
  let len = 0;
  const room = (first: boolean) => w - Array.from(first ? lead : hang).length;
  for (const word of ws) {
    const sep = line.length > 0 ? 1 : 0;
    if (line.length > 0 && len + sep + word.len > room(lines.length === 0)) {
      lines.push(line);
      line = [];
      len = 0;
    }
    len += (line.length > 0 ? 1 : 0) + word.len;
    line.push(word);
  }
  if (line.length > 0) lines.push(line);
  return lines.map((row, i) => {
    const prefix = i === 0 ? lead : hang;
    const width = row.reduce((sum, word) => sum + word.len, 0) + Math.max(0, row.length - 1);
    const pad = center ? " ".repeat(Math.max(0, Math.floor((w - width) / 2))) : "";
    let text = prefix + pad;
    const runs: Run[] = [];
    row.forEach((word, k) => {
      if (k > 0) text += " ";
      for (const piece of word.pieces) {
        const from = Array.from(text).length;
        text += piece.text;
        const to = Array.from(text).length;
        for (const hl of piece.hl)
          runs.push(
            piece.href !== undefined && hl === "link"
              ? { from, to, hl, href: piece.href }
              : { from, to, hl },
          );
      }
    });
    return { text, runs: joined(runs) };
  });
}

/** Runs of one style one space apart made one: inline code or a link keeps its spaces styled. */
function joined(runs: readonly Run[]): Run[] {
  const out: Run[] = [];
  for (const run of runs.toSorted((a, b) => a.from - b.from)) {
    const prev = out.findLast((r) => r.hl === run.hl && r.href === run.href);
    if (prev !== undefined && prev.to + 1 === run.from) prev.to = run.to;
    else out.push({ ...run });
  }
  return out;
}

/**
 * The page's Markdown rendered at w cells, its images as `shown` serves them. `rowsOf` gives the
 * rows an image covers at width w (snacks.nvim keeps an image's aspect: its height in rows follows
 * its width).
 */
export function render(
  source: string,
  w: number,
  linkHome: boolean,
  shown: Shown,
  rowsOf: (img: { width: number; height: number }) => number,
): Rendered {
  const lines: string[] = [];
  const runs: Run[][] = [];
  const images: Placement[] = [];
  const copies: Copy[] = [];
  const add = (b: Built) => {
    lines.push(b.text);
    runs.push(b.runs);
  };
  const blank = () => {
    if (lines.length > 0 && lines.at(-1) !== "") add({ text: "", runs: [] });
  };
  const md = source.replace(/\n$/, "").split("\n");
  let named = false;
  for (let i = 0; i < md.length; i += 1) {
    const line = md[i] ?? "";
    if (line === "") {
      blank();
      continue;
    }
    if (line.startsWith("```")) {
      // The block: its language as its label (`[copy]` after it), its lines as they are, the
      // fences hidden.
      const lang = line.slice(3).trim();
      const at = lines.length;
      add({
        text: lang,
        runs: lang === "" ? [] : [{ from: 0, to: Array.from(lang).length, hl: "muted" }],
      });
      const commands: string[] = [];
      const rows: number[] = [];
      for (i += 1; i < md.length && !(md[i] ?? "").startsWith("```"); i += 1) {
        const code = md[i] ?? "";
        const comment = /(^|\s)#\s.*$/.exec(code);
        const cut = comment === null ? null : comment.index + (comment[1]?.length ?? 0);
        add({
          text: code,
          runs:
            cut === null
              ? []
              : [
                  {
                    from: Array.from(code.slice(0, cut)).length,
                    to: Array.from(code).length,
                    hl: "muted",
                  },
                ],
        });
        commands.push(code.replace(/(^|\s)#\s.*$/, "").trimEnd());
        rows.push(lines.length - 1);
      }
      const pick = copied(commands);
      const row = rows[pick?.index ?? -1];
      if (pick !== null && row !== undefined) copies.push({ line: at, at: row, text: pick.text });
      continue;
    }
    const art = /^<a href="([^"]+)"><pre>$/.exec(line)?.[1];
    if (art !== undefined) {
      // A drawing in characters that links somewhere (`<a href="…"><pre>` … `</pre></a>`, as GitHub
      // renders it): its lines as they are, every character a link.
      for (i += 1; i < md.length && md[i] !== "</pre></a>"; i += 1) {
        const text = md[i] ?? "";
        const n = Array.from(text).length;
        add({ text, runs: n === 0 ? [] : [{ from: 0, to: n, hl: "heading", href: art }] });
      }
      continue;
    }
    const heading = /^(#{1,6}) (.*)$/.exec(line);
    if (heading?.[2] !== undefined) {
      const text = heading[2];
      const n = Array.from(text).length;
      // The page's name (its first `# ` heading) links home on the site's own pages.
      const home = linkHome && !named && heading[1] === "#";
      if (heading[1] === "#") named = true;
      add({
        text,
        runs: [
          { from: 0, to: n, hl: "heading" },
          ...(home ? [{ from: 0, to: n, hl: "link" as const, href: "/" }] : []),
        ],
      });
      continue;
    }
    if (line.startsWith("> ")) {
      // A quote's sentence: its lines up to one that ends it (".", ";" or "·").
      let said = line.slice(2);
      while (!/[.;·]$/.test(said) && (md[i + 1] ?? "").startsWith("> ")) {
        i += 1;
        said += ` ${(md[i] ?? "").slice(2)}`;
      }
      for (const b of wrap(words([{ text: said, hl: ["italic"] }]), w, "▍ ", "▍ ", false))
        add({ text: b.text, runs: [{ from: 0, to: 1, hl: "muted" }, ...b.runs] });
      continue;
    }
    const item = /^( *)- (.*)$/.exec(line);
    if (item?.[1] !== undefined && item[2] !== undefined) {
      const indent = item[1];
      for (const b of wrap(words(texts(parts(item[2]))), w, `${indent}• `, `${indent}  `, false))
        add(b);
      continue;
    }
    // A paragraph: this line and the next ones up to a blank line.
    let text = line;
    while (
      i + 1 < md.length &&
      (md[i + 1] ?? "") !== "" &&
      !/^(#|```|> |- )/.test(md[i + 1] ?? "")
    ) {
      i += 1;
      text += ` ${md[i] ?? ""}`;
    }
    const center = /<p\b[^>]*align="center"/.test(text);
    let group: Piece[] = [];
    const flush = () => {
      if (group.length > 0) for (const b of wrap(words(group), w, "", "", center)) add(b);
      group = [];
    };
    for (const part of parts(text)) {
      if (part.$ === "Text") group.push(part.piece);
      else if (part.$ === "Break") flush();
      else {
        flush();
        const file = served(part.src, part.width, shown);
        const img = { src: file.src, alt: part.alt, width: part.width, height: file.height };
        const rows = rowsOf(img);
        images.push({ line: lines.length, rows, ...img });
        for (let r = 0; r < rows; r += 1) add({ text: "", runs: [] });
      }
    }
    flush();
  }
  return { lines, runs, copies, images };
}

function texts(ps: readonly Part[]): Piece[] {
  return ps.flatMap((p) => (p.$ === "Text" ? [p.piece] : []));
}

/** The width an image shows at in CSS pixels: its own, and no wider than the text. */
export function imagePixels(img: { width: number }, w: number, cell: Cell): number {
  return Math.min(img.width, w * cell.cw);
}

/** The rows an image covers: its height at that width, in whole lines. */
export function imageRows(img: { width: number; height: number }, w: number, cell: Cell): number {
  return Math.ceil((imagePixels(img, w, cell) * img.height) / img.width / cell.lh);
}

/**
 * The images of the window from line `top`, `left` columns scrolled, over text w cells wide: one
 * `<img>` each, placed in cells (the layer clips them to the text rows), centred as the README
 * centres them. The build paints the first screen's, the browser every later one's. The window's
 * first image is the page's largest paint: fetched first; the others when they come near.
 */
export function imagesHtml(
  images: readonly Placement[],
  top: number,
  left: number,
  w: number,
): string {
  return images
    .map(
      (img, k) =>
        `<a href="${repository}" style="${imageStyle(img, top, left, w)}"><img src="${escape(img.src)}" alt="${escape(img.alt).replaceAll('"', "&quot;")}" width="${img.width}" height="${img.height}" ${k === 0 ? 'fetchpriority="high"' : 'loading="lazy"'}></a>`,
    )
    .join("");
}

/** Where an image shows in the window from line `top`, `left` columns scrolled, text w cells wide. */
export function imageStyle(img: Placement, top: number, left: number, w: number): string {
  const width = `min(${img.width}px,${w} * var(--cw))`;
  return `top:calc(${img.line - top} * var(--lh));left:calc((${w} * var(--cw) - ${width}) / 2 - ${left} * var(--cw));width:${width}`;
}

/** The home page's editor file at w cells: rendered, with what the browser needs to render it again. */
export function pageFile(
  path: string,
  source: string,
  shown: Shown,
  w: number,
  cell: Cell,
  linkHome: boolean,
): EditorFile {
  const r = render(source, w, linkHome, shown, (img) => imageRows(img, w, cell));
  return {
    path,
    lines: r.lines,
    runs: r.runs,
    copies: r.copies,
    images: r.images,
    page: { source, shown, width: w, linkHome },
  };
}
