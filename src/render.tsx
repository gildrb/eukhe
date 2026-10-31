import * as stylex from "@stylexjs/stylex";
import { renderToString } from "preact-render-to-string";
import { type EditorFile, editorFile, Markdown } from "./markdown.tsx";
import { escape, gutterRows, statusParts, textRows } from "./paint.ts";
import { notFound, source } from "./source.ts";
import { colors, palette, type } from "./tokens.stylex.ts";
import Vim, { type BendList, type Buf } from "./vim.mjs";

export const origin = "https://eukhe.com";

const title = "eukhe";
const description =
  "A coding agent whose memory is one endless chat log, shared by all sessions. curl -fsSL https://eukhe.com/install | sh";

/** `?v=` names the glyph set: v2 is the Latin and Greek subset (scripts/subset-fonts.sh). */
const fonts = [
  { file: "/fonts/IoskeleyMono-Regular.woff2?v=2", weight: 400 },
  { file: "/fonts/IoskeleyMono-Bold.woff2?v=2", weight: 700 },
];

/** Rules StyleX cannot hold: the faces, the selection, and the page color before any class. */
const globalCss = [
  ...fonts.map(
    ({ file, weight }) =>
      `@font-face{font-family:"Ioskeley Mono";src:url(${file}) format("woff2");font-weight:${weight};font-style:normal;font-display:swap}`,
  ),
  `html{background:${palette.bg.dark};color-scheme:dark}`,
  `@media (prefers-color-scheme:light){html{background:${palette.bg.light};color-scheme:light}}`,
  `::selection{color:${colors.bg};background:${colors.primary}}`,
  // The editor (client.ts): a terminal of cells over the whole window, its first screen painted
  // here; the page stays in the document for assistive technology, search and agents. A cell is
  // 0.6em (every glyph of the font) by a line; the screen is W x H, whole cells.
  `[data-term]{--fs:15px;--cw:9px;--lh:18px;--ox:2px;--oy:2px;--W:round(down,100vw - 4px,var(--cw));--H:round(down,100dvh - 4px,var(--lh))}`,
  `@media (pointer:coarse){[data-term]{--fs:13px;--cw:7.8px;--lh:17px}}`,
  `html:not([data-vim]) [data-term]{display:none}`,
  `html[data-vim]{overflow:hidden}`,
  `html[data-vim] main{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%)}`,
  `html[data-vim] [data-deco]{display:none}`,
  // Rows and highlight groups: made by client.ts, which owns no StyleX classes.
  `[data-text]>div,[data-gutter]>div,[data-float]>div{height:var(--lh);white-space:pre;overflow:hidden}`,
  `[data-status-r]{position:absolute;right:var(--cw)}`,
  `[data-float][hidden]{display:none}`,
  `.title,.cnr,.ti,.prompt,.match,.sel{color:${colors.primary}}`,
  `.muted,.nr,.bd,.dim,.count,.ink-tertiary{color:${colors.tertiary}}`,
  `.heading,.match{color:${colors.primary};font-weight:${type.bold}}`,
  `.link,.copy{text-decoration:underline;text-decoration-color:${colors.tertiary};text-underline-offset:3px}`,
  `.copy{cursor:pointer}`,
  `.ink-primary{color:${colors.primary}}`,
  `.ink-article{color:${colors.article}}`,
  `.ink-bg{color:${colors.bg}}`,
  `.cl{background:color-mix(in oklch,${colors.primary} 6%,transparent)}`,
  `.hit{background:color-mix(in oklch,${colors.tertiary} 40%,transparent)}`,
  `.sel{background:color-mix(in oklch,${colors.primary} 14%,${colors.bg})}`,
  `.thumb{background:${colors.tertiary}}`,
  // A character two cells wide (fff's prompt goose): drawn in a box of exactly two cells.
  `.w2{display:inline-block;width:calc(2 * var(--cw));overflow:hidden;vertical-align:top}`,
].join("");

/** The favicon: the header's cursor, one block, in each theme's `primary`. */
export const favicon = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32"><style>rect{fill:${palette.primary.dark}}@media (prefers-color-scheme:light){rect{fill:${palette.primary.light}}}</style><rect x="9" y="4" width="14" height="24"/></svg>\n`;

/** The first screen, as client.ts would paint it on any screen (paint.ts). */
type Screen = {
  text: string;
  gutter: string;
  left: string;
  right: string;
  char: string;
  vars: Record<string, number>;
};

/** Rows as the client's layers hold them: one <div> each, the cursor's row with 'cursorline'. */
function rowsHtml(rows: readonly string[], cursorline: number | null): string {
  return rows.map((row, r) => `<div${r === cursorline ? ' class="cl"' : ""}>${row}</div>`).join("");
}

function cons<T>(items: readonly T[]): BendList<T> {
  return items.reduceRight<BendList<T>>((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
}

/** The editor at the start over these files, on a screen tall and wide enough for the page. */
function firstScreen(files: readonly EditorFile[]): Screen {
  const page = files[0];
  if (page === undefined) throw new Error("the editor has no page");
  const bufs = cons(
    files.map((file): Buf => ({ $: "Buf", path: file.path, lines: cons(file.lines) })),
  );
  const h = page.lines.length;
  const frame = Vim["Vim.frame"](Vim["Vim.init"](bufs, h + 2, 400));
  const { left, right } = statusParts(frame.status);
  return {
    text: rowsHtml(textRows(frame, page, [], h).htmls, frame.cl ? frame.cur.row : null),
    gutter: rowsHtml(gutterRows(frame), null),
    left,
    right,
    char: escape(frame.char),
    vars: {
      "--g": frame.gutter,
      "--crow": frame.cur.row,
      "--ccol": frame.cur.col,
      "--bar-start": 0,
      "--bar-len": 0,
    },
  };
}

/** Loads the module named in its own `data-src` once the page has loaded. */
const loader = `const src=document.currentScript.dataset.src;addEventListener("load",()=>{const s=document.createElement("script");s.type="module";s.src=src;document.body.append(s)})`;

/** Without the script: the page, not the terminal. */
const noscript = `<style>html[data-vim]{overflow:auto}html[data-vim] main{position:static;width:auto;height:auto;overflow:visible;clip-path:none}html[data-vim] [data-deco]{display:inline}[data-term]{display:none}</style>`;

function Page({
  css,
  markdown,
  path,
  script,
  screen,
}: {
  css: string;
  markdown: string;
  path: string;
  script: string;
  screen: Screen | null;
}) {
  return (
    <html lang="en" {...(screen === null ? {} : { "data-vim": "" })} {...stylex.props(styles.html)}>
      <head>
        <meta charset="UTF-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1.0" />
        <title>{path === "/" ? title : `Not found | ${title}`}</title>
        <meta name="description" content={description} />
        <meta name="theme-color" media="(prefers-color-scheme: dark)" content={palette.bg.dark} />
        <meta name="theme-color" media="(prefers-color-scheme: light)" content={palette.bg.light} />
        <link rel="icon" type="image/svg+xml" href="/favicon.svg" />
        {path === "/" ? <link rel="canonical" href={`${origin}/`} /> : null}
        <link rel="alternate" type="text/markdown" href="/index.md" />
        <meta property="og:title" content={title} />
        <meta property="og:description" content={description} />
        <meta property="og:url" content={`${origin}/`} />
        <link
          rel="preload"
          href={fonts[0]?.file}
          as="font"
          type="font/woff2"
          crossOrigin="anonymous"
        />
        <style dangerouslySetInnerHTML={{ __html: globalCss + css }} />
        {screen === null ? null : <noscript dangerouslySetInnerHTML={{ __html: noscript }} />}
      </head>
      <body {...stylex.props(styles.body)}>
        <main {...stylex.props(styles.main)}>
          <Markdown source={markdown} />
        </main>
        {/* The editor: a terminal of rows x cols cells; client.ts paints Vim.frame into it. */}
        <div
          data-term=""
          aria-hidden="true"
          style={screen?.vars ?? {}}
          {...stylex.props(styles.term)}
        >
          <div
            data-gutter=""
            dangerouslySetInnerHTML={{ __html: screen?.gutter ?? "" }}
            {...stylex.props(styles.gutter)}
          />
          <div
            data-text=""
            dangerouslySetInnerHTML={{ __html: screen?.text ?? "" }}
            {...stylex.props(styles.text)}
          />
          <div data-status="" {...stylex.props(styles.status)}>
            <span data-status-l="">{screen?.left ?? ""}</span>
            <span data-status-r="">{screen?.right ?? ""}</span>
          </div>
          <div data-cmd="" {...stylex.props(styles.cmd)} />
          <div data-bar="" {...stylex.props(styles.bar)} />
          <div data-float="" hidden {...stylex.props(styles.float)} />
          <div
            data-cursor=""
            dangerouslySetInnerHTML={{ __html: screen?.char ?? "" }}
            {...stylex.props(styles.cursor)}
          />
        </div>
        {/* The editor's code loads after the page: the first screen needs none of it. */}
        <script data-src={script} dangerouslySetInnerHTML={{ __html: loader }} />
      </body>
    </html>
  );
}

/** A file the editor holds; `plain` files show as they are, not as Markdown. */
export type SourceFile = { path: string; text: string; plain: boolean };

/**
 * Every file the site serves, by path under `dist/`, from the StyleX CSS, the client script and the
 * editor's other files of this build (the page comes first). `files.json` holds each file's lines
 * (for the Bend core) and highlights (for the screen).
 */
export function render(css: string, script: string, files: SourceFile[]): Record<string, string> {
  const editor = [{ path: "index.md", text: source, plain: false }, ...files].map((file) =>
    editorFile(file.path, file.text, file.plain),
  );
  const html = (markdown: string, path: string, screen: Screen | null) =>
    `<!doctype html>\n${renderToString(<Page css={css} markdown={markdown} path={path} script={script} screen={screen} />)}\n`;
  return {
    "index.html": html(source, "/", firstScreen(editor)),
    "index.md": source,
    "404.html": html(notFound, "/404", null),
    "files.json": JSON.stringify(editor),
    "favicon.svg": favicon,
    "robots.txt": `User-agent: *\nAllow: /\n\nSitemap: ${origin}/sitemap.xml\n`,
    "sitemap.xml": `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n  <url><loc>${origin}/</loc></url>\n</urlset>\n`,
    "llms.txt": source,
  };
}

const blink = stylex.keyframes({
  "0%, 50%": { opacity: 1 },
  "51%, 100%": { opacity: 0 },
});

const styles = stylex.create({
  html: {
    backgroundColor: colors.bg,
    WebkitFontSmoothing: "antialiased",
    MozOsxFontSmoothing: "grayscale",
    WebkitTextSizeAdjust: "100%",
    textRendering: "optimizeLegibility",
  },
  /** The column's width, for the header's fitted type (`markdown.tsx`). */
  main: { containerType: "inline-size" },
  body: {
    margin: 0,
    padding: { default: type.inset, "@media (max-width: 559px)": type.insetPhone },
    backgroundColor: colors.bg,
    color: colors.article,
    fontFamily: type.family,
    fontSize: type.size,
    lineHeight: type.leading,
  },
  /**
   * The terminal: the whole window, with Ghostty's 2px padding. The cell (--cw by --lh), the
   * grid's origin (--ox, --oy) and the screen (--W by --H) are set in globalCss; client.ts sets the
   * positions below in cells.
   */
  term: {
    position: "fixed",
    inset: 0,
    fontSize: "var(--fs)",
    lineHeight: "var(--lh)",
    // The finger scrolls the text (client.ts), never the page or its zoom.
    touchAction: "none",
    whiteSpace: "pre",
    userSelect: "none",
    cursor: "default",
  },
  /** The sign and number columns. */
  gutter: {
    position: "absolute",
    top: "var(--oy)",
    left: "var(--ox)",
    height: "calc(var(--H) - 2 * var(--lh))",
    overflow: "hidden",
    color: colors.tertiary,
  },
  /** The text rows, right of the gutter; the cursor's row carries 'cursorline' (`.cl`). */
  text: {
    position: "absolute",
    top: "var(--oy)",
    left: "calc(var(--ox) + var(--g) * var(--cw))",
    width: "calc(var(--W) - var(--g) * var(--cw))",
    height: "calc(var(--H) - 2 * var(--lh))",
    overflow: "hidden",
  },
  /** laststatus=3: one statusline across the window. */
  status: {
    position: "absolute",
    top: "calc(var(--oy) + var(--H) - 2 * var(--lh))",
    left: "var(--ox)",
    width: "var(--W)",
    height: "var(--lh)",
    overflow: "hidden",
    color: colors.tertiary,
    backgroundColor: `color-mix(in oklch, ${colors.primary} 8%, ${colors.bg})`,
  },
  cmd: {
    position: "absolute",
    top: "calc(var(--oy) + var(--H) - var(--lh))",
    left: "var(--ox)",
    width: "var(--W)",
    height: "var(--lh)",
    overflow: "hidden",
  },
  /** A floating window (fff, fzf-lua): opaque over the cells under it. */
  float: {
    position: "absolute",
    top: "calc(var(--oy) + var(--frow) * var(--lh))",
    left: "calc(var(--ox) + var(--fcol) * var(--cw))",
    width: "calc(var(--fw) * var(--cw))",
    backgroundColor: colors.bg,
  },
  /** vim's block cursor: the character under it in the page color. */
  cursor: {
    position: "absolute",
    top: "calc(var(--oy) + var(--crow) * var(--lh))",
    left: "calc(var(--ox) + var(--ccol) * var(--cw))",
    width: "var(--cw)",
    height: "var(--lh)",
    backgroundColor: colors.primary,
    color: colors.bg,
    pointerEvents: "none",
    animationName: { default: blink, "@media (prefers-reduced-motion: reduce)": "none" },
    animationDuration: "1s",
    animationIterationCount: "infinite",
    animationDelay: "0.5s",
  },
  /** The scrollbar: a thumb at the right edge of the text rows. */
  bar: {
    position: "absolute",
    top: "calc(var(--oy) + var(--bar-start) * var(--lh))",
    left: "calc(var(--ox) + var(--W) - 2px)",
    width: "2px",
    height: "calc(var(--bar-len) * var(--lh))",
    backgroundColor: colors.tertiary,
    pointerEvents: "none",
  },
});
