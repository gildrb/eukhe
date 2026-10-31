import * as stylex from "@stylexjs/stylex";
import { renderToString } from "preact-render-to-string";
import { editorFile, Markdown } from "./markdown.tsx";
import { notFound, source } from "./source.ts";
import { colors, palette, type } from "./tokens.stylex.ts";

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
  // The editor (client.ts): a terminal of cells over the whole window, shown once the script runs
  // on a screen with a keyboard and room; the page stays in the document for assistive technology.
  `html:not([data-vim]) [data-term]{display:none}`,
  `html[data-vim]{overflow:hidden}`,
  `html[data-vim] main{position:absolute;width:1px;height:1px;overflow:hidden;clip-path:inset(50%)}`,
  `html[data-vim] [data-deco]{display:none}`,
  // Rows and highlight groups: made by client.ts, which owns no StyleX classes.
  `[data-text]>div,[data-float]>div{height:var(--lh);white-space:pre;overflow:hidden}`,
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

function Page({
  css,
  markdown,
  path,
  script,
}: {
  css: string;
  markdown: string;
  path: string;
  script: string;
}) {
  return (
    <html lang="en" {...stylex.props(styles.html)}>
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
          crossorigin="anonymous"
        />
        <style dangerouslySetInnerHTML={{ __html: globalCss + css }} />
      </head>
      <body {...stylex.props(styles.body)}>
        <main {...stylex.props(styles.main)}>
          <Markdown source={markdown} path={path === "/" ? "index.md" : "404"} />
        </main>
        {/* The editor: a terminal of rows x cols cells; client.ts paints Vim.frame into it. */}
        <div data-term="" aria-hidden="true" {...stylex.props(styles.term)}>
          <pre data-gutter="" {...stylex.props(styles.gutter)} />
          <div data-text="" {...stylex.props(styles.text)} />
          <div data-status="" {...stylex.props(styles.status)} />
          <div data-cmd="" {...stylex.props(styles.cmd)} />
          <div data-bar="" {...stylex.props(styles.bar)} />
          <div data-float="" hidden {...stylex.props(styles.float)} />
          <div data-cursor="" {...stylex.props(styles.cursor)} />
        </div>
        <script type="module" src={script} />
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
  const html = (markdown: string, path: string) =>
    `<!doctype html>\n${renderToString(<Page css={css} markdown={markdown} path={path} script={script} />)}\n`;
  const editor = [{ path: "index.md", text: source, plain: false }, ...files].map((file) =>
    editorFile(file.path, file.text, file.plain),
  );
  return {
    "index.html": html(source, "/"),
    "index.md": source,
    "404.html": html(notFound, "/404"),
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
   * The terminal: the whole window, with Ghostty's 2px padding. client.ts sets the cell (--cw by
   * --lh, from the font), the grid's origin (--ox, --oy) and every position below in cells.
   */
  term: {
    position: "fixed",
    inset: 0,
    fontSize: "15px",
    lineHeight: "var(--lh)",
    whiteSpace: "pre",
    userSelect: "none",
    cursor: "default",
  },
  /** The sign and number columns. */
  gutter: {
    position: "absolute",
    top: "var(--oy)",
    left: "var(--ox)",
    margin: 0,
    font: "inherit",
    color: colors.tertiary,
  },
  /** The text rows, right of the gutter; the cursor's row carries 'cursorline' (`.cl`). */
  text: {
    position: "absolute",
    top: "var(--oy)",
    left: "calc(var(--ox) + var(--g) * var(--cw))",
    width: "calc((var(--cols) - var(--g)) * var(--cw))",
  },
  /** laststatus=3: one statusline across the window. */
  status: {
    position: "absolute",
    top: "calc(var(--oy) + var(--h) * var(--lh))",
    left: "var(--ox)",
    width: "calc(var(--cols) * var(--cw))",
    height: "var(--lh)",
    overflow: "hidden",
    color: colors.tertiary,
    backgroundColor: `color-mix(in oklch, ${colors.primary} 8%, ${colors.bg})`,
  },
  cmd: {
    position: "absolute",
    top: "calc(var(--oy) + (var(--h) + 1) * var(--lh))",
    left: "var(--ox)",
    width: "calc(var(--cols) * var(--cw))",
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
    left: "calc(var(--ox) + var(--cols) * var(--cw) - 2px)",
    width: "2px",
    height: "calc(var(--bar-len) * var(--lh))",
    backgroundColor: colors.tertiary,
    pointerEvents: "none",
  },
});
