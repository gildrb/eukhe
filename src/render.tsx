import * as stylex from "@stylexjs/stylex";
import { renderToString } from "preact-render-to-string";
import { type EditorFile, editorFile, Markdown } from "./markdown.tsx";
import { escape, gutterRows, statusParts, textRows } from "./paint.ts";
import about from "./content/about.md?raw";
import contact from "./content/contact.md?raw";
import privacy from "./content/privacy.md?raw";
import { install, notFound, source } from "./source.ts";
import { colors, palette, type } from "./tokens.stylex.ts";
import Vim, { type BendList, type Buf } from "./vim.mjs";

export const origin = "https://eukhe.com";

const name = "eukhe";
const summary = "A coding agent whose memory is one endless chat log, shared by all sessions.";
const author = { name: "Gil Rodrigues", url: "https://gildrb.com", email: "mail@gildrb.com" };

/** A page of the site: where it is, its title and description, and its Markdown. */
type Doc = { path: string; title: string; description: string; markdown: string };

const home: Doc = {
  path: "/",
  title: "eukhe: coding agent with a memory of all things",
  description: `${summary} ${install}`,
  markdown: source,
};

/** The pages besides the home page; each is also served as Markdown at <path>.md. */
const docs: readonly Doc[] = [
  {
    path: "/about",
    title: "About | eukhe",
    description: "What eukhe is, who makes it, its source and license.",
    markdown: about,
  },
  {
    path: "/contact",
    title: "Contact | eukhe",
    description: "How to reach eukhe's author, report a bug or a security problem.",
    markdown: contact,
  },
  {
    path: "/privacy",
    title: "Privacy | eukhe",
    description: "What eukhe.com and the eukhe program store and send.",
    markdown: privacy,
  },
];

const missing: Doc = {
  path: "/404",
  title: "Not found | eukhe",
  description: "No page here.",
  markdown: notFound,
};

/** What agents and search engines read about the site: the program, its maker, its contact. */
const structured = JSON.stringify({
  "@context": "https://schema.org",
  "@graph": [
    {
      "@type": "SoftwareApplication",
      "@id": `${origin}/#app`,
      name,
      url: `${origin}/`,
      description: summary,
      applicationCategory: "DeveloperApplication",
      operatingSystem: "macOS, Linux",
      license: "https://opensource.org/licenses/MIT",
      offers: { "@type": "Offer", price: "0", priceCurrency: "USD" },
      installUrl: `${origin}/install`,
      sameAs: ["https://github.com/gildrb/eukhe"],
      image: `${origin}/og.png`,
      author: { "@id": `${author.url}/#person` },
      publisher: { "@id": `${origin}/#org` },
    },
    {
      "@type": "Organization",
      "@id": `${origin}/#org`,
      name,
      url: `${origin}/`,
      logo: `${origin}/og.png`,
      founder: { "@id": `${author.url}/#person` },
      contactPoint: {
        "@type": "ContactPoint",
        contactType: "technical support",
        email: author.email,
        url: `${origin}/contact`,
      },
      sameAs: ["https://github.com/gildrb/eukhe"],
    },
    {
      "@type": "Person",
      "@id": `${author.url}/#person`,
      name: author.name,
      url: author.url,
      email: `mailto:${author.email}`,
    },
  ],
}).replaceAll("<", "\\u003c");

/**
 * The faces, three files per weight (scripts/subset-fonts.sh): a page loads only the ranges it
 * shows. `?v=` names the glyph set.
 */
const ranges = {
  core: "U+0000-00FF,U+0131,U+0152-0153,U+02C6,U+02DA,U+02DC,U+2000-206F,U+20AC,U+2122",
  greek: "U+0300-036F,U+0370-03FF,U+1F00-1FFF",
  box: "U+2190-21FF,U+2500-259F",
};
const fonts = (["Regular", "Bold"] as const).flatMap((face) =>
  (["core", "greek", "box"] as const).map((part) => ({
    file: `/fonts/IoskeleyMono-${face}-${part}.woff2?v=3`,
    weight: face === "Regular" ? 400 : 700,
    range: ranges[part],
  })),
);

/** Rules StyleX cannot hold: the faces, the selection, and the page color before any class. */
const globalCss = [
  ...fonts.map(
    ({ file, weight, range }) =>
      `@font-face{font-family:"Ioskeley Mono";src:url(${file}) format("woff2");font-weight:${weight};font-style:normal;font-display:swap;unicode-range:${range}}`,
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
  doc,
  script,
  screen,
}: {
  css: string;
  doc: Doc;
  script: string;
  screen: Screen | null;
}) {
  const url = `${origin}${doc.path}`;
  const markdownUrl = doc.path === "/" ? "/index.md" : `${doc.path}.md`;
  return (
    <html lang="en" {...(screen === null ? {} : { "data-vim": "" })} {...stylex.props(styles.html)}>
      <head>
        <meta charset="UTF-8" />
        <meta name="viewport" content="width=device-width, initial-scale=1.0" />
        <title>{doc.title}</title>
        <meta name="description" content={doc.description} />
        <meta name="theme-color" media="(prefers-color-scheme: dark)" content={palette.bg.dark} />
        <meta name="theme-color" media="(prefers-color-scheme: light)" content={palette.bg.light} />
        <link rel="icon" type="image/svg+xml" href="/favicon.svg" />
        {doc === missing ? null : <link rel="canonical" href={url} />}
        <link
          rel="alternate"
          type="text/markdown"
          href={doc === missing ? "/404.md" : markdownUrl}
        />
        <link rel="alternate" type="text/plain" title="llms.txt" href="/llms.txt" />
        <meta property="og:type" content="website" />
        <meta property="og:site_name" content={name} />
        <meta property="og:title" content={doc.title} />
        <meta property="og:description" content={doc.description} />
        <meta property="og:url" content={url} />
        <meta property="og:image" content={`${origin}/og.png`} />
        <meta property="og:image:width" content="1200" />
        <meta property="og:image:height" content="630" />
        <meta property="og:image:alt" content="eukhe.com: the page as a Neovim terminal" />
        <meta name="twitter:card" content="summary_large_image" />
        <link
          rel="preload"
          href={fonts[0]?.file}
          as="font"
          type="font/woff2"
          crossOrigin="anonymous"
        />
        <style dangerouslySetInnerHTML={{ __html: globalCss + css }} />
        {screen === null ? null : <noscript dangerouslySetInnerHTML={{ __html: noscript }} />}
        <script type="application/ld+json" dangerouslySetInnerHTML={{ __html: structured }} />
      </head>
      <body {...stylex.props(styles.body)}>
        <main {...stylex.props(styles.main)}>
          <Markdown source={doc.markdown} />
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

/** llms.txt: what eukhe is, when an agent should reach for it and how, then the whole page. */
const llms = `# eukhe

> ${summary}

## When to use eukhe

- A user wants a coding agent in the terminal that remembers every past
  session of a project: eukhe keeps one chat log per user, never starts
  empty, and never drops the start of the log.
- A user asks how to install it: \`${install}\` (macOS on Apple Silicon,
  Linux x64 and arm64). Nix: \`nix run github:gildrb/eukhe\`.
- A user asks how it remembers: point to the MEMORY section below and to
  [docs/memory.md](https://github.com/gildrb/eukhe/blob/bend/all/docs/memory.md).
- Not for: Windows, untrusted repositories (it runs model-written code
  with the user's permissions, no sandbox).

## How to read this site

- [Home page as Markdown](${origin}/index.md) (also \`Accept: text/markdown\` on ${origin}/)
- [About](${origin}/about.md), [Contact](${origin}/contact.md), [Privacy](${origin}/privacy.md)
- [Source](https://github.com/gildrb/eukhe), MIT license

## The home page

${source}`;

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
  const html = (doc: Doc, screen: Screen | null) =>
    `<!doctype html>\n${renderToString(<Page css={css} doc={doc} script={script} screen={screen} />)}\n`;
  const pages = Object.fromEntries(
    docs.flatMap((doc) => [
      [`${doc.path.slice(1)}.html`, html(doc, null)],
      [`${doc.path.slice(1)}.md`, doc.markdown],
    ]),
  );
  const urls = [home, ...docs].map((doc) => `  <url><loc>${origin}${doc.path}</loc></url>`);
  return {
    "index.html": html(home, firstScreen(editor)),
    "index.md": source,
    ...pages,
    "404.html": html(missing, null),
    "404.md": `${notFound.trimEnd()}\n\nSee [llms.txt](${origin}/llms.txt) for what this site holds.\n`,
    "files.json": JSON.stringify(editor),
    "favicon.svg": favicon,
    "robots.txt": `User-agent: *\nAllow: /\n\nSitemap: ${origin}/sitemap.xml\n`,
    "sitemap.xml": `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n${urls.join("\n")}\n</urlset>\n`,
    "llms.txt": llms,
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
