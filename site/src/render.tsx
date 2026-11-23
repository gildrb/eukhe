import * as stylex from "@stylexjs/stylex";
import { renderToString } from "preact-render-to-string";
import { type EditorFile, editorFile, Markdown } from "./markdown.tsx";
import { escape, gutterRows, statusParts, textRows } from "./paint.ts";
import about from "./content/about.md?raw";
import contact from "./content/contact.md?raw";
import privacy from "./content/privacy.md?raw";
import { desktop, imagesHtml, pageFile, type Shown, textWidth } from "./rendered.ts";
import { definition, install, notFound, source } from "./source.ts";
import { colors, palette, type } from "./tokens.stylex.ts";
import Vim, { type BendList, type Buf } from "./vim.mjs";

export const origin = "https://eukhe.com";

const name = "Eukhe";
/** The title a shared link to the home page shows. */
const sharedTitle = "Eukhe Harness";
const author = { name: "Gil Rodrigues", url: "https://gildrb.com", email: "g@gildrb.com" };

/** A page of the site: where it is, its title and description, and its Markdown. */
type Doc = { path: string; title: string; description: string; markdown: string };

const home: Doc = {
  path: "/",
  title: "index.md | Eukhe",
  description: definition,
  markdown: source,
};

/** The pages besides the home page; each is also served as Markdown at <path>.md. */
const docs: readonly Doc[] = [
  {
    path: "/about",
    title: "about.md | Eukhe",
    description: "What Eukhe is, what is proven today and what is planned, and who makes it.",
    markdown: about,
  },
  {
    path: "/contact",
    title: "contact.md | Eukhe",
    description: "How to reach Eukhe's author and report a bug or a security problem.",
    markdown: contact,
  },
  {
    path: "/privacy",
    title: "privacy.md | Eukhe",
    description: "What eukhe.com and the Eukhe program store and send.",
    markdown: privacy,
  },
];

const missing: Doc = {
  path: "/404",
  title: "404.md | Eukhe",
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
      description: definition,
      applicationCategory: "DeveloperApplication",
      operatingSystem: "macOS, Linux",
      license: "https://opensource.org/licenses/MIT",
      offers: { "@type": "Offer", price: "0", priceCurrency: "USD" },
      installUrl: `${origin}/install`,
      sameAs: ["https://github.com/gildrb/eukhe"],
      author: { "@id": `${author.url}/#person` },
      publisher: { "@id": `${origin}/#org` },
    },
    {
      "@type": "Organization",
      "@id": `${origin}/#org`,
      name,
      url: `${origin}/`,
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
 * The faces: Paper Mono's release files as they are (scripts/fonts.py), one per weight. Its
 * advance is 606/1000 em; `size-adjust` sets it to the grid's 0.6em cell (99.01%: a CSS scale, the
 * files stay unmodified). Paper Mono has no Greek: the epigraphs' Greek comes from the system's
 * monospace (the font-family stack, tokens.stylex.ts). `?v=` names the release.
 */
const fonts = (["Regular", "Bold"] as const).map((face) => ({
  file: `/fonts/PaperMono-${face}.woff2?v=1.000`,
  weight: face === "Regular" ? 400 : 700,
}));

/** Rules StyleX cannot hold: the faces, the selection, and the page color before any class. */
const globalCss = [
  ...fonts.map(
    ({ file, weight }) =>
      `@font-face{font-family:"Paper Mono";src:url(${file}) format("woff2");font-weight:${weight};font-style:normal;font-display:swap;size-adjust:99.01%}`,
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
  `.muted,.nr,.bd,.dim,.count{color:${colors.tertiary}}`,
  `.heading,.match{color:${colors.primary};font-weight:${type.bold}}`,
  `.link,.copy{text-decoration:underline;text-decoration-color:${colors.tertiary};text-underline-offset:3px}`,
  // The README's images: in the page under their figure; in the editor in rows of their own, under
  // the text layer.
  `main img{display:block;margin:0 auto;max-width:100%;height:auto}`,
  `[data-images]{position:absolute;top:var(--oy);left:calc(var(--ox) + var(--g) * var(--cw));right:0;height:calc(var(--H) - 2 * var(--lh));overflow:hidden;pointer-events:none}`,
  `[data-images]>a{position:absolute;display:block;pointer-events:auto}`,
  `[data-images] img{display:block;width:100%;height:auto}`,
  `.bold{font-weight:${type.bold};color:${colors.primary}}`,
  `.italic{font-style:italic}`,
  `.code{color:${colors.primary}}`,
  `.copy{cursor:pointer}`,
  `.cl{background:color-mix(in oklch,${colors.primary} 6%,transparent)}`,
  `.hit{background:color-mix(in oklch,${colors.tertiary} 40%,transparent)}`,
  `.sel{background:color-mix(in oklch,${colors.primary} 14%,${colors.bg})}`,
  `.thumb{background:${colors.tertiary}}`,
  // Visual mode's selection (Neovim's Visual group).
  `.vis{background:color-mix(in oklch,${colors.primary} 22%,transparent)}`,
  // What a yank took, for 150 ms (Neovim's vim.hl.on_yank with IncSearch).
  `.yank{background:${colors.primary};color:${colors.bg}}`,
  // A character two cells wide (fff's prompt goose): drawn in a box of exactly two cells.
  `.w2{display:inline-block;width:calc(2 * var(--cw));overflow:hidden;vertical-align:top}`,
].join("");

/** The favicon: a block in the Temple of Hephaestus's proportion (9 : 4), the full width of the canvas, in each theme's primary. */
export const favicon = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 36 36"><style>rect{fill:${palette.primary.dark}}@media (prefers-color-scheme:light){rect{fill:${palette.primary.light}}}</style><rect y="10" width="36" height="16"/></svg>\n`;
/** Where pages link the favicon: the version changes with it, so browsers drop the one they cached. */
export const faviconHref = "/favicon.svg?v=3";

/** The first screen, as client.ts would paint it on any screen (paint.ts). */
type Screen = {
  text: string;
  gutter: string;
  left: string;
  right: string;
  char: string;
  images: string;
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
    images: page.page === null ? "" : imagesHtml(page.images, 0, 0, page.page.width),
    vars: {
      "--g": frame.gutter,
      "--crow": frame.cur.row,
      "--ccol": frame.cur.col,
      "--bar-start": 0,
      "--bar-len": 0,
    },
  };
}

/** The editor's file of a page: index.md for the home page, about.md for /about. */
function markdownFile(doc: Doc): string {
  return doc.path === "/" ? "index.md" : `${doc.path.slice(1)}.md`;
}

/** Without the script: the page, not the terminal. */
const noscript = `<style>html[data-vim]{overflow:auto}html[data-vim] main{position:static;width:auto;height:auto;overflow:visible;clip-path:none}html[data-vim] [data-deco]{display:inline}[data-term]{display:none}</style>`;

/**
 * `translate="no"`: the page is English and never machine-translated. A string record: preact types
 * `translate` as a boolean, and renders no `translate="no"` from one.
 */
const noTranslate: Readonly<Record<string, string>> = { translate: "no" };

function Page({
  css,
  doc,
  script,
  screen,
  shown,
}: {
  css: string;
  doc: Doc;
  script: string;
  screen: Screen | null;
  shown: Shown;
}) {
  const url = `${origin}${doc.path}`;
  const markdownUrl = doc.path === "/" ? "/index.md" : `${doc.path.replace(/\/$/, "")}.md`;
  return (
    <html
      lang="en"
      {...noTranslate}
      {...(screen === null ? {} : { "data-vim": "", "data-page": markdownFile(doc) })}
      {...stylex.props(styles.html)}
    >
      <head>
        <meta charset="UTF-8" />
        {/* English, never machine-translated: the Greek epigraphs (lang="grc") trip the
            browser's language guess and its "translate this page" offer. */}
        <meta name="google" content="notranslate" />
        <meta name="viewport" content="width=device-width, initial-scale=1.0" />
        <title>{doc.title}</title>
        <meta name="description" content={doc.description} />
        <meta name="theme-color" media="(prefers-color-scheme: dark)" content={palette.bg.dark} />
        <meta name="theme-color" media="(prefers-color-scheme: light)" content={palette.bg.light} />
        <link rel="icon" type="image/svg+xml" href={faviconHref} />
        {doc === missing ? null : <link rel="canonical" href={url} />}
        <link
          rel="alternate"
          type="text/markdown"
          href={doc === missing ? "/404.md" : markdownUrl}
        />
        <link rel="alternate" type="text/plain" title="llms.txt" href="/llms.txt" />
        <meta property="og:type" content="website" />
        <meta property="og:site_name" content={name} />
        <meta property="og:title" content={doc === home ? sharedTitle : doc.title} />
        <meta property="og:description" content={doc.description} />
        <meta property="og:url" content={url} />
        <meta name="twitter:card" content="summary" />
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
        <main>
          <Markdown source={doc.markdown} linkHome={doc !== home} shown={shown} />
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
          <div data-images="" dangerouslySetInnerHTML={{ __html: screen?.images ?? "" }} />
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
        {/* The editor's code: a module, so it never holds up the first screen, and it runs before
            the page's load (fonts, images) ends, so the first touch already scrolls. */}
        <script type="module" src={script} />
      </body>
    </html>
  );
}

/** llms.txt: what Eukhe is, the wish, its laws, embedding and components, how to install it, then the whole page. */
const llms = `# Eukhe

> ${definition}

## What it is

Eukhe is εὐχή, Greek for wish. You write the wish as rules in
\`AGENTS.md\`, as a task and as commands that must pass. When one of
those commands fails, Eukhe gives its output to the agent and runs
another turn, until every command passes or the run reaches a limit. A
session is an append-only log on disk, so it survives a crash and
\`eukhe --continue\` reopens it.

The \`eukhe\` command runs a coding agent on Eukhe's core in your
terminal. The \`eukhe-sdk\` Rust crate runs sessions on it inside your
own process.

## Wish

- Eukhe reads \`AGENTS.md\` in the project and puts it in the system prompt.
- \`eukhe --auto -p "task"\` keeps running turns on the task until its
  acceptance checks all pass, it reaches a limit (\`--budget-tokens\` and the
  other \`--budget-*\` flags), or its turns stop making progress; the run then
  ends at its next final answer.
- \`eukhe --autonomous --autonomous-gate "cargo test"\` runs \`cargo test\`
  after each turn and runs another turn while it fails, up to the
  limits that \`eukhe --help\` lists.

## Laws

[spec/README.md](${origin}/spec/README.md) numbers the requirements. A
law is a theorem that the core, the part of Eukhe written in
[Bend](https://bend-lang.com), meets one of those requirements.
\`PROOF.bend\` holds a proof of every law, and \`bend PROOF.bend\` checks
them. The proofs cover the Bend core and say nothing about what the
model writes.

## Embed

The npm package \`eukhe\` runs Eukhe from TypeScript:
\`npm install eukhe && npx eukhe install\`, then \`Eukhe.start({ cwd })\`,
\`eukhe.session()\` and \`session.prompt(text)\`, which streams typed events
and ends with the run report
([crates/eukhe-sdk/ts/README.md](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/ts/README.md)). Any other
language starts \`eukhe acp\`, an Agent Client Protocol agent on stdio; the
budget, checks, undo, diff and irreversible effects are \`_eukhe/\` methods
([crates/eukhe-sdk/README.md](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/README.md#acp), JSON Schema
[crates/eukhe-sdk/acp.schema.json](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/acp.schema.json)).
A machine needs one model provider login: \`eukhe login <provider>\`.
[crates/eukhe-sdk/README.md](https://github.com/gildrb/eukhe/blob/main/crates/eukhe-sdk/README.md) holds the T3 Code
settings and an agent skill for adding Eukhe to a project
(\`npx skills add https://github.com/gildrb/eukhe/tree/main/crates/eukhe-sdk\`).

## Components

[Durable](${origin}/spec/durable/), [Memory](${origin}/spec/memory/),
[RLM](${origin}/spec/rlm/) and [Autoresearch](${origin}/spec/autoresearch/)
have requirements and laws. Loop, the code behind \`--auto\`, has no
requirements, spec files or laws yet.

Planned and not built: confinement of the programs the agent runs, checks
the agent never sees, review of the process for gaming, capability
security, replayable record, orchestration at scale, stable SDK contract.

## Install

\`${install}\` on macOS (Apple Silicon) or Linux (x64, arm64). With Nix:
\`nix run github:gildrb/eukhe\`. Eukhe does not run on Windows. It runs
model-written Python and shell with the user's permissions and has no
sandbox: use it in trusted repositories only.

## How to read this site

- [Home page as Markdown](${origin}/index.md) (also \`Accept: text/markdown\` on ${origin}/):
  Eukhe's README, with the site's epigraphs
- [About](${origin}/about.md), [Contact](${origin}/contact.md), [Privacy](${origin}/privacy.md)
- [Source](https://github.com/gildrb/eukhe), MIT license

## The home page

${source}`;

/** A file the editor holds; `plain` files show as they are, not as Markdown. */
export type SourceFile = { path: string; text: string; plain: boolean };

/**
 * A folder of eukhe's files as a page, for a browser without the editor: what the folder holds,
 * folders first, each a link. `folder` ends in "/".
 */
function folderDoc(folder: string, paths: readonly string[]): Doc {
  const children = new Set(
    paths
      .filter((file) => file.startsWith(folder))
      .map((file) => file.slice(folder.length).replace(/\/.*$/s, "/")),
  );
  const sorted = [...children].toSorted((a, b) =>
    a.endsWith("/") === b.endsWith("/") ? (a < b ? -1 : 1) : a.endsWith("/") ? -1 : 1,
  );
  return {
    path: `/${folder}`,
    title: `/${folder} | Eukhe`,
    description: `Eukhe's ${folder}: ${sorted.join(", ")}.`,
    markdown: [
      "EUKHE",
      folder.toUpperCase(),
      "2026",
      "",
      `# ${folder}`,
      "",
      ...sorted.map((child) => `- [${child}](/${folder}${child})`),
      "",
    ].join("\n"),
  };
}

/**
 * Every file the site serves, by path under `dist/`, from the StyleX CSS, the client script and
 * eukhe's files of this build. `files.json` holds each editor file's lines (for the Bend core) and
 * highlights (for the screen); eukhe's files are also served as they are, at their paths, and each
 * of their folders as a page.
 */
export function render(
  css: string,
  script: string,
  files: SourceFile[],
  shown: Shown,
): Record<string, string> {
  // The editor's files: the home page (rendered), the other pages, then eukhe's files.
  // Markdown shows rendered (rendered.ts): the home page, the site's pages, eukhe's Markdown files;
  // eukhe's other files show as they are.
  const editor = [
    pageFile("index.md", source, shown, textWidth, desktop, false),
    ...[...docs, missing].map((doc) =>
      pageFile(`${doc.path.slice(1)}.md`, doc.markdown, shown, textWidth, desktop, true),
    ),
    ...files.map((file) =>
      file.path.endsWith(".md")
        ? pageFile(file.path, file.text, shown, textWidth, desktop, false)
        : editorFile(file.path, file.text, file.plain, false),
    ),
  ];
  // A page opens the editor on its own file: that file first (client.ts orders them the same way).
  const first = (path: string) => {
    const own = editor.filter((file) => file.path === path);
    return firstScreen([...own, ...editor.filter((file) => file.path !== path)]);
  };
  const html = (doc: Doc, screen: Screen | null) =>
    `<!doctype html>\n${renderToString(<Page css={css} doc={doc} script={script} screen={screen} shown={shown} />)}\n`;
  const pages = Object.fromEntries(
    docs.flatMap((doc) => [
      [`${doc.path.slice(1)}.html`, html(doc, first(`${doc.path.slice(1)}.md`))],
      [`${doc.path.slice(1)}.md`, doc.markdown],
    ]),
  );
  const urls = [home, ...docs].map((doc) => `  <url><loc>${origin}${doc.path}</loc></url>`);
  const paths = files.map((file) => file.path);
  const folders = new Set(
    paths.flatMap((file) =>
      file
        .split("/")
        .slice(0, -1)
        .map((_, i, parts) => `${parts.slice(0, i + 1).join("/")}/`),
    ),
  );
  const eukhe = Object.fromEntries([
    ...files.map((file): [string, string] => [file.path, file.text]),
    ...[...folders].flatMap((folder): [string, string][] => {
      const doc = folderDoc(folder, paths);
      return [
        [`${folder}index.html`, html(doc, null)],
        [`${folder.slice(0, -1)}.md`, doc.markdown],
      ];
    }),
  ]);
  const site: Record<string, string> = {
    "index.html": html(home, first("index.md")),
    "index.md": source,
    ...pages,
    "404.html": html(missing, first("404.md")),
    // The README at the path GitHub gives it, so a link to it can be shared.
    "README.md": source,
    "404.md": `${notFound.trimEnd()}\n\nSee [llms.txt](${origin}/llms.txt) for what this site holds.\n`,
    "files.json": JSON.stringify(editor),
    "favicon.svg": favicon,
    "robots.txt": `User-agent: *\nAllow: /\n\nSitemap: ${origin}/sitemap.xml\n`,
    "sitemap.xml": `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n${urls.join("\n")}\n</urlset>\n`,
    "llms.txt": llms,
  };
  const taken = Object.keys(eukhe).filter((file) => file in site);
  if (taken.length > 0) throw new Error(`eukhe's files clash with the site's: ${taken.join(", ")}`);
  return { ...site, ...eukhe };
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
    // Over the images (cursorline, selection and a yank's flash cover them, as in a terminal);
    // a click passes to the image's link under it, and to the editor (client.ts reads the cell).
    pointerEvents: "none",
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
