import * as stylex from "@stylexjs/stylex";
import { renderToString } from "preact-render-to-string";
import { Markdown } from "./markdown.tsx";
import { notFound, source } from "./source.ts";
import { colors, palette, type } from "./tokens.stylex.ts";

export const origin = "https://eukhe.com";

const title = "eukhe";
const description =
  "A coding agent whose memory is one endless chat log, shared by all sessions. curl -fsSL https://eukhe.com/install | sh";

const fonts = [
  { file: "/fonts/IoskeleyMono-Regular.woff2", weight: 400 },
  { file: "/fonts/IoskeleyMono-Bold.woff2", weight: 700 },
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
].join("");

/** The favicon: the header's cursor, one block, in each theme's `primary`. */
export const favicon = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 32 32"><style>rect{fill:${palette.primary.dark}}@media (prefers-color-scheme:light){rect{fill:${palette.primary.light}}}</style><rect x="9" y="4" width="14" height="24"/></svg>\n`;

function Page({ css, markdown, path }: { css: string; markdown: string; path: string }) {
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
          <Markdown source={markdown} />
        </main>
      </body>
    </html>
  );
}

/** Every file the site serves, by path under `dist/`, from the StyleX CSS of this build. */
export function render(css: string): Record<string, string> {
  const html = (markdown: string, path: string) =>
    `<!doctype html>\n${renderToString(<Page css={css} markdown={markdown} path={path} />)}\n`;
  return {
    "index.html": html(source, "/"),
    "index.md": source,
    "404.html": html(notFound, "/404"),
    "favicon.svg": favicon,
    "robots.txt": `User-agent: *\nAllow: /\n\nSitemap: ${origin}/sitemap.xml\n`,
    "sitemap.xml": `<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">\n  <url><loc>${origin}/</loc></url>\n</urlset>\n`,
    "llms.txt": source,
  };
}

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
});
