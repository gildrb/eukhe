import * as stylex from "@stylexjs/stylex";
import type { ComponentChildren } from "preact";
import { escape, greekLine } from "./paint.ts";
import { type Placement, repository, served, type Shown } from "./rendered.ts";
import { colors, type } from "./tokens.stylex.ts";

/**
 * Markdown shown as Markdown: every character of the source stays on the page. Headings, links,
 * code and tables only gain weight, color and a working <a>. Each source line is one
 * `[data-l]` span (the vim cursor in `client.ts` counts on them). Left of a line, its number.
 */
type Line =
  | { $: "Heading"; marker: string; text: string; title: boolean; home: boolean }
  | { $: "Quote"; text: string }
  | { $: "Fence"; text: string }
  | { $: "Code"; text: string }
  | { $: "Table"; text: string }
  | { $: "Text"; text: string }
  | { $: "Raw"; text: string }
  | { $: "Art"; text: string; href: string };

/** A line and its 1-based number in the source. */
type Entry = { n: number; line: Line };

/**
 * Markdown: headings, `>` quotes, fences, tables, text. A page is named by its first `# ` heading;
 * on the site's own pages (`linkHome`: all but the home page) the name links home.
 */
function classify(source: string, plain: boolean, linkHome: boolean): Entry[] {
  const lines = source.split("\n");
  if (plain) return lines.map((text, index): Entry => ({ n: index + 1, line: { $: "Raw", text } }));
  let named = false;
  let fenced = false;
  // Inside a drawing that links (`<a href="…"><pre>` … `</pre></a>`): where it goes.
  let art: string | null = null;
  return lines.map((text, index): Entry => {
    const n = index + 1;
    if (art !== null) {
      if (text === "</pre></a>") {
        art = null;
        return { n, line: { $: "Raw", text } };
      }
      return { n, line: { $: "Art", text, href: art } };
    }
    const opens = /^<a href="([^"]+)"><pre>$/.exec(text)?.[1];
    if (opens !== undefined) {
      art = opens;
      return { n, line: { $: "Raw", text } };
    }
    if (text.startsWith("```")) {
      fenced = !fenced;
      return { n, line: { $: "Fence", text } };
    }
    if (fenced) return { n, line: { $: "Code", text } };
    const heading = /^(#{1,6} )(.*)$/.exec(text);
    if (heading?.[1] !== undefined && heading[2] !== undefined) {
      const title = !named && heading[1] === "# ";
      if (title) named = true;
      return {
        n,
        line: {
          $: "Heading",
          marker: heading[1],
          text: heading[2],
          title,
          home: title && linkHome,
        },
      };
    }
    if (text.startsWith("> ")) return { n, line: { $: "Quote", text: text.slice(2) } };
    if (text.startsWith("|")) return { n, line: { $: "Table", text } };
    return { n, line: { $: "Text", text } };
  });
}

/** Inline code and links. */
const inlinePattern = /`([^`]+)`|\[([^\]]+)\]\(([^)\s]+)\)/;
/** A trailing `# comment` on a shell line. */
const commentPattern = /(^|\s)#\s.*$/;
/** A table's rule row. */
const rulePattern = /^[|\s-]+$/;

/**
 * Where a link's URL goes from this site. The page is eukhe's README: its relative links
 * (`LICENSE`, `spec/rlm/`) are eukhe's files, which the site serves at the same paths.
 */
function linkHref(url: string): string {
  return /^([a-z][a-z0-9+.-]*:|\/|#)/i.test(url) ? url : `/${url}`;
}

/** Inline code and links: `[label](url)` keeps its brackets, and the URL is the link. */
function inline(text: string): ComponentChildren[] {
  const parts: ComponentChildren[] = [];
  let last = 0;
  for (const match of text.matchAll(new RegExp(inlinePattern, "g"))) {
    parts.push(text.slice(last, match.index));
    const [whole, code, label, url] = match;
    if (code !== undefined) {
      parts.push(<span {...stylex.props(styles.muted)}>`</span>, code);
      parts.push(<span {...stylex.props(styles.muted)}>`</span>);
    } else if (label !== undefined && url !== undefined) {
      const href = linkHref(url);
      const external = /^https?:/.test(href);
      parts.push(
        `[${label}](`,
        <a
          href={href}
          {...(external ? { target: "_blank", rel: "noopener" } : {})}
          {...stylex.props(styles.link)}
        >
          {url}
        </a>,
        ")",
      );
    }
    last = match.index + whole.length;
  }
  parts.push(text.slice(last));
  return parts;
}

/** A shell line: the text, and a trailing `# comment` in the muted color. */
function shellLine(text: string): ComponentChildren {
  const comment = commentPattern.exec(text);
  if (comment === null) return text;
  const start = comment.index + (comment[1]?.length ?? 0);
  return [text.slice(0, start), <span {...stylex.props(styles.muted)}>{text.slice(start)}</span>];
}

/** A table row: pipes and rules muted. */
function tableRow(text: string): ComponentChildren {
  if (rulePattern.test(text)) return <span {...stylex.props(styles.muted)}>{text}</span>;
  return text
    .split(/(\|)/)
    .map((cell) => (cell === "|" ? <span {...stylex.props(styles.muted)}>|</span> : cell));
}

/** After the page's name: without the script, the blinking cursor of a terminal; with it, the vim cursor. */
function deco(): ComponentChildren {
  return <span aria-hidden="true" data-deco="" {...stylex.props(styles.deco)} />;
}

function content(item: Line): ComponentChildren {
  switch (item.$) {
    case "Text":
      return inline(item.text);
    case "Heading": {
      // The page name is the <h1>; `#` sections are <h2>, deeper ones <h3>.
      const Tag = item.title ? "h1" : item.marker.length === 2 ? "h2" : "h3";
      const heading = (
        <Tag {...stylex.props(styles.heading)}>
          <span {...stylex.props(styles.muted)}>{item.marker}</span>
          {item.home ? (
            <a href="/" {...stylex.props(styles.link)}>
              {item.text}
            </a>
          ) : (
            item.text
          )}
        </Tag>
      );
      return item.title ? [heading, deco()] : heading;
    }
    case "Quote":
      return [<span {...stylex.props(styles.muted)}>{"> "}</span>, inline(item.text)];
    case "Fence":
      return <span {...stylex.props(styles.muted)}>{item.text}</span>;
    case "Code":
      return shellLine(item.text);
    case "Table":
      return tableRow(item.text);
    case "Raw":
      return item.text;
    case "Art":
      return (
        <a href={item.href} {...stylex.props(styles.art)}>
          {item.text}
        </a>
      );
    default: {
      const _: never = item;
      return _;
    }
  }
}

/**
 * What the page shows as one block: a source line as it is (heading, code, table), or
 * prose lines joined into one that wraps at the screen's width: a paragraph, a list item with its
 * indented continuation lines, a quote's sentence (a quote line ending in ".", ";" or "·" ends it).
 * The editor shows each source line whole; a phone wraps the blocks at its width.
 */
type Block =
  | { $: "One"; entry: Entry }
  | { $: "Blank" }
  | { $: "Para"; text: string }
  | { $: "Item"; indent: string; text: string }
  | { $: "Quote"; text: string };

const sentenceEnd = /[.;·]$/;

function toBlocks(entries: readonly Entry[]): Block[] {
  const out: Block[] = [];
  const last = () => out.at(-1);
  for (const entry of entries) {
    const line = entry.line;
    const prev = last();
    if (line.$ === "Text") {
      const item = /^( *)- (.*)$/.exec(line.text);
      if (line.text === "") out.push({ $: "Blank" });
      else if (item?.[1] !== undefined && item[2] !== undefined)
        out.push({ $: "Item", indent: item[1], text: item[2] });
      else if (prev?.$ === "Item" && line.text.startsWith("  "))
        prev.text = `${prev.text} ${line.text.trim()}`;
      else if (prev?.$ === "Para") prev.text = `${prev.text} ${line.text}`;
      else out.push({ $: "Para", text: line.text });
    } else if (line.$ === "Quote") {
      if (prev?.$ === "Quote" && !sentenceEnd.test(prev.text))
        prev.text = `${prev.text} ${line.text}`;
      else out.push({ $: "Quote", text: line.text });
    } else out.push({ $: "One", entry });
  }
  return out;
}

/** The commands of each fenced block, trailing `# comments` dropped, keyed by its opening fence. */
function fences(entries: readonly Entry[]): Map<number, { n: number; command: string }[]> {
  const blocks = new Map<number, { n: number; command: string }[]>();
  let open: { n: number; code: { n: number; command: string }[] } | null = null;
  for (const entry of entries) {
    if (entry.line.$ === "Fence") {
      if (open === null) open = { n: entry.n, code: [] };
      else {
        blocks.set(open.n, open.code);
        open = null;
      }
    } else if (open !== null && entry.line.$ === "Code")
      open.code.push({
        n: entry.n,
        command: entry.line.text.replace(commentPattern, "").trimEnd(),
      });
  }
  return blocks;
}

/**
 * A line of Ancient Greek's attributes (paint.ts `greekLine`): its language, and no translation. A
 * string record: preact types `translate` as a boolean, and renders no `translate="no"` from one.
 */
function greek(text: string): Readonly<Record<string, string>> {
  return greekLine(text) ? { lang: "grc", translate: "no" } : {};
}

/**
 * The page: one block per row group, each wrapping at the screen's width; list items and quotes
 * hang their marker. Each fence that opens commands gets a copy button for them.
 */
function body(entries: readonly Entry[], shown: Shown): ComponentChildren[] {
  const fenced = fences(entries);
  let images = 0;
  return toBlocks(entries).map((block) => {
    switch (block.$) {
      case "Blank":
        return <span {...stylex.props(styles.row)}> </span>;
      case "Para": {
        // The README's own HTML (a centred image and its caption), rendered: the README is this
        // repository's, read at build time; its images are the files the site serves for them, and
        // each image links the source.
        const html = /^<p\b[^>]*>(.*)<\/p>$/.exec(block.text)?.[1];
        if (html !== undefined)
          return (
            <span
              {...stylex.props(styles.row, styles.figure)}
              dangerouslySetInnerHTML={{
                __html: html.replaceAll(/<img\b[^>]*>/g, (img) => {
                  images += 1;
                  return `<a href="${repository}">${figure(img, shown, images === 1)}</a>`;
                }),
              }}
            />
          );
        return <span {...stylex.props(styles.row)}>{inline(block.text)}</span>;
      }
      case "Item":
        return (
          <span
            {...stylex.props(styles.row, block.indent === "" ? styles.hang : styles.hangNested)}
          >
            <span {...stylex.props(styles.muted)}>{`${block.indent}- `}</span>
            {inline(block.text)}
          </span>
        );
      case "Quote":
        return (
          <span {...greek(block.text)} {...stylex.props(styles.row, styles.hang)}>
            <span {...stylex.props(styles.muted)}>{"> "}</span>
            {inline(block.text)}
          </span>
        );
      case "One": {
        const { entry } = block;
        const code =
          entry.line.$ === "Code" ||
          entry.line.$ === "Table" ||
          entry.line.$ === "Raw" ||
          entry.line.$ === "Art";
        const text = "text" in entry.line ? entry.line.text : "";
        const commands = copied((fenced.get(entry.n) ?? []).map((c) => c.command))?.text ?? "";
        return (
          <span {...greek(text)} {...stylex.props(styles.row, code && styles.hang)}>
            {content(entry.line)}
            {commands !== "" ? (
              <button
                type="button"
                data-copy={commands}
                aria-label={`Copy ${commands}`}
                {...stylex.props(styles.copy)}
              >
                [copy]
              </button>
            ) : null}
          </span>
        );
      }
      default: {
        const _: never = block;
        return _;
      }
    }
  });
}

/** A highlight group of the editor's screen (client.ts paints each as a class). */
export type Hl = "title" | "muted" | "heading" | "link" | "bold" | "italic" | "code";

/** Characters from..to (code points, end exclusive) of a line drawn in a group. */
/** `href`: where a link run goes when it is not its own text (a page's name, linking home). */
export type Run = { from: number; to: number; hl: Hl; href?: string };

/**
 * A file as the editor holds it: its lines, each line's highlights, and its code blocks' `[copy]`:
 * the line it follows (the block's opening line) and the commands it copies.
 */
export type EditorFile = {
  path: string;
  lines: string[];
  runs: Run[][];
  copies: Copy[];
  images: Placement[];
  /** The home page: its Markdown and its images as served, to render again at a narrower width. */
  page: { source: string; shown: Shown; width: number; linkHome: boolean } | null;
};

/** Code points in a string: the editor's columns. */
function cellCount(text: string): number {
  return Array.from(text).length;
}

/** A run over the code points of `text` from UTF-16 index `start` to `end`. */
function span(text: string, start: number, end: number, hl: Hl): Run {
  return { from: cellCount(text.slice(0, start)), to: cellCount(text.slice(0, end)), hl };
}

/** Inline code ticks muted, link URLs as links; `offset` is where `text` starts in its line. */
function inlineRuns(text: string, offset: number): Run[] {
  const runs: Run[] = [];
  for (const match of text.matchAll(new RegExp(inlinePattern, "g"))) {
    const [whole, code, label, url] = match;
    const at = match.index;
    if (code !== undefined) {
      runs.push(
        span(text, at, at + 1, "muted"),
        span(text, at + whole.length - 1, at + whole.length, "muted"),
      );
    } else if (label !== undefined && url !== undefined) {
      // The URL as written: the editor opens a relative one itself (`client.ts`, gf).
      runs.push(span(text, at + label.length + 3, at + whole.length - 1, "link"));
    }
  }
  return runs.map((run) => ({ ...run, from: run.from + offset, to: run.to + offset }));
}

/** The highlights of one line: the same rules as the page's styles. */
function lineRuns(item: Line): Run[] {
  switch (item.$) {
    case "Text":
      return inlineRuns(item.text, 0);
    case "Heading": {
      const marker = cellCount(item.marker);
      const to = marker + cellCount(item.text);
      return [
        { from: 0, to: marker, hl: "muted" },
        { from: marker, to, hl: "heading" },
        ...(item.home ? [{ from: marker, to, hl: "link" as const, href: "/" }] : []),
      ];
    }
    case "Quote":
      return [{ from: 0, to: 2, hl: "muted" }, ...inlineRuns(item.text, 2)];
    case "Fence":
      return [{ from: 0, to: cellCount(item.text), hl: "muted" }];
    case "Code": {
      const comment = commentPattern.exec(item.text);
      if (comment === null) return [];
      return [
        span(item.text, comment.index + (comment[1]?.length ?? 0), item.text.length, "muted"),
      ];
    }
    case "Table": {
      if (rulePattern.test(item.text)) return [{ from: 0, to: cellCount(item.text), hl: "muted" }];
      const runs: Run[] = [];
      for (const pipe of item.text.matchAll(/\|/g))
        runs.push(span(item.text, pipe.index, pipe.index + 1, "muted"));
      return runs;
    }
    case "Raw":
      return [];
    case "Art": {
      const to = cellCount(item.text);
      return to === 0 ? [] : [{ from: 0, to, hl: "heading", href: item.href }];
    }
    default: {
      const _: never = item;
      return _;
    }
  }
}

/** A code block's `[copy]`: after its opening line (0-based), its commands, one a line. */
export type Copy = { line: number; at: number; text: string };

/**
 * What a block's `[copy]` copies: its first command that is not a `cd` (the reader's own folder),
 * so the install block gives the install command and the use block `eukhe`; its index in `commands`.
 */
export function copied(commands: readonly string[]): { index: number; text: string } | null {
  const index = commands.findIndex((c) => c !== "" && !/^cd(\s|$)/.test(c));
  const text = commands[index];
  return text === undefined ? null : { index, text };
}

/** Each code block that holds a command: its `[copy]`. */
function copyFences(entries: readonly Entry[]): Copy[] {
  return [...fences(entries)].flatMap(([n, code]) => {
    const pick = copied(code.map((c) => c.command));
    const line = code[pick?.index ?? -1];
    return pick === null || line === undefined
      ? []
      : [{ line: n - 1, at: line.n - 1, text: pick.text }];
  });
}

/** A file for the editor: Markdown gets the page's highlights. */
export function editorFile(
  path: string,
  source: string,
  plain: boolean,
  linkHome: boolean,
): EditorFile {
  const text = source.replace(/\n$/, "");
  const entries = classify(text, plain, linkHome);
  return {
    path,
    lines: text.split("\n"),
    runs: entries.map((entry) => lineRuns(entry.line)),
    copies: plain ? [] : copyFences(entries),
    images: [],
    page: null,
  };
}

/**
 * A README `<img>` as the page shows it: the served file, its width and height, and the page's
 * first image fetched first (its largest paint), the others when they come near.
 */
function figure(img: string, shown: Shown, first: boolean): string {
  const attr = (name: string) => new RegExp(`\\b${name}="([^"]*)"`).exec(img)?.[1];
  const width = Number(attr("width") ?? "640");
  const file = served(attr("src") ?? "", width, shown);
  const alt = attr("alt") ?? "";
  return `<img src="${escape(file.src)}" alt="${alt}" width="${width}" height="${file.height}" ${first ? 'fetchpriority="high"' : 'loading="lazy"'}>`;
}

/** The page (and the 404 page) as Markdown, for phones and browsers without the script. */
export function Markdown({
  source,
  linkHome,
  shown,
}: {
  source: string;
  linkHome: boolean;
  shown: Shown;
}) {
  const entries = classify(source.replace(/\n$/, ""), false, linkHome);
  return (
    <pre {...stylex.props(styles.pre)}>
      <code {...stylex.props(styles.code)}>{body(entries, shown)}</code>
    </pre>
  );
}

const flash = stylex.keyframes({
  "0%, 50%": { opacity: 1 },
  "51%, 100%": { opacity: 0 },
});

const styles = stylex.create({
  pre: {
    margin: 0,
    maxWidth: type.measure,
    whiteSpace: "pre-wrap",
    textWrap: "pretty",
    overflowWrap: "anywhere",
    fontFamily: "inherit",
    fontSize: "inherit",
    lineHeight: "inherit",
  },
  code: { fontFamily: "inherit", fontSize: "inherit", lineHeight: "inherit" },
  /** A drawing in characters that links: the text's color and weight, no underline. */
  art: { color: colors.primary, fontWeight: type.bold, textDecoration: "none" },
  /** A block one character wide, a space after the name: drawn, not a glyph (no extra font). */
  deco: {
    display: "inline-block",
    width: "1ch",
    height: "1.15em",
    marginLeft: "1ch",
    verticalAlign: "text-bottom",
    backgroundColor: colors.primary,
    userSelect: "none",
    animationName: { default: flash, "@media (prefers-reduced-motion: reduce)": "none" },
    animationDuration: "1s",
    animationIterationCount: "infinite",
  },
  muted: { color: colors.tertiary },
  /** A centred figure (the README's `<p align="center">`): its image no wider than the page. */
  figure: { textAlign: "center" },
  /** A row of the page: one block, wrapping at the screen's width; an empty one keeps its line. */
  row: { display: "block", minHeight: type.leading },
  /** A list item, a quote or a code line: wrapped lines start under the text, not the marker. */
  hang: { paddingLeft: "2ch", textIndent: "-2ch" },
  /** A nested list item: its marker under the parent's text. */
  hangNested: { paddingLeft: "4ch", textIndent: "-4ch" },
  /** `[copy]` two characters after a fence; not part of the text, so never selected. */
  copy: {
    marginLeft: "2ch",
    padding: 0,
    borderWidth: 0,
    backgroundColor: "transparent",
    fontFamily: "inherit",
    fontSize: "inherit",
    lineHeight: "inherit",
    color: { default: colors.article, ":hover": colors.primary, ":focus-visible": colors.primary },
    textDecorationLine: "underline",
    textDecorationColor: { default: colors.tertiary, ":hover": colors.primary },
    textUnderlineOffset: "3px",
    cursor: "pointer",
    userSelect: "none",
    transitionProperty: "color, text-decoration-color",
    transitionDuration: "150ms",
    transitionTimingFunction: "cubic-bezier(0.4, 0, 0.2, 1)",
    outline: { default: null, ":focus-visible": `1px solid ${colors.primary}` },
    outlineOffset: "2px",
  },
  heading: {
    display: "inline",
    margin: 0,
    fontSize: "inherit",
    fontWeight: type.bold,
    color: colors.primary,
  },
  link: {
    color: { default: "inherit", ":hover": colors.primary, ":focus-visible": colors.primary },
    textDecorationColor: { default: colors.tertiary, ":hover": colors.primary },
    textUnderlineOffset: "3px",
    // gildrb.com's hover: both ways, 150ms.
    transitionProperty: "color, text-decoration-color",
    transitionDuration: "150ms",
    transitionTimingFunction: "cubic-bezier(0.4, 0, 0.2, 1)",
    outline: { default: null, ":focus-visible": `1px solid ${colors.primary}` },
    outlineOffset: "2px",
  },
});
