import * as stylex from "@stylexjs/stylex";
import type { ComponentChildren } from "preact";
import { install, swatch } from "./source.ts";
import { colors, type Token, type } from "./tokens.stylex.ts";

/**
 * Markdown shown as Markdown: every character of the source stays on the page. Headings, links,
 * code and tables only gain weight, color and a working <a>. Each source line is one
 * `[data-l]` span (the vim cursor in `client.ts` counts on them). Left of a line, its number;
 * right of it, its inks: the color tokens it is drawn in, each name in its own color.
 */
type Line =
  | { $: "Header"; text: string; first: boolean }
  | { $: "Motto"; text: string }
  | { $: "Heading"; marker: string; text: string }
  | { $: "Quote"; text: string }
  | { $: "Fence"; text: string }
  | { $: "Code"; text: string }
  | { $: "Table"; text: string }
  | { $: "Text"; text: string }
  | { $: "Raw"; text: string };

/** A line and its 1-based number in the source. */
type Entry = { n: number; line: Line };

/**
 * The lines before the first blank one are the header, the next text line the motto; then
 * Markdown: headings, `>` quotes, fences, tables, text.
 */
function classify(source: string, plain: boolean): Entry[] {
  const lines = source.split("\n");
  if (plain) return lines.map((text, index): Entry => ({ n: index + 1, line: { $: "Raw", text } }));
  const headerEnd = lines.indexOf("");
  const motto = lines.findIndex((text, index) => index > headerEnd && text !== "");
  let fenced = false;
  return lines.map((text, index): Entry => {
    const n = index + 1;
    if (index < headerEnd) return { n, line: { $: "Header", text, first: index === 0 } };
    if (index === motto) return { n, line: { $: "Motto", text } };
    if (text.startsWith("```")) {
      fenced = !fenced;
      return { n, line: { $: "Fence", text } };
    }
    if (fenced) return { n, line: { $: "Code", text } };
    const heading = /^(#{1,6} )(.*)$/.exec(text);
    if (heading?.[1] !== undefined && heading[2] !== undefined)
      return { n, line: { $: "Heading", marker: heading[1], text: heading[2] } };
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
      const external = /^https?:/.test(url);
      parts.push(
        `[${label}](`,
        <a
          href={url}
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

/** A table row: pipes and rules muted; a swatch takes the color named right after it. */
function tableRow(text: string): ComponentChildren {
  if (rulePattern.test(text)) return <span {...stylex.props(styles.muted)}>{text}</span>;
  return text.split(/(\|)/).map((cell) => {
    if (cell === "|") return <span {...stylex.props(styles.muted)}>|</span>;
    const painted = new RegExp(`^(\\s*)${swatch}( (oklch\\([^)]+\\)).*)$`).exec(cell);
    if (painted?.[1] === undefined || painted[2] === undefined || painted[3] === undefined)
      return cell;
    return [
      painted[1],
      <span key="swatch" style={{ color: painted[3] }}>
        {swatch}
      </span>,
      painted[2],
    ];
  });
}

/** The tokens a line is drawn in, in the order they first appear; the same rules as above. */
function inks(item: Line): Token[] {
  switch (item.$) {
    case "Header":
      return ["primary"];
    case "Heading":
      return ["tertiary", "primary"];
    case "Quote":
      return ["tertiary", "article"];
    case "Fence":
      return ["tertiary"];
    case "Code":
      return commentPattern.test(item.text) ? ["article", "tertiary"] : ["article"];
    case "Table":
      return rulePattern.test(item.text) ? ["tertiary"] : ["tertiary", "article"];
    case "Raw":
      return item.text === "" ? [] : ["article"];
    case "Motto":
    case "Text":
      if (item.text === "") return [];
      return inlinePattern.test(item.text) ? ["article", "tertiary"] : ["article"];
    default: {
      const _: never = item;
      return _;
    }
  }
}

function content(item: Line): ComponentChildren {
  switch (item.$) {
    case "Header":
      return item.first
        ? [
            <h1 {...stylex.props(styles.title)}>{item.text}</h1>,
            // Without the script: the blinking cursor of a terminal. With it, the vim cursor.
            <span aria-hidden="true" data-deco="" {...stylex.props(styles.deco)} />,
          ]
        : item.text;
    case "Motto":
    case "Text":
      return inline(item.text);
    case "Heading": {
      // The page name is the <h1>; `#` sections are <h2>, deeper ones <h3>.
      const Tag = item.marker.length === 2 ? "h2" : "h3";
      return (
        <Tag {...stylex.props(styles.heading)}>
          <span {...stylex.props(styles.muted)}>{item.marker}</span>
          {item.text}
        </Tag>
      );
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
    default: {
      const _: never = item;
      return _;
    }
  }
}

/**
 * What the page shows as one block: a source line as it is (header, heading, code, table), or
 * prose lines joined into one that wraps at the screen's width: a paragraph, a list item with its
 * indented continuation lines, a quote's sentence (a quote line ending in ".", ";" or "·" ends it).
 * The source is hard-wrapped at 68 columns for the editor; a phone is narrower.
 */
type Block =
  | { $: "One"; entry: Entry }
  | { $: "Blank" }
  | { $: "Para"; text: string }
  | { $: "Item"; text: string }
  | { $: "Quote"; text: string };

const sentenceEnd = /[.;·]$/;

function toBlocks(entries: readonly Entry[]): Block[] {
  const out: Block[] = [];
  const last = () => out.at(-1);
  for (const entry of entries) {
    const line = entry.line;
    const prev = last();
    if (line.$ === "Text") {
      if (line.text === "") out.push({ $: "Blank" });
      else if (line.text.startsWith("- ")) out.push({ $: "Item", text: line.text.slice(2) });
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

/** The commands of each fenced block, keyed by its opening fence's line number. */
function fences(entries: readonly Entry[]): Map<number, string> {
  const blocks = new Map<number, string>();
  let open: { n: number; code: string[] } | null = null;
  for (const entry of entries) {
    if (entry.line.$ === "Fence") {
      if (open === null) open = { n: entry.n, code: [] };
      else {
        blocks.set(open.n, open.code.join("\n"));
        open = null;
      }
    } else if (open !== null && entry.line.$ === "Code") open.code.push(entry.line.text);
  }
  return blocks;
}

/**
 * The page: one block per row group, each wrapping at the screen's width; list items and quotes
 * hang their marker. Only the install command's fence gets a copy button (`source.ts`).
 */
function body(entries: readonly Entry[]): ComponentChildren[] {
  const fenced = fences(entries);
  return toBlocks(entries).map((block) => {
    switch (block.$) {
      case "Blank":
        return <span {...stylex.props(styles.row)}> </span>;
      case "Para":
        return <span {...stylex.props(styles.row)}>{inline(block.text)}</span>;
      case "Item":
        return (
          <span {...stylex.props(styles.row, styles.hang)}>
            <span {...stylex.props(styles.muted)}>{"- "}</span>
            {inline(block.text)}
          </span>
        );
      case "Quote":
        return (
          <span {...stylex.props(styles.row, styles.hang)}>
            <span {...stylex.props(styles.muted)}>{"> "}</span>
            {inline(block.text)}
          </span>
        );
      case "One": {
        const { entry } = block;
        const header = entry.line.$ === "Header";
        const code = entry.line.$ === "Code" || entry.line.$ === "Table" || entry.line.$ === "Raw";
        return (
          <span {...stylex.props(styles.row, header && styles.header, code && styles.hang)}>
            {content(entry.line)}
            {fenced.get(entry.n) === install ? (
              <button
                type="button"
                data-copy={install}
                aria-label="Copy the install command"
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
export type Hl = "title" | "muted" | "heading" | "link" | { color: string };

/** Characters from..to (code points, end exclusive) of a line drawn in a group. */
export type Run = { from: number; to: number; hl: Hl };

/**
 * A file as the editor holds it: its lines, each line's highlights, the page's inks, and the line
 * of the install command's opening fence (`[copy]` follows it), if the file holds one.
 */
export type EditorFile = {
  path: string;
  lines: string[];
  runs: Run[][];
  inks: Token[][] | null;
  copy: number | null;
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
    const [whole, code, label] = match;
    const at = match.index;
    if (code !== undefined) {
      runs.push(
        span(text, at, at + 1, "muted"),
        span(text, at + whole.length - 1, at + whole.length, "muted"),
      );
    } else if (label !== undefined) {
      runs.push(span(text, at + label.length + 3, at + whole.length - 1, "link"));
    }
  }
  return runs.map((run) => ({ ...run, from: run.from + offset, to: run.to + offset }));
}

/** The highlights of one line: the same rules as the page's styles. */
function lineRuns(item: Line): Run[] {
  switch (item.$) {
    case "Header":
      return [{ from: 0, to: cellCount(item.text), hl: "title" }];
    case "Motto":
    case "Text":
      return inlineRuns(item.text, 0);
    case "Heading": {
      const marker = cellCount(item.marker);
      return [
        { from: 0, to: marker, hl: "muted" },
        { from: marker, to: marker + cellCount(item.text), hl: "heading" },
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
      for (const painted of item.text.matchAll(
        new RegExp(`${swatch}(?= (oklch\\([^)]+\\)))`, "g"),
      )) {
        const color = painted[1];
        if (color !== undefined)
          runs.push(span(item.text, painted.index, painted.index + swatch.length, { color }));
      }
      return runs;
    }
    case "Raw":
      return [];
    default: {
      const _: never = item;
      return _;
    }
  }
}

/** The 0-based line of the install command's opening fence. */
function copyFence(entries: readonly Entry[]): number | null {
  for (const [n, code] of fences(entries)) if (code === install) return n - 1;
  return null;
}

/** A file for the editor: Markdown gets the page's highlights; `inks` only for the page. */
export function editorFile(path: string, source: string, plain: boolean): EditorFile {
  const text = source.replace(/\n$/, "");
  const entries = classify(text, plain);
  return {
    path,
    lines: text.split("\n"),
    runs: entries.map((entry) => lineRuns(entry.line)),
    inks: path === "index.md" ? entries.map((entry) => inks(entry.line)) : null,
    copy: plain ? null : copyFence(entries),
  };
}

/** The page (and the 404 page) as Markdown, for phones and browsers without the script. */
export function Markdown({ source }: { source: string }) {
  const entries = classify(source.replace(/\n$/, ""), false);
  const headerChars = Math.max(
    0,
    ...entries.map((entry) => (entry.line.$ === "Header" ? entry.line.text.length + 2 : 0)),
  );
  return (
    <pre style={{ "--header-chars": headerChars }} {...stylex.props(styles.pre)}>
      <code {...stylex.props(styles.code)}>{body(entries)}</code>
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
  /**
   * Header lines never wrap: on a screen narrower than the longest (`--header-chars`, 0.6em each)
   * their type shrinks to fit the column (`main` is the container); their lines stay 20px.
   */
  header: {
    whiteSpace: "pre",
    fontSize: `min(${type.size}, 100cqi / (0.6 * var(--header-chars)))`,
    color: colors.primary,
  },
  /** The page's name, an <h1> set as the line it sits on. */
  title: { display: "inline", margin: 0, fontSize: "inherit", fontWeight: "inherit" },
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
  /** A row of the page: one block, wrapping at the screen's width; an empty one keeps its line. */
  row: { display: "block", minHeight: type.leading },
  /** A list item, a quote or a code line: wrapped lines start under the text, not the marker. */
  hang: { paddingLeft: "2ch", textIndent: "-2ch" },
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
