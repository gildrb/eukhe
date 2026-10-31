import * as stylex from "@stylexjs/stylex";
import type { ComponentChildren } from "preact";
import { swatch } from "./source.ts";
import { colors, type Token, type } from "./tokens.stylex.ts";

/**
 * Markdown shown as Markdown: every character of the source stays on the page. Headings, links,
 * code and tables only gain weight, color and a working <a>. Right of each line, its inks: the
 * color tokens it is drawn in, each name in its own color (`Inks`).
 */
type Line =
  | { $: "Heading"; marker: string; text: string }
  | { $: "Fence"; text: string }
  | { $: "Code"; text: string }
  | { $: "Table"; text: string }
  | { $: "Text"; text: string };

function classify(source: string): Line[] {
  let fenced = false;
  return source.split("\n").map((text): Line => {
    if (text.startsWith("```")) {
      fenced = !fenced;
      return { $: "Fence", text };
    }
    if (fenced) return { $: "Code", text };
    const heading = /^(#{1,6} )(.*)$/.exec(text);
    if (heading?.[1] !== undefined && heading[2] !== undefined)
      return { $: "Heading", marker: heading[1], text: heading[2] };
    if (text.startsWith("|")) return { $: "Table", text };
    return { $: "Text", text };
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
    return [painted[1], <span style={{ color: painted[3] }}>{swatch}</span>, painted[2]];
  });
}

/** The tokens a line is drawn in, in the order they first appear; the same rules as above. */
function inks(item: Line): Token[] {
  switch (item.$) {
    case "Heading":
      return ["tertiary", "primary"];
    case "Fence":
      return ["tertiary"];
    case "Code":
      return commentPattern.test(item.text) ? ["article", "tertiary"] : ["article"];
    case "Table":
      return rulePattern.test(item.text) ? ["tertiary"] : ["tertiary", "article"];
    case "Text":
      if (item.text === "") return [];
      return inlinePattern.test(item.text) ? ["article", "tertiary"] : ["article"];
    default: {
      const _: never = item;
      return _;
    }
  }
}

/**
 * The inks of one line or of a block's lines, set in a column right of the text, from the top of
 * the line it is placed in. Not part of the text: hidden from selection and assistive technology,
 * and from screens too narrow for the column.
 */
function Inks({ rows }: { rows: readonly (readonly Token[])[] }) {
  if (rows.every((row) => row.length === 0)) return null;
  return (
    <span aria-hidden="true" data-inks="" {...stylex.props(styles.anchor)}>
      <span {...stylex.props(styles.inks)}>
        {rows.map((row, at) => [
          at === 0 ? "" : "\n",
          row.map((token, index) => [
            index === 0 ? "" : " ",
            <span {...stylex.props(ink[token])}>{token}</span>,
          ]),
        ])}
      </span>
    </span>
  );
}

function line(item: Line): ComponentChildren {
  switch (item.$) {
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
    case "Fence":
      return <span {...stylex.props(styles.muted)}>{item.text}</span>;
    case "Code":
      return shellLine(item.text);
    case "Table":
      return tableRow(item.text);
    case "Text":
      return inline(item.text);
    default: {
      const _: never = item;
      return _;
    }
  }
}

/** A code fence or a table: kept on its lines and scrolled sideways when wider than the page. */
type Group = { $: "Line"; line: Line } | { $: "Block"; lines: Line[] };

function group(lines: readonly Line[]): Group[] {
  const groups: Group[] = [];
  let open: Line[] | null = null;
  for (const item of lines) {
    const last = groups.at(-1);
    if (open !== null) {
      open.push(item);
      if (item.$ === "Fence") open = null;
    } else if (item.$ === "Fence") {
      open = [item];
      groups.push({ $: "Block", lines: open });
    } else if (item.$ === "Table" && last?.$ === "Block" && last.lines[0]?.$ === "Table") {
      last.lines.push(item);
    } else if (item.$ === "Table") {
      groups.push({ $: "Block", lines: [item] });
    } else {
      groups.push({ $: "Line", line: item });
    }
  }
  return groups;
}

/**
 * Lines join with a newline; a block sits on its own lines. The newline that ends the text before a
 * block draws no line of its own, so a blank line there becomes the block's top margin: the page
 * looks like the source, and copies as the source.
 */
function body(groups: readonly Group[]): ComponentChildren[] {
  return groups.map((item, index) => {
    const previous = groups[index - 1];
    switch (item.$) {
      case "Line":
        return [
          previous?.$ === "Line" ? "\n" : "",
          <Inks rows={[inks(item.line)]} />,
          line(item.line),
        ];
      case "Block": {
        const blank = previous?.$ === "Line" && previous.line.text === "";
        // A fenced block's commands, as the copy button hands them over.
        const code = item.lines
          .filter((each) => each.$ === "Code")
          .map((each) => each.text)
          .join("\n");
        return (
          <span {...stylex.props(styles.block, styles.anchor, blank && styles.afterBlank)}>
            <Inks rows={item.lines.map(inks)} />
            <span {...stylex.props(styles.scroll)}>
              {item.lines.map((each, at) => [
                at === 0 ? "" : "\n",
                line(each),
                at === 0 && each.$ === "Fence" ? (
                  <button
                    type="button"
                    data-copy={code}
                    aria-label="Copy the commands"
                    {...stylex.props(styles.copy)}
                  >
                    [copy]
                  </button>
                ) : null,
              ])}
            </span>
          </span>
        );
      }
      default: {
        const _: never = item;
        return _;
      }
    }
  });
}

/**
 * The page: the header block (the lines before the first blank one) with a blinking cursor after
 * its first line, the motto after one blank line, then the document. One 20px line throughout.
 */
export function Markdown({ source }: { source: string }) {
  const [head = "", motto = "", ...rest] = source.split("\n\n");
  const [title = "", ...subtitle] = head.split("\n");
  const groups = group(classify(rest.join("\n\n")));
  return (
    <pre {...stylex.props(styles.pre)}>
      <code {...stylex.props(styles.code)}>
        <span
          style={{ "--header-chars": Math.max(...head.split("\n").map((each) => each.length)) }}
          {...stylex.props(styles.header)}
        >
          <Inks rows={[title, ...subtitle].map((): Token[] => ["primary"])} />
          <h1 {...stylex.props(styles.title)}>{title}</h1>{" "}
          <span aria-hidden="true" {...stylex.props(styles.cursor)}>
            █
          </span>
          {"\n"}
          {subtitle.join("\n")}
        </span>
        {"\n\n"}
        <span {...stylex.props(styles.anchor)}>
          <Inks rows={[inks({ $: "Text", text: motto })]} />
          {inline(motto)}
        </span>
        {"\n\n"}
        {body(groups)}
      </code>
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
   * The header never wraps: on a screen narrower than its longest line (`--header-chars`, 0.6em
   * each) its type shrinks to fit the column (`main` is the container); its lines stay 20px.
   */
  header: {
    display: "inline-block",
    whiteSpace: "pre",
    fontSize: `min(${type.size}, 100cqi / (0.6 * var(--header-chars)))`,
    color: colors.primary,
    position: "relative",
  },
  block: { display: "block" },
  /** A block's lines keep their length and scroll sideways when wider than the column. */
  scroll: { display: "block", overflowX: "auto", whiteSpace: "pre", overflowWrap: "normal" },
  /** Places `inks` at the start of its line. */
  anchor: { position: "relative" },
  /** Two characters right of the 68-character measure; shown from 720px, where it fits. */
  inks: {
    position: "absolute",
    top: 0,
    left: `calc(${type.measure} + 2ch)`,
    display: { default: "none", "@media (min-width: 720px)": "block" },
    whiteSpace: "pre",
    fontWeight: 400,
    userSelect: "none",
    pointerEvents: "none",
  },
  afterBlank: { marginTop: type.leading },
  /** The page's name, an <h1> set as the line it sits on. */
  title: { display: "inline", margin: 0, fontSize: "inherit", fontWeight: "inherit" },
  cursor: {
    color: colors.primary,
    animationName: { default: flash, "@media (prefers-reduced-motion: reduce)": "none" },
    animationDuration: "1s",
    animationIterationCount: "infinite",
  },
  muted: { color: colors.tertiary },
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

/** Each token's name in its own color. */
const ink = stylex.create({
  bg: { color: colors.bg },
  primary: { color: colors.primary },
  article: { color: colors.article },
  tertiary: { color: colors.tertiary },
});
