import * as stylex from "@stylexjs/stylex";
import type { ComponentChildren } from "preact";
import { swatch } from "./source.ts";
import { colors, type } from "./tokens.stylex.ts";

/**
 * Markdown shown as Markdown: every character of the source stays on the page. Headings, links,
 * code and tables only gain weight, color and a working <a>.
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

/** Inline code and links: `[label](url)` keeps its brackets, and the URL is the link. */
function inline(text: string): ComponentChildren[] {
  const parts: ComponentChildren[] = [];
  const pattern = /`([^`]+)`|\[([^\]]+)\]\(([^)\s]+)\)/g;
  let last = 0;
  for (const match of text.matchAll(pattern)) {
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
  const comment = /(^|\s)#\s.*$/.exec(text);
  if (comment === null) return text;
  const start = comment.index + (comment[1]?.length ?? 0);
  return [text.slice(0, start), <span {...stylex.props(styles.muted)}>{text.slice(start)}</span>];
}

/** A table row: pipes and rules muted; a swatch takes the color named right after it. */
function tableRow(text: string): ComponentChildren {
  if (/^[|\s-]+$/.test(text)) return <span {...stylex.props(styles.muted)}>{text}</span>;
  return text.split(/(\|)/).map((cell) => {
    if (cell === "|") return <span {...stylex.props(styles.muted)}>|</span>;
    const painted = new RegExp(`^(\\s*)${swatch}( (oklch\\([^)]+\\)).*)$`).exec(cell);
    if (painted?.[1] === undefined || painted[2] === undefined || painted[3] === undefined)
      return cell;
    return [painted[1], <span style={{ color: painted[3] }}>{swatch}</span>, painted[2]];
  });
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
        return [previous?.$ === "Line" ? "\n" : "", line(item.line)];
      case "Block": {
        const blank = previous?.$ === "Line" && previous.line.text === "";
        return (
          <span {...stylex.props(styles.block, blank && styles.afterBlank)}>
            {item.lines.map((each, at) => [at === 0 ? "" : "\n", line(each)])}
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
 * The page: the header block (the lines before the first blank one) set tight with a blinking
 * cursor after its first line, the motto 80px below, then the document.
 */
export function Markdown({ source }: { source: string }) {
  const [head = "", motto = "", ...rest] = source.split("\n\n");
  const [title = "", ...subtitle] = head.split("\n");
  const groups = group(classify(rest.join("\n\n")));
  return (
    <pre {...stylex.props(styles.pre)}>
      <code {...stylex.props(styles.code)}>
        <span {...stylex.props(styles.header)}>
          <h1 {...stylex.props(styles.title)}>{title}</h1>{" "}
          <span aria-hidden="true" {...stylex.props(styles.cursor)}>
            █
          </span>
          {"\n"}
          {subtitle.join("\n")}
        </span>
        {"\n\n"}
        <span {...stylex.props(styles.spaced)}>{inline(motto)}</span>
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
    overflowWrap: "anywhere",
    fontFamily: "inherit",
    fontSize: "inherit",
    lineHeight: "inherit",
  },
  code: { fontFamily: "inherit", fontSize: "inherit", lineHeight: "inherit" },
  header: { display: "inline-block", lineHeight: "18px", color: colors.primary },
  block: { display: "block", overflowX: "auto", whiteSpace: "pre", overflowWrap: "normal" },
  afterBlank: { marginTop: type.leading },
  /** The page's name, an <h1> set as the line it sits on. */
  title: { display: "inline", margin: 0, fontSize: "inherit", fontWeight: "inherit" },
  cursor: {
    color: colors.primary,
    animationName: { default: flash, "@media (prefers-reduced-motion: reduce)": "none" },
    animationDuration: "1s",
    animationIterationCount: "infinite",
  },
  spaced: { display: "inline-block", marginTop: "80px" },
  muted: { color: colors.tertiary },
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
