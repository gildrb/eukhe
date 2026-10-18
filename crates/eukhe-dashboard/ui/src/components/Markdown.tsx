// Assistant prose: markdown-to-jsx renders straight to elements (no HTML
// strings, raw HTML stays text, URLs pass its sanitizer). Each element
// gets its style through `overrides`; code blocks get a header with the
// language and Copy.

import * as stylex from "@stylexjs/stylex";
import { Markdown, RuleType, type MarkdownToJSX } from "markdown-to-jsx/react";
import { createElement, memo } from "react";
import { colors, fonts, radius, space, type } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { CopyButton } from "./CopyButton.tsx";

function Link({ href, children }: { href?: string; children?: preact.ComponentChildren }) {
  return (
    <a
      href={href}
      target="_blank"
      rel="noopener noreferrer"
      {...stylex.props(ui.focusRing, md.link)}
    >
      {children}
    </a>
  );
}

/** Images from the web are not loaded (the CSP permits the app's own files only): their link shows. */
function Picture({ src, alt }: { src?: string; alt?: string }) {
  return src ? <Link href={src}>{alt || src}</Link> : <span>{alt}</span>;
}

function Table(props: { children?: preact.ComponentChildren }) {
  return (
    <div {...stylex.props(md.tableFrame)}>
      <table {...stylex.props(md.table)}>{props.children}</table>
    </div>
  );
}

function CodeBlock({ lang, text }: { lang: string; text: string }) {
  return (
    <figure {...stylex.props(md.code)}>
      <figcaption {...stylex.props(md.codeHead)}>
        <span translate={false}>{lang || "text"}</span>
        <CopyButton text={text} />
      </figcaption>
      <pre tabIndex={0} translate={false} {...stylex.props(ui.mono, md.pre)}>
        <code>{text}</code>
      </pre>
    </figure>
  );
}

const options = (streaming: boolean): MarkdownToJSX.Options => ({
  forceBlock: true,
  disableParsingRawHTML: true,
  optimizeForStreaming: streaming,
  // Its own element literals are React's; Preact builds every element instead (and so no wrapper).
  createElement: createElement as MarkdownToJSX.Options["createElement"],
  wrapper: null,
  overrides: {
    a: { component: Link },
    img: { component: Picture },
    table: { component: Table },
    p: { props: stylex.props(md.p) },
    h1: { props: stylex.props(md.heading) },
    h2: { props: stylex.props(md.heading) },
    h3: { props: stylex.props(md.heading) },
    h4: { props: stylex.props(md.heading) },
    h5: { props: stylex.props(md.heading) },
    h6: { props: stylex.props(md.heading) },
    ul: { props: stylex.props(md.list, md.bullets) },
    ol: { props: stylex.props(md.list) },
    li: { props: stylex.props(md.item) },
    blockquote: { props: stylex.props(md.quote) },
    hr: { props: stylex.props(md.rule) },
    code: { props: stylex.props(ui.mono, md.inline) },
    th: { props: stylex.props(md.cell, md.head) },
    td: { props: stylex.props(md.cell) },
    input: { props: stylex.props(md.task) },
  },
  renderRule(next, node, _children, state) {
    if (node.type === RuleType.codeBlock) {
      return <CodeBlock key={state.key} lang={node.lang ?? ""} text={node.text} />;
    }
    return next();
  },
});

// Built on first use: the styles they name are defined at the end of this module.
const built: Partial<Record<"settled" | "streaming", MarkdownToJSX.Options>> = {};

/** Rendered markdown; `streaming` hides half-written constructs at the end. */
export const Prose = memo(function Prose({
  text,
  streaming = false,
}: {
  text: string;
  streaming?: boolean;
}) {
  return (
    <div {...stylex.props(md.prose)}>
      <Markdown options={(built[streaming ? "streaming" : "settled"] ??= options(streaming))}>
        {text}
      </Markdown>
    </div>
  );
});

const md = stylex.create({
  prose: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x4,
    minWidth: 0,
    fontSize: type.text,
    lineHeight: type.proseLine,
    color: colors.primary,
    overflowWrap: "anywhere",
    fontFeatureSettings: '"liga" 1, "calt" 1',
  },
  p: { margin: 0 },
  heading: {
    margin: 0,
    marginTop: space.x2,
    fontSize: type.text,
    lineHeight: type.proseLine,
    fontWeight: 600,
  },
  link: {
    color: colors.primary,
    textDecorationLine: "underline",
    textDecorationThickness: "1px",
    textUnderlineOffset: "0.2em",
    textDecorationColor: colors.tertiary,
  },
  list: {
    margin: 0,
    paddingInlineStart: space.x6,
    display: "flex",
    flexDirection: "column",
    rowGap: space.x1,
  },
  bullets: { listStyleType: '"–  "' },
  item: { paddingInlineStart: space.x1, "::marker": { color: colors.tertiary } },
  quote: {
    margin: 0,
    paddingInlineStart: space.x4,
    borderInlineStartWidth: "2px",
    borderInlineStartStyle: "solid",
    borderInlineStartColor: colors.hairline,
    color: colors.secondary,
  },
  rule: {
    width: "100%",
    height: "1px",
    margin: 0,
    borderWidth: 0,
    backgroundColor: colors.hairline,
  },
  inline: {
    paddingInline: "4px",
    paddingBlock: "1px",
    borderRadius: radius.code,
    backgroundColor: colors.surface,
    fontSize: "0.875em",
  },
  code: {
    margin: 0,
    minWidth: 0,
    borderRadius: radius.control,
    backgroundColor: colors.surface,
    overflow: "hidden",
  },
  codeHead: {
    display: "flex",
    alignItems: "center",
    justifyContent: "space-between",
    paddingInlineStart: space.x4,
    paddingInlineEnd: space.x3,
    minHeight: "36px",
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: colors.tertiary,
    fontFamily: fonts.sans,
  },
  pre: {
    margin: 0,
    paddingInline: space.x4,
    paddingBottom: space.x4,
    overflowX: "auto",
    fontSize: type.small,
    lineHeight: "22px",
    whiteSpace: "pre",
    outline: "none",
  },
  tableFrame: { maxWidth: "100%", overflowX: "auto" },
  table: {
    borderCollapse: "collapse",
    minWidth: "100%",
    fontSize: type.small,
    lineHeight: type.smallLine,
  },
  cell: {
    paddingBlock: space.x2,
    paddingInlineEnd: space.x4,
    borderBottomWidth: "1px",
    borderBottomStyle: "solid",
    borderBottomColor: colors.hairline,
    textAlign: "start",
    verticalAlign: "top",
  },
  head: { fontWeight: 500, color: colors.secondary },
  task: {
    margin: 0,
    marginInlineEnd: space.x2,
    accentColor: colors.primary,
    verticalAlign: "-2px",
  },
});
