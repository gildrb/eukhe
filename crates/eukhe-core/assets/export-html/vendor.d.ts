// The globals the vendored scripts define before template.ts runs (template.html loads
// vendor/marked.min.js, then vendor/highlight.min.js, then the template): the parts of their
// APIs the template uses, typed after marked v15.0.4 and highlight.js v11.9.0.

/** A marked token (`Tokens.Generic`). */
type MarkedToken = { type: string; raw: string; text?: string; tokens?: MarkedToken[] };

/** marked `Tokens.Del`. */
type MarkedDelToken = { type: "del"; raw: string; text: string; tokens: MarkedToken[] };

/** marked `Tokens.Link`. */
type MarkedLinkToken = {
  type: "link";
  raw: string;
  href: string;
  title?: string | null;
  text: string;
  tokens: MarkedToken[];
};

/** marked `Tokens.Image`. */
type MarkedImageToken = { type: "image"; raw: string; href: string; title: string | null; text: string };

/** marked `Tokens.Code`. */
type MarkedCodeToken = {
  type: "code";
  raw: string;
  codeBlockStyle?: "indented";
  lang?: string;
  text: string;
  escaped?: boolean;
};

/** marked `Tokens.Codespan`. */
type MarkedCodespanToken = { type: "codespan"; raw: string; text: string };

/** `this` in a tokenizer override (marked `_Tokenizer`). */
type MarkedTokenizer = { lexer: { inlineTokens(src: string): MarkedToken[] } };

/** `this` in a renderer override (marked `_Renderer`). */
type MarkedRenderer = { parser: { parseInline(tokens: MarkedToken[]): string } };

/**
 * marked `MarkedExtension`, the options this template sets. A tokenizer override returns the
 * token, `undefined` for no token, or `false` to fall back to the built-in tokenizer; a renderer
 * override returns the HTML, or `false` to fall back.
 */
type MarkedExtension = {
  breaks?: boolean;
  gfm?: boolean;
  tokenizer?: {
    html?(this: MarkedTokenizer, src: string): MarkedToken | undefined | false;
    tag?(this: MarkedTokenizer, src: string): MarkedToken | undefined | false;
    del?(this: MarkedTokenizer, src: string): MarkedDelToken | undefined | false;
  };
  renderer?: {
    link?(this: MarkedRenderer, token: MarkedLinkToken): string | false;
    image?(this: MarkedRenderer, token: MarkedImageToken): string | false;
    code?(this: MarkedRenderer, token: MarkedCodeToken): string | false;
    codespan?(this: MarkedRenderer, token: MarkedCodespanToken): string | false;
  };
};

/** The `marked` global (vendor/marked.min.js, UMD). */
declare const marked: {
  use(...extensions: MarkedExtension[]): unknown;
  /** Synchronous: no extension sets `async: true`, so the result is the HTML, never a promise. */
  parse(src: string): string;
};

/** highlight.js `HighlightResult`. */
type HighlightResult = { value: string; language?: string; relevance: number; illegal: boolean };

/** The `hljs` global (vendor/highlight.min.js). */
declare const hljs: {
  /** Throws for a language it does not know. */
  highlight(code: string, options: { language: string; ignoreIllegals?: boolean }): HighlightResult;
  highlightAuto(code: string, languageSubset?: string[]): HighlightResult;
  /** The language definition, or undefined when none is registered under `name`. */
  getLanguage(name: string): object | undefined;
};
