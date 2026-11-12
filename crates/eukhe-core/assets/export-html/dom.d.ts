// What the page around template.ts guarantees, as types: the elements template.html always
// contains, looked up by id, and the global the template adds to `window`. The DOM lib's
// `Document`, `Window` and `DateConstructor` take these overloads through interface merging,
// which a `type` alias cannot do; hence the interfaces.

/** The `session-data` script element. An element's `textContent` is never null. */
type SessionDataScript = HTMLScriptElement & { readonly textContent: string };

/** The `tree-search` input. Its `input` events target the input itself (it has no children). */
type TreeSearchInput = {
  addEventListener(type: "input", listener: (event: Event & { readonly target: HTMLInputElement }) => void): void;
} & HTMLInputElement;

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the DOM lib's Document
interface Document {
  getElementById(elementId: "session-data"): SessionDataScript;
  getElementById(elementId: "tree-search"): TreeSearchInput;
  getElementById(
    elementId: "sidebar-overlay" | "sidebar-resizer" | "tree-container" | "tree-status" | "header-container" | "messages",
  ): HTMLDivElement;
  /** `sidebar` is an `<aside>`, `content` a `<main>`. */
  getElementById(elementId: "sidebar" | "content"): HTMLElement;
  getElementById(elementId: "hamburger" | "sidebar-close"): HTMLButtonElement;
}

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the DOM lib's Window
interface Window {
  /** Null only in a document without a browsing context; the template runs in a page. */
  getSelection(): Selection;
  /** Set by template.ts; the header's download button calls it from its `onclick` attribute. */
  downloadSessionJson: () => void;
}

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the ES lib's DateConstructor
interface DateConstructor {
  /** `new Date(null)` is the epoch: a null converts to the time value 0. */
  new (value: string | null): Date;
}

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the DOM lib's URLSearchParams
interface URLSearchParams {
  /** The value is a USVString: a null converts to the text "null". */
  set(name: string, value: string | null): void;
}
