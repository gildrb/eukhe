// The JS surface of the Bend core (`npm run bend` writes vim.mjs from vim/vim.bend). Bend values
// cross as they are: constructors as `{$: "Name", ...fields}`, `Nat` as a number, `Bool` as a
// boolean, `String` as a string, lists as `Con`/`Nil` cells. The editor state is opaque to the host.

export type BendList<T> = { $: "Nil" } | { $: "Con"; head: T; tail: BendList<T> };
export type Maybe<T> = { $: "None" } | { $: "Some"; value: T };

declare const editor: unique symbol;
/** The editor (vim/types.bend `St`): only the core reads it. */
export type St = { readonly [editor]: true };

export type Buf = { $: "Buf"; path: string; lines: BendList<string> };
export type Tgt = { $: "File"; i: number } | { $: "Dir"; path: string };
export type Cell = { $: "Cell"; row: number; col: number };
export type Span = { $: "Span"; row: number; col: number; len: number };
/** What a run of a float's cells is painted as. */
export type Group =
  | { $: "Border" }
  | { $: "Title" }
  | { $: "Sel" }
  | { $: "Match" }
  | { $: "Dim" }
  | { $: "Prompt" }
  | { $: "Count" }
  | { $: "Number" }
  | { $: "Thumb" };
/** A run of `len` cells from (row, col) of a float; later marks paint over earlier ones. */
export type Mark = { $: "Mark"; row: number; col: number; len: number; group: Group };
/** A float (a picker): screen position, size in cells, rows of text (borders included, each
 * `width` cells; U+1FABF (the goose) takes two cells, every other character one) and its marks. */
export type Float = {
  $: "Float";
  row: number;
  col: number;
  width: number;
  height: number;
  lines: BendList<string>;
  marks: BendList<Mark>;
};
export type Frame = {
  $: "Frame";
  tgt: Tgt;
  top: number;
  left: number;
  /** The screen column where text starts: sign column (file windows) and number column. */
  gutter: number;
  /** One per text row, each exactly `gutter` cells. */
  nums: BendList<string>;
  /** The cursor's screen cell (the prompt's caret while a picker is open). */
  cur: Cell;
  char: string;
  cmd: string;
  /** Search hits, in screen columns. */
  hits: BendList<Span>;
  bar: Span;
  /** Whether row `cur.row` shows the cursorline (false while a float has focus). */
  cl: boolean;
  /** The whole statusline row, exactly `cols` cells. */
  status: string;
  /** The screen column of 'colorcolumn' (100) when visible in a file window. */
  cc: Maybe<number>;
  float: Maybe<Float>;
};
export type Ev =
  | { $: "EvKey"; name: string }
  | { $: "EvClick"; row: number; col: number }
  | { $: "EvWheel"; down: boolean; notches: number }
  | { $: "EvSize"; rows: number; cols: number };
export type Act =
  | { $: "Nothing" }
  | { $: "OpenUrl"; url: string }
  | { $: "CopyText"; text: string };
export type Step = { $: "Step"; st: St; act: Act };

declare const Vim: {
  "Vim.init": (files: BendList<Buf>, rows: number, cols: number) => St;
  "Vim.step": (st: St, ev: Ev) => Step;
  "Vim.frame": (st: St) => Frame;
  "Vim.lines": (st: St) => BendList<string>;
};
export default Vim;
