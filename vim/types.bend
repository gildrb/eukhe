# eukhe.com's Neovim: the types
# =============================
#
# One value, St, holds the whole editor. Vim.step (vim.bend) changes it,
# one event at a time; Vim.frame (screen.bend) says what the screen shows.

import Base

# a place in a buffer: a line and a column, both from 0; a column counts
# characters, not bytes
type Pos is Data:
  Pos{line: Nat, col: Nat}

# the column j and k aim for: a column, or the end of every line after $
type Want is Data:
  Col{n: Nat}
  End{}

# a file the editor holds: its path from the site's root ("index.md",
# "docs/install.md") and its lines, at least one
type Buf is Data:
  Buf{path: String, lines: List<&2, String>}

# what the window shows: file number i, or a folder's listing (Oil), its
# path "" for the root or "docs/"
type Tgt is Data:
  File{i: Nat}
  Dir{path: String}

# the window: what it shows, the cursor, the column j and k aim for, and
# the first line and column on screen
type Win is Data:
  Win{tgt: Tgt, cur: Pos, want: Want, top: Nat, left: Nat}

# a picker: fff's files and live grep, fzf-lua's buffers and buffer lines
type Pick is Data:
  FFiles{}
  FGrep{}
  ZBufs{}
  ZLines{}

# a picker's item: what opening it shows, where the cursor goes, its text
# (a path, a matched line, a buffer's line) and the columns of text the
# query matched
type Item is Data:
  Item{tgt: Tgt, pos: Pos, text: String, hits: List<&2, Nat>}

# what the command line takes: an Ex command (:), a search forward (/) or
# back (?)
type Line is Data:
  Colon{}
  Slash{}
  Quest{}

# the mode: normal, typing on the command line, or a picker with its
# query, its items (the ones listed, at most a page for fff), how many
# match in all, the selected item, the first item on screen and the
# preview's scroll (lines)
type Mode is Data:
  Normal{}
  Typing{kind: Line, text: String}
  Picking{kind: Pick, query: String, items: List<&2, Item>, n: Nat, sel: Nat, top: Nat, pv: Nat}

# a key that waits for the next one: g, z, the leader (Space), leader f,
# y
type Pend is Data:
  NoPend{}
  PendG{}
  PendZ{}
  PendLead{}
  PendLeadF{}
  PendY{}

# the last search: its text, whether it went back, whether it matches
# whole words only (* and #)
type Find is Data:
  Find{text: String, back: Bool, word: Bool}

# the options :set changes
type Opts is Data:
  Opts{nu: Bool, rnu: Bool, hls: Bool}

# a folder's listing as Oil shows it (found once, at the start)
type Listing is Data:
  Listing{path: String, lines: List<&2, String>}

# where a folder's listing (Oil) was left: its path and the cursor
type Spot is Data:
  Spot{path: String, pos: Pos}

# the editor: the files and their lines in lower case (for grep), every
# folder's listing, the window, the cursor of every file when it was left, the cursor of every
# folder left, the files opened (most recent first), the files in the
# order they were first opened (buffer numbers), the jumps back (Ctrl-o)
# and forward (Ctrl-i), the mode, the count typed so far (0: none), the
# waiting key, the last search and whether it is highlighted, the
# options, the screen's rows and columns, the message on the command line
# and the search count shown at its right ("[1/10]")
type St is Data:
  St{files: List<&2, Buf>, folded: List<&2, List<&2, String>>, dirs: List<&2, Listing>, win: Win, marks: List<&2, Pos>, spots: List<&2, Spot>, opened: List<&2, Nat>, bufs: List<&2, Nat>, back: List<&2, Win>, fwd: List<&2, Win>, mode: Mode, count: Nat, pend: Pend, find: Maybe<&2, Find>, hl: Bool, opts: Opts, rows: Nat, cols: Nat, msg: String, stat: String}

# what happens: a key in Vim's notation ("j", "G", "<Space>", "<Esc>",
# "<CR>", "<BS>", "<C-d>"), a click on screen cell (row, col), notches of
# the wheel, a new screen size in cells
type Ev is Data:
  EvKey{name: String}
  EvClick{row: Nat, col: Nat}
  EvWheel{down: Bool, notches: Nat}
  EvSize{rows: Nat, cols: Nat}

# what the host does after a step: nothing, open a URL, copy text
type Act is Data:
  Nothing{}
  OpenUrl{url: String}
  CopyText{text: String}

# one step: the editor after it, and what the host does
type Step is Data:
  Step{st: St, act: Act}

# a cell of the screen
type Cell is Data:
  Cell{row: Nat, col: Nat}

# a run of len cells from (row, col): a search hit on screen
type Span is Data:
  Span{row: Nat, col: Nat, len: Nat}

# what a run of a float's cells is painted as
type Group is Data:
  Border{}
  Title{}
  Sel{}
  Match{}
  Dim{}
  Prompt{}
  Count{}
  Number{}
  Thumb{}

# a run of len cells from (row, col) of a float, painted as group
type Mark is Data:
  Mark{row: Nat, col: Nat, len: Nat, group: Group}

# a float (a picker): its first screen row and column, its size in cells,
# its rows of text (borders included, each width cells wide) and the runs
# painted specially, later ones over earlier ones
type Float is Data:
  Float{row: Nat, col: Nat, width: Nat, height: Nat, lines: List<&2, String>, marks: List<&2, Mark>}

# the screen: what the window shows, its first line and column, the
# screen column where text starts (sign and number columns), the gutter of
# each text row, the cursor's cell and the character under it, the
# command line, the search hits on screen, the scrollbar (first row and
# rows; 0 rows: none), whether the cursor's row shows the cursorline, the
# statusline (cols cells), the screen column of 'colorcolumn', the float
type Frame is Data:
  Frame{tgt: Tgt, top: Nat, left: Nat, gutter: Nat, nums: List<&2, String>, cur: Cell, char: String, cmd: String, hits: List<&2, Span>, bar: Span, cl: Bool, status: String, cc: Maybe<&2, Nat>, float: Maybe<&2, Float>}
