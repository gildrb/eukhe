# eukhe.com as Neovim

The desktop page is a read-only Neovim. One pure Bend function holds all of it:
`Vim.step(st, event) -> Step{st, act}`; `Vim.frame(st) -> Frame` says what the screen shows.
`src/client.ts` only turns browser events into `Ev`, paints `Frame` on a fixed character grid,
and runs `Act` (open a URL, copy the install command). Phones (no fine pointer, under 720px) get the
plain page.

Laws: `LAWS.bend`. Proofs: `PROOF.bend`. Gate: `python3 ~/.agents/skills/bend/scripts/gate.py .`.

## Grid

- Ioskeley Mono, 12px: every glyph on the page advances 600/1000 em (checked at build), so one
  cell is `1ch` by 20px. The screen is `rows x cols` cells; Bend picks every cell.
- No browser wrapping (`wrap` off, as in Gil's nvim). The page source is hard-wrapped at 68
  columns; longer lines (docs tables) scroll sideways (`sidescrolloff`).

## Requirements

| Id  | Requirement                                                                                                                                                                                                                                                                                                                                  |
| --- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| R1  | The cursor is always on one cell of one row: never between rows, never off a line's text, never off screen. Holds for every sequence of events from the start (the bend-lang.com game law).                                                                                                                                                  |
| R2  | Motions behave as Neovim: `h j k l`, `w b e W B E`, `0 ^ $`, `gg G`, counts, `H M L`, `{ }`, `Ctrl-d u f b e y`, `zz zt zb`, `/ ? n N * #`.                                                                                                                                                                                                  |
| R3  | Gil's nvim config: leader Space; `-` and `<leader>e` Oil; `<leader>ff`, `<leader><leader>` files; `<leader>fg` grep; `<leader>fw` grep word; `<leader>fb` buffers; `<leader>/` buffer lines; `number`, `relativenumber`, `cursorline`, `scrolloff=8`, `sidescrolloff=8`, `ignorecase`, `smartcase`, `nowrap`, `Esc` clears search highlight. |
| R4  | `:` commands (`:N`, `:e`, `:Oil`, `:bn`, `:bp`, `:set nu/rnu/hls`, `:noh`, `:q`, `:w`), unknown ones answer as Neovim does.                                                                                                                                                                                                                  |
| R5  | Statusline: the file and `line:col`, nothing else; no key hints anywhere.                                                                                                                                                                                                                                                                    |
| R6  | Files: the page (`index.md`), `LICENSE`, eukhe's `docs/*.md`, this site's Bend source; one page, buffers in memory.                                                                                                                                                                                                                          |
| R7  | Mouse: a click puts the cursor on the clicked cell; the wheel scrolls three lines a notch, the cursor follows.                                                                                                                                                                                                                               |
| R8  | Links open from the keyboard (`gx` URL, `gf` file) and by click. The only copy is the install command.                                                                                                                                                                                                                                       |
| R9  | Custom scrollbar, from the frame; no native scrollbar.                                                                                                                                                                                                                                                                                       |
| A1  | Search patterns are literal text (no regex); `*` and `#` match whole words.                                                                                                                                                                                                                                                                  |
| A2  | Word classes follow Vim's `iskeyword` default and `utf_class`, reduced to the page's characters.                                                                                                                                                                                                                                             |
| A3  | Pickers filter by in-order letters (fuzzy subsequence), ignoring case, in path order.                                                                                                                                                                                                                                                        |
| A4  | Neovim defaults where Gil's config is silent: `nostartofline`, `wrapscan`, `hlsearch`, `incsearch`, `mousescroll=ver:3`, `numberwidth=4`, `laststatus=3`, `cmdheight=1`.                                                                                                                                                                     |
