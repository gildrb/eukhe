# eukhe.com as Neovim

The page is a read-only Neovim with Gil's config, on every screen with the script. Without it, the plain page (Markdown reflowed to the screen's width).

| Part  | File                                   | Does                                                                                                                 |
| ----- | -------------------------------------- | -------------------------------------------------------------------------------------------------------------------- |
| Core  | `vim/*.bend` (entry `vim/vim.bend`)    | `Vim.init`, `Vim.step(st, ev) -> Step{st, act}`, `Vim.frame(st)`, `Vim.lines(st)`; pure, decides everything          |
| Host  | `src/client.ts`                        | browser events to `Ev`; paints `Frame` on a cell grid; runs `Act` (open URL, copy install command)                   |
| Files | `scripts/files.ts`, `src/markdown.tsx` | `files.json`: the pages and eukhe's files (the repository's, `..`); each file's lines, highlights, the install fence |
| Laws  | `LAWS.bend`, `laws/vim/`               | requirements `R1`-`R7`, `A1`-`A3` atop LAWS.bend; one law per claim, by section in `laws/vim/<section>.bend`         |

## Grid

- The whole window, 2px padding (Ghostty). Font 15px (13px on touch screens); cell = one advance of Paper Mono (set to 0.6em by `size-adjust`) by its line height, measured at start.
- Layers: number column, text rows, statusline, command line, float, cursor, scrollbar. A key rewrites only the rows that changed.
- First screen: painted at build by `src/render.tsx` with the browser's own painter (`src/paint.ts`); a row's HTML never depends on the screen width (CSS clips it), so the editor takes it over unchanged.
- The editor's code loads after the `load` event and starts at the first input (key, click, touch, wheel); `files.json` loads meanwhile.
- The goose of fff's prompt (U+1FABF) takes two cells; every other character one.

## Touch

| Gesture         | Does                                                                           |
| --------------- | ------------------------------------------------------------------------------ |
| Vertical drag   | text follows the finger, a row per line height (`<C-e>`, `<C-y>` with a count) |
| Flick           | keeps scrolling, 5% slower each frame                                          |
| Horizontal drag | view moves a column per cell (`zl`, `zh` with a count)                         |
| Tap             | cursor to the cell; `[copy]` copies the install command                        |
| Tap a link      | its label or URL: eukhe's file or folder opens in the editor (gf), a URL opens |
| Tap Oil entry   | opens it (Enter); `../` goes up                                                |
| Tap statusline  | the folder above the window (`-`)                                              |
| Pinch           | font 7-28px; the screen gains or loses rows and columns                        |
| Browser back    | edge swipe, or a rightward drag at the first column: back a tap (`<C-o>`)      |

Each place a tap opens is a browser history entry (same URL); back and forward step through them with `<C-o>` and `<C-i>`. Mouse clicks open links (label or URL); Oil and statusline taps are touch-only, as in nvim. No keyboard comes up: pickers and commands stay desktop-only.

## Reference

| Source            | Path                                              |
| ----------------- | ------------------------------------------------- |
| Options, keymaps  | `~/.config/nvim/lua/config/{options,keymaps}.lua` |
| Oil, fff, fzf-lua | `~/.config/nvim/lua/plugins/editor.lua`           |

## Use

```sh
npm run bend                                              # vim/vim.bend -> src/vim.mjs (the pinned Bend)
"$(../scripts/pinned_bend.sh)" vim/vim.bend --check-only  # type-check the core
python3 scripts/vim-diff.py                               # diff Bend screens against real nvim (pyte)
node scripts/vim-smoke.mjs                                # drive the core from Node
```

## Limitations

- fff ranks by frecency; ours lists matches in file order.
- Live grep shows one page of 40 matches.
- fzf-lua buffer numbers follow first-open order.
