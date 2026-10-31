# eukhe.com as Neovim

On desktop (fine pointer, 720px or wider) the page is a read-only Neovim with Gil's config. Phones get the plain page.

| Part  | File                                   | Does                                                                                                        |
| ----- | -------------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| Core  | `vim/*.bend` (entry `vim/vim.bend`)    | `Vim.init`, `Vim.step(st, ev) -> Step{st, act}`, `Vim.frame(st)`, `Vim.lines(st)`; pure, decides everything |
| Host  | `src/client.ts`                        | browser events to `Ev`; paints `Frame` on a cell grid; runs `Act` (open URL, copy install command)          |
| Files | `scripts/files.ts`, `src/markdown.tsx` | `files.json`: each file's lines, highlights, the page's inks, the install fence                             |
| Laws  | `LAWS.bend`                            | requirements `R1`-`R7`, `A1`-`A3` at its top; one law per claim                                             |

## Grid

- The whole window, 2px padding (Ghostty). Font 15px; cell = one advance of Ioskeley Mono by its line height, measured at start.
- Layers: number column, text rows, statusline, command line, float, cursor, scrollbar. A key rewrites only the rows that changed.
- The goose of fff's prompt (U+1FABF) takes two cells; every other character one.

## Reference

| Source            | Path                                              |
| ----------------- | ------------------------------------------------- |
| Options, keymaps  | `~/.config/nvim/lua/config/{options,keymaps}.lua` |
| Oil, fff, fzf-lua | `~/.config/nvim/lua/plugins/editor.lua`           |

## Use

```sh
npm run bend                      # vim/vim.bend -> src/vim.mjs
bend vim/vim.bend --check-only    # type-check the core
python3 scripts/vim-diff.py       # diff Bend screens against real nvim (pyte)
node scripts/vim-smoke.mjs        # drive the core from Node
```

## Limitations

- fff ranks by frecency; ours lists matches in file order.
- Live grep shows one page of 40 matches.
- fzf-lua buffer numbers follow first-open order.
