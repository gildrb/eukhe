# site

eukhe.com: Eukhe's README and the files it links, set as Neovim renders Markdown, in Paper Mono and gildrb.com's colors. Preact, StyleX, strict TypeScript, Vite+ (`vp`), a Cloudflare Worker. Its build reads the repository's files (`../../README.md` and what it links to); its own laws (`LAWS.bend`, `laws/`, `proof/`, `LAWS.lock`) and check. No Eukhe gate, hook or release runs it; nothing deploys on a push.

## Commands

```sh
vp install --frozen-lockfile  # dependencies
vp dev                        # dev server, http://127.0.0.1:5175
vp check                      # format, lint, type check
vp run laws                   # the site's proofs (checker and --verdict), then LAWS.lock
vp run build                  # vim/vim.bend -> src/vim.mjs, then prerender into dist/
vp exec wrangler dev          # dist/ behind the Worker, http://127.0.0.1:8787
```

From the repository root: `make site-check` (install, check, laws, build); `make site-deploy` (install, build, `wrangler deploy`). The site's Bend (`vim/vim.bend`) builds with the Bend release Eukhe pins (`../../.github/scripts/toolchain.env`, found by `../../.github/scripts/pinned_bend.py`).

## Content

- Home page: the repository's `README.md`, read at build time; its first `# ` heading names the page. `src/source.ts` puts a `Source:` line under its title and at its end.
- The editor shows Markdown rendered as Neovim does with render-markdown.nvim and snacks.nvim (`src/rendered.ts`): markers hidden, prose wrapped at 80 cells or the screen, the README's HTML rendered, each `<img>` in rows of its own under its line, linking the source. Each image the README shows is served at its path (`.github/media/*.webp`), named by its content. Every code block gets a `[copy]` of its commands.
- Visual mode (`v`, `V`, a mouse drag) selects, motions extend it, `-- VISUAL --` names it; `y`, `yy`, `Y`, Cmd-C, Ctrl-C copy; a yank flashes for 150 ms (vim/visual.bend; laws R7, R9, R10).
- `scripts/files.ts`: every file the README's relative links reach, read at build time from the repository's tracked files outside `crates/site/`. A linked folder, or a linked `README.md` (its folder's index), brings the whole folder; links of each Markdown file reached are followed in turn. A link that leaves the repository or reaches no file fails the build.
- The editor holds those files (`<Space><Space>` finds them); a click on a relative link opens its file or folder (gf). The site serves each at its path (`/LICENSE`, `/spec/rlm/family.bend`, text), and each folder as a page (`/spec/rlm/`).
- `src/epigraphs.ts`: Attic Greek epigraphs, at most one under a README heading, each with translation and citation; keyed by heading line. An epigraph whose heading the README no longer holds is left out (the build names it).
- `src/content/{about,contact,privacy}.md`: the other pages, rendered the same way.
- `src/tokens.stylex.ts` `palette`: every color, OKLCH, per theme.
- Font notices: `THIRD_PARTY_NOTICES.md`.

## Worker

`worker/index.ts`, files from `dist/`. Routes: `eukhe.com/*`, `www.eukhe.com/*`. `gildrb.com/eukhe` and `eukhe.gildrb.com` redirect here from gildrb.com.

| Request                          | Response                                 |
| -------------------------------- | ---------------------------------------- |
| `GET /install`                   | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: */*` (curl)    | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: text/markdown` | `index.md`                               |
| `GET /`, `Accept: text/html`     | `index.html`                             |
| `www.eukhe.com/*`                | 301 to `eukhe.com`                       |
