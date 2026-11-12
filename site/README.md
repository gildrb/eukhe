# site

eukhe.com: the page for [Eukhe](https://github.com/gildrb/eukhe), a harness and embeddable core for agents, set as visible Markdown in Paper Mono, in gildrb.com's colors. Preact, StyleX, strict TypeScript, Vite+, a Cloudflare Worker.

It lives in `site/` of Eukhe's repository (until November 2026 it was gildrb/eukhe-site, whose history is this folder's) and is apart from Eukhe in all but one thing: its build reads the repository's files (`../README.md` and what it links to). It has its own toolchain (npm, `package-lock.json`), laws (`LAWS.bend`, `laws/`, `proof/`, `LAWS.lock`) and check; no Eukhe gate, hook or release runs it, and a broken site breaks only the site's deploy.

## Install

```sh
npm ci  # dependencies (npm, any version)
```

The site's Bend (`vim/vim.bend`) builds with the Bend release Eukhe pins (`../scripts/toolchain.env`, found by `../scripts/pinned_bend.sh`).

## Use

```sh
npm run dev       # dev server, http://127.0.0.1:5175
npm run check     # format, lint, type check (vp check)
npm run laws      # the site's proofs (checker and --verdict), then LAWS.lock
npm run build     # vim/vim.bend -> src/vim.mjs, then prerender into dist/
npx wrangler dev  # dist/ behind the Worker, http://127.0.0.1:8787
```

From the repository root: `make site-check` (`npm ci`, check, laws, build) and `make site-deploy` (`npm ci`, build, `wrangler deploy`). A deploy happens only when someone runs `make site-deploy`; nothing deploys on a push.

## Content

- The home page is eukhe's README: the repository's `README.md`, read at build time. `src/source.ts` puts `src/content/head.md` (the header, then the motto) above it and a `Source:` line below it.
- `scripts/files.ts`: every file the README's relative links reach, read from the repository at build time at their paths in it (its tracked files, `git ls-files`, outside `site/`). A linked folder, or a linked `README.md` (its folder's index), brings the whole folder; the links of each Markdown file reached are followed in turn. A link that leaves the repository or reaches no file fails the build.
- The editor holds them (`<Space><Space>` finds them); a click on a relative link opens its file or folder there (gf). The site also serves each at its path (`/LICENSE`, `/spec/rlm/family.bend`, text), and each folder as a page (`/spec/rlm/`).
- `src/epigraphs.ts`: the site's Attic Greek epigraphs, at most one under a README heading, each with its translation and citation. The README's own lines stay as they are; an epigraph whose heading the README no longer holds is left out (the build names it), so a README edit never breaks the site.
- `src/content/{about,contact,privacy}.md`: the other pages. Every character shows; the first block is the header, the second the motto.
- `src/tokens.stylex.ts` `palette`: every color, OKLCH, per theme.

## Worker

`worker/index.ts`, files from `dist/`. Routes: `eukhe.com/*`, `www.eukhe.com/*`. `gildrb.com/eukhe` and `eukhe.gildrb.com` redirect here from gildrb.com.

| Request                          | Response                                 |
| -------------------------------- | ---------------------------------------- |
| `GET /install`                   | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: */*` (curl)    | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: text/markdown` | `index.md`                               |
| `GET /`, `Accept: text/html`     | `index.html`                             |
| `www.eukhe.com/*`                | 301 to `eukhe.com`                       |

## License

Code: MIT ([LICENSE](LICENSE)). Font: [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
