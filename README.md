# eukhe-site

eukhe.com: the page for [Eukhe](https://github.com/gildrb/eukhe), the harness for the AGI era, set as visible Markdown in Ioskeley Mono, in gildrb.com's colors. Preact, StyleX, strict TypeScript, Vite+, a Cloudflare Worker.

## Install

```sh
vp install  # dependencies
```

## Use

```sh
vp dev            # dev server, http://127.0.0.1:5175
vp check          # format, lint, type check
vp build          # prerender into dist/
npx wrangler dev  # dist/ behind the Worker, http://127.0.0.1:8787
npm run eukhe     # copy eukhe's README and the files it links to from main into src/content/eukhe/
npm run deploy    # build (fails while the copy differs from eukhe's main), then wrangler deploy
```

## Content

- The home page is eukhe's README: `src/content/eukhe/README.md`, a verbatim copy of `README.md` on eukhe's `main`. `src/source.ts` puts `src/content/head.md` (the header, then the motto) above it and a `Source:` line below it.
- `src/content/eukhe/`: the README and every file its relative links reach, at their paths in eukhe's repository. A linked folder, or a linked `README.md` (its folder's index), brings the whole folder. `npm run eukhe` refreshes them; `npm run build` fails while they differ from `main`.
- The editor holds them (`<Space><Space>` finds them); a click on a relative link opens its file or folder there (gf). The site also serves each at its path (`/LICENSE`, `/spec/rlm/family.bend`, text), and each folder as a page (`/spec/rlm/`).
- `src/epigraphs.ts`: the site's Attic Greek epigraphs, at most one under a README heading, each with its translation and citation. The README's own lines stay as they are.
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
