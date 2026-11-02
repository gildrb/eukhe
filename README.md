# eukhe-site

eukhe.com: the page for [eukhe](https://github.com/gildrb/eukhe), set as visible Markdown in Ioskeley Mono, in gildrb.com's colors. Preact, StyleX, strict TypeScript, Vite+, a Cloudflare Worker.

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
npm run readme    # copy eukhe's README.md from main into src/content/README.md
npm run deploy    # build (fails while the copy differs from eukhe's README), then wrangler deploy
```

## Content

- The home page is eukhe's README: `src/content/README.md`, a verbatim copy of `README.md` on eukhe's `main`. `npm run readme` refreshes it; `npm run build` fails while it differs. `src/source.ts` puts `src/content/head.md` (the header, then the motto) above it.
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
