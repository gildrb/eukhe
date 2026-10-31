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
npm run deploy    # build, then wrangler deploy
```

## Content

- `src/content/index.md`: the page. Every character shows; the first block is the header, the second the motto.
- `src/tokens.stylex.ts` `palette`: every color, OKLCH, per theme. The page prints it as the COLORS table (`src/source.ts`).

## Worker

`worker/index.ts`, files from `dist/`.

| Request                          | Response                                 |
| -------------------------------- | ---------------------------------------- |
| `GET /install`                   | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: */*` (curl)    | 302 to the latest release's `install.sh` |
| `GET /`, `Accept: text/markdown` | `index.md`                               |
| `GET /`, `Accept: text/html`     | `index.html`                             |
| `www.eukhe.com/*`                | 301 to `eukhe.com`                       |

## Limitations

- `wrangler.jsonc` has no eukhe.com route: the domain stays on the `gildrb-products` Worker until it moves here.

## License

Code: MIT ([LICENSE](LICENSE)). Font: [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
