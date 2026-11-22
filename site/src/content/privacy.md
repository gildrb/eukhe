# Eukhe

## This site

eukhe.com sets no cookies, runs no analytics, tracking or advertising scripts and stores nothing on the device. It serves its fonts and files itself. Cloudflare serves the site and processes request data such as IP addresses to deliver pages and stop abuse, under [Cloudflare's privacy policy](https://www.cloudflare.com/privacypolicy/). The install command downloads the installer from GitHub, under [GitHub's privacy statement](https://docs.github.com/site-policy/privacy-policies/github-general-privacy-statement).

## The Eukhe program

Eukhe runs on the user's machine and keeps its chat logs and memory in `~/.eukhe/`. Prompts and the files the agent reads go to the providers of the models a session uses: the session's model, failover models, the memory model and any model a check or the agent names. Each provider's terms apply. The scrubber `privacy.anonymizeRemote` (off by default) replaces the listed terms and the email addresses, phone numbers and IP addresses it detects with tokens before a request goes to a remote provider.

Eukhe downloads its pinned uv and Python at the first start of the Python kernel, and a locked package at its first import, each checked against its pinned sha256. `eukhe kernel install` downloads them ahead of time, `eukhe tiny-models download` downloads local models and `eukhe update` downloads a release.

Questions go to [g@gildrb.com](mailto:g@gildrb.com).

More: [about](/about), [contact](/contact), [llms.txt](/llms.txt).
