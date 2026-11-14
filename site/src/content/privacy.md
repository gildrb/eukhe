EUKHE
PRIVACY
2026

# PRIVACY

## THIS SITE

eukhe.com sets no cookies and runs no analytics, tracking or
advertising scripts. It collects no personal data of its own and
stores nothing on your device. Its fonts and files are served from
eukhe.com itself; no third party is asked for anything while you read.

The site is served by Cloudflare, which processes request data such as
IP addresses to deliver pages and protect against abuse, under
[Cloudflare's privacy policy](https://www.cloudflare.com/privacypolicy/).
The install command downloads the installer from GitHub, under
[GitHub's privacy statement](https://docs.github.com/site-policy/privacy-policies/github-general-privacy-statement).

## THE EUKHE PROGRAM

Eukhe runs on your machine. Its chat logs and memory stay in
`~/.eukhe/` on your disk. Prompts, and the files the agent reads, go
to the providers of the models a session uses (the session's model,
failover models, the memory model, and any model a check or the agent
names), under each provider's terms. An optional scrubber,
`privacy.anonymizeRemote` (off by default), replaces the listed terms
and the email addresses, phone numbers and IP addresses it detects
with tokens before a request goes to a remote provider. Eukhe fetches
its pinned uv and Python the first time the Python kernel starts, and
a locked package the first time the kernel imports it, each checked
against its pinned sha256. `eukhe kernel install` fetches them ahead
of time; `eukhe tiny-models download` fetches local models; `eukhe
update` fetches a release.

Questions? Write to [mail@gildrb.com](mailto:mail@gildrb.com).

More: [about](/about), [contact](/contact), [llms.txt](/llms.txt).
