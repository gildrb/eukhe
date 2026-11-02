# Service config schema

Every file `services/<stem>.json` holds one JSON object with exactly these keys:

| key | type | rule |
|---|---|---|
| `name` | string | equals the file stem (`services/search.json` → `"search"`) |
| `port` | integer | 1024–65535, and no two services share a port |
| `replicas` | integer | at least 1 |
| `owner` | string | an e-mail address ending in `@example.org` |
| `healthcheck` | object | `{"path": string starting with "/", "interval_s": integer 5–300}` |

File names are referenced by the deploy scripts: never rename or delete a config file.
