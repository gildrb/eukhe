# Glossary

Terms as they are used in reports and in code that produces reports.

- **Active user** — an enabled account whose last login falls within the 30 days before the
  report date. The `active` field on `User` is only the *enabled* flag (false = suspended); it is
  not what "active" means in reports.
- **Paying user** — an enabled account on the `pro` or `team` plan. `trial` and `free` are not paying.
- **Report date** — the `--today` date given to the report command.
