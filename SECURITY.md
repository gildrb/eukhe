# Security policy

## Report a vulnerability

Do not open a public issue for a vulnerability.

Use GitHub private vulnerability reporting:
<https://github.com/gildrb/eukhe/security/advisories/new>

Include the affected version (`eukhe --version`), the steps to reproduce, and the impact.

## Supported versions

| Version | Supported |
| --- | --- |
| `main` | Yes |
| Latest release | Yes |
| Older releases | No |

## Verify a release

Each release has the archives, `SHA256SUMS`, and `release.json`. The release workflow attests the build provenance of each asset.

1. Download the archive and `SHA256SUMS` from the release.
2. Verify the checksum:

   ```sh
   sha256sum --ignore-missing -c SHA256SUMS
   ```

   On macOS, use `shasum -a 256 --ignore-missing -c SHA256SUMS`.

3. Verify the provenance attestation (GitHub CLI 2.49 or later):

   ```sh
   gh attestation verify eukhe-<version>-<platform>.tar.gz --repo gildrb/eukhe
   ```

Do not use an asset if one of these checks fails.

## Trust model

Settings in `<project>/.eukhe/` that run code apply only when the project path is in `trustedProjects` in the global settings. For other projects, eukhe ignores these settings.
