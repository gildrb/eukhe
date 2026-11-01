# merge-settings.sh <settings.json> <declared.json>
#
# The Home Manager activation of `programs.eukhe.settings`: the declared
# settings over the settings eukhe keeps in the same file. Every declared
# key wins (objects merge key by key, any other value is replaced); every
# key the file holds and the declaration does not stays as it is, such as
# the model choices eukhe saves (`defaultProvider`, `defaultModel`,
# `recentModels`). A missing file becomes the declared settings. A file
# that is not a JSON object is left untouched (the declared settings are
# not applied and the activation says why): nothing it holds is lost.
#
# The write takes eukhe's settings lock (the `<file>.lock` directory; one
# older than 10 seconds is stale) and replaces the file atomically, mode
# 0600.
set -euo pipefail

target="$1"
declared="$2"
dir="$(dirname -- "${target}")"
lock="${target}.lock"
mkdir -p -- "${dir}"

if [[ ! -e "${target}" ]]; then
  install -m 0600 -- "${declared}" "${target}"
  exit 0
fi

held=0
for _ in $(seq 1 100); do
  if mkdir -- "${lock}" 2>/dev/null; then
    held=1
    break
  fi
  modified="$(stat -c %Y -- "${lock}" 2>/dev/null || echo "")"
  if [[ -n "${modified}" && $(($(date +%s) - modified)) -gt 10 ]]; then
    rmdir -- "${lock}" 2>/dev/null || true
    continue
  fi
  sleep 0.1
done
if [[ ${held} -ne 1 ]]; then
  echo "eukhe: ${target} stays locked by a running eukhe; the declared settings were not applied (activate again)" >&2
  exit 0
fi
tmp="$(mktemp -- "${dir}/.settings.json.XXXXXX")"
trap 'rm -f -- "${tmp}"; rmdir -- "${lock}" 2>/dev/null || true' EXIT

if ! jq -e 'type == "object"' "${target}" >/dev/null 2>&1; then
  echo "eukhe: ${target} is not a JSON object; the declared settings were not applied (fix or remove the file)" >&2
  exit 0
fi
jq -s '.[0] * .[1]' "${target}" "${declared}" >"${tmp}"
chmod 0600 -- "${tmp}"
mv -f -- "${tmp}" "${target}"
