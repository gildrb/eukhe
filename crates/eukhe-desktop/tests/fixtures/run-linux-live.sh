#!/usr/bin/env bash
# Runs the Linux live test binary ($1, from `cargo test --test linux_live --no-run`)
# against the GTK 3 fixture on a private Xvfb display, D-Bus session and AT-SPI
# bus, inside a nix shell. Never touches the caller's display or session.
set -euo pipefail
fixtures=$(cd "$(dirname "$0")" && pwd)
binary=$(realpath "$1")
shift

if [ -z "${EUKHE_LIVE_INNER:-}" ]; then
  atspi=$(nix build --no-link --print-out-paths nixpkgs#at-spi2-core | head -n1)
  exec env -u WAYLAND_DISPLAY -u DISPLAY -u DBUS_SESSION_BUS_ADDRESS -u AT_SPI_BUS_ADDRESS \
    EUKHE_LIVE_INNER=1 EUKHE_LIVE_ATSPI="$atspi" \
    nix-shell --pure --keep EUKHE_LIVE_INNER --keep EUKHE_LIVE_ATSPI \
    -p 'python3.withPackages (p: [ p.pygobject3 ])' gtk3 gobject-introspection xvfb dbus coreutils procps \
    --run "dbus-run-session -- bash '$0' '$binary' $*"
fi

work=$(mktemp -d)
trap 'kill $(jobs -p) 2>/dev/null || true; rm -rf "$work"' EXIT
export XDG_RUNTIME_DIR="$work" HOME="$work"

# A display number no server holds; -displayfd reports the one it took.
exec {display_fd}<> <(:)
Xvfb -displayfd "$display_fd" -screen 0 1280x800x24 -nolisten tcp -noreset >"$work/xvfb.log" 2>&1 &
read -r -t 20 number <&"$display_fd"
export DISPLAY=":$number"

# The bus launcher's own activation of the registry needs systemd, so the
# registry starts here once the bus is up, and before the fixture registers.
"$EUKHE_LIVE_ATSPI/libexec/at-spi-bus-launcher" --launch-immediately >"$work/atspi.log" 2>&1 &
for _ in $(seq 100); do
  dbus-send --session --print-reply --dest=org.freedesktop.DBus /org/freedesktop/DBus \
    org.freedesktop.DBus.NameHasOwner string:org.a11y.Bus 2>/dev/null | grep -q true && break
  sleep 0.1
done
"$EUKHE_LIVE_ATSPI/libexec/at-spi2-registryd" >"$work/registry.log" 2>&1 &
sleep 1
python3 "$fixtures/gtk3_fixture.py" >"$work/fixture.log" 2>&1 &

status=0
"$binary" --ignored --nocapture --test-threads=1 "$@" || status=$?
if [ "$status" -ne 0 ]; then
  tail -n 40 "$work"/*.log >&2 || true
fi
exit "$status"
