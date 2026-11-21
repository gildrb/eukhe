"""merge_settings.py <settings.json> <declared.json>

The Home Manager activation of `programs.eukhe.settings`: the declared
settings over the settings eukhe keeps in the same file. Every declared key
wins (objects merge key by key, any other value is replaced); every key the
file holds and the declaration does not stays as it is, such as the model
choices eukhe saves (`defaultProvider`, `defaultModel`, `recentModels`). A
missing file becomes the declared settings. A file that is not a JSON object
is left untouched (the declared settings are not applied and the activation
says why): nothing it holds is lost.

The write takes eukhe's settings lock (the `<file>.lock` directory; one older
than 10 seconds is stale) and replaces the file atomically, mode 0600.

nix/home-manager.nix runs it as `eukhe-merge-settings`
(pkgs.writers.writePython3Bin). Tests: python3 nix/test_merge_settings.py
"""

import json
import os
import sys
import tempfile
import time

STALE = 10  # seconds: a lock this old is a crashed eukhe's


def merge(saved, declared):
    """`saved` with `declared` over it: objects merge key by key (jq's `*`),
    any other declared value replaces the saved one."""
    if not (isinstance(saved, dict) and isinstance(declared, dict)):
        return declared
    merged = dict(saved)
    for key, value in declared.items():
        merged[key] = merge(saved[key], value) if key in saved else value
    return merged


def take(lock):
    """Take the settings lock: 100 tries 0.1 s apart; a stale one is
    removed. False when a running eukhe keeps it."""
    for _ in range(100):
        try:
            os.mkdir(lock)
            return True
        except OSError:
            pass
        try:
            modified = int(os.stat(lock).st_mtime)
        except OSError:
            modified = None
        if modified is not None and int(time.time()) - modified > STALE:
            try:
                os.rmdir(lock)
            except OSError:
                pass
            continue
        time.sleep(0.1)
    return False


def saved_object(target):
    """The file's settings, or None when it is not a JSON object."""
    try:
        with open(target, encoding="utf-8") as handle:
            saved = json.load(handle)
    except (OSError, ValueError):
        return None
    return saved if isinstance(saved, dict) else None


def main():
    target, declared_path = sys.argv[1], sys.argv[2]
    directory = os.path.dirname(target) or "."
    os.makedirs(directory, exist_ok=True)
    with open(declared_path, "rb") as handle:
        declared = handle.read()

    if not os.path.exists(target):
        fd = os.open(target, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
        with os.fdopen(fd, "wb") as handle:
            handle.write(declared)
        os.chmod(target, 0o600)
        return 0

    lock = f"{target}.lock"
    if not take(lock):
        print(
            f"eukhe: {target} stays locked by a running eukhe; the declared "
            "settings were not applied (activate again)",
            file=sys.stderr,
        )
        return 0
    fd, tmp = tempfile.mkstemp(prefix=".settings.json.", dir=directory)
    try:
        saved = saved_object(target)
        if saved is None:
            print(
                f"eukhe: {target} is not a JSON object; the declared settings "
                "were not applied (fix or remove the file)",
                file=sys.stderr,
            )
            return 0
        merged = merge(saved, json.loads(declared))
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            fd = -1
            json.dump(merged, handle, indent=2, ensure_ascii=False)
            handle.write("\n")
        os.chmod(tmp, 0o600)
        os.replace(tmp, target)
    finally:
        if fd != -1:
            os.close(fd)
        if os.path.exists(tmp):
            os.unlink(tmp)
        try:
            os.rmdir(lock)
        except OSError:
            pass
    return 0


if __name__ == "__main__":
    sys.exit(main())
