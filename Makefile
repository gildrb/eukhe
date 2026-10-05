# Merge gate (AGENTS.md): fmt + clippy + test + release build must pass before every merge.
check:
	cargo fmt --all --check
	cargo clippy --workspace --all-targets -- -D warnings
	cargo test --workspace
	cargo build --release --workspace


# Supply-chain gates — local mirrors of the
# ci.yml workflow jobs. They fail loudly when the tool is missing instead of
# silently skipping the gate.

deny:
	@command -v cargo-deny >/dev/null 2>&1 || { echo "cargo-deny not installed (cargo install cargo-deny --locked)"; exit 1; }
	cargo deny --all-features --workspace check advisories bans licenses sources

# Windows cfg-hygiene gate: cross-target check +
# clippy at -D warnings for every crate and test, the local mirror of the
# ci.yml windows-cross job (.github/workflows/ci.yml). Fails loudly when the
# target is missing instead of silently skipping the gate.
windows-cross:
	@rustup target list --installed | grep -q x86_64-pc-windows-gnu || { echo "x86_64-pc-windows-gnu target not installed (rustup target add x86_64-pc-windows-gnu)"; exit 1; }
	cargo check --workspace --target x86_64-pc-windows-gnu --all-targets
	cargo clippy --workspace --target x86_64-pc-windows-gnu --all-targets -- -D warnings

# Lints every workflow file (.github/workflows/ is the one home for
# workflow files).
actionlint:
	@command -v actionlint >/dev/null 2>&1 || { echo "actionlint not installed (see rhysd/actionlint releases)"; exit 1; }
	actionlint .github/workflows/ci.yml .github/workflows/eukhe-release.yml

# GLIBC baseline gate (eukhe-release.yml's build-linux job): a
# GNU/Linux artifact must not require symbols above GLIBC_2.35, the Ubuntu
# 22.04 release baseline. No-op on non-GNU hosts; the authoritative gate runs
# in CI inside the ubuntu:22.04 build container. POSIX sh throughout: make
# runs recipes with /bin/sh, which is dash on Ubuntu (no [[ ]], no ==).
glibc-gate:
	@case "$(TARGET)" in *-linux-gnu) \
		if ! objdump -T "$(GLIBC_BINARY)" >/dev/null 2>&1; then \
			echo "glibc-gate: unable to inspect $(GLIBC_BINARY) with objdump (build and split first)" >&2; exit 1; \
		fi; \
		syms="$$(objdump -T "$(GLIBC_BINARY)" | grep -o 'GLIBC_[0-9.]*' || true)"; \
		if [ -z "$$syms" ]; then \
			echo "glibc-gate: no GLIBC symbols found in $(GLIBC_BINARY) - refusing to pass without evidence" >&2; exit 1; \
		fi; \
		max_glibc="$$(printf '%s\n' "$$syms" | sort -Vu | tail -1)"; \
		echo "highest GLIBC symbol required: $${max_glibc}"; \
		top="$$(printf '%s\nGLIBC_2.35\n' "$$max_glibc" | sort -Vu | tail -1)"; \
		if [ "$$top" != "GLIBC_2.35" ]; then \
			echo "binary requires $${max_glibc}, above the GLIBC_2.35 (Ubuntu 22.04) baseline" >&2; exit 1; \
		fi \
		;; esac

# Local mirror of eukhe-release.yml's build-job gates:
# release build against the committed lockfile, deterministic tarball assembly,
# then end-to-end verification of the host-target artifact. The vendored
# eukhe-runtime/ at the repo root is the default runtime sidecar
# (kernel-packaging lane); pass RUNTIME_DIR to re-anchor it.
VERSION := $(shell sed -n 's/^version *= *"\([^"]*\)".*/\1/p' Cargo.toml | head -1)
TARGET := $(shell rustc -vV | sed -n 's/^host: //p')
RUNTIME_DIR ?=
RUNTIME_FLAG = $(if $(RUNTIME_DIR),--runtime-dir $(RUNTIME_DIR),)

# Bundled catalog assets (catalog spec §3.2 layer 2): generated at build
# time, never committed. The release workflow fetches the catalog commit
# pinned in scripts/release/catalog-pin.json and checks each file's sha256
# (`--network`). The local dry-runs default to the offline fixture snapshot
# (it passes the full packer gates: >= 42 transport tuples, >= 68 services);
# CATALOG_ASSETS_MODE=network switches them to the pinned fetch for
# packaging parity.
CATALOG_ASSETS_DIR = target/catalog-assets
CATALOG_ASSETS_MODE ?= fixture
CATALOG_ASSETS_FLAG = --catalog-assets $(CATALOG_ASSETS_DIR)

# Mirror the Linux CI split: Cargo's executable remains unstripped and the
# archive receives a separate shipped ELF plus its detached decoder.
ifneq ($(filter %-unknown-linux-gnu,$(TARGET)),)
RELEASE_BINARY = target/release/dist/eukhe
RELEASE_DECODER = target/release/dist/eukhe-$(VERSION)-$(if $(filter aarch64-%,$(TARGET)),linux-arm64,linux-x64).debug.gz
RELEASE_ASSEMBLE_FLAGS = --binary $(RELEASE_BINARY) --decoder $(RELEASE_DECODER)
RELEASE_SPLIT = python3 scripts/release/split_debug.py --binary target/release/eukhe --shipped $(RELEASE_BINARY) --out target/release/dist --version "$(VERSION)" --target "$(TARGET)"
RELEASE_VERIFY_DECODER = python3 scripts/release/verify_decoders.py target/release/dist
RELEASE_PACKAGE_BUILD = cargo build --release --locked --workspace
RELEASE_PACKAGE_FLAGS = --binary $(RELEASE_BINARY) --decoder $(RELEASE_DECODER) --skip-build
GLIBC_BINARY = $(RELEASE_BINARY)
else
RELEASE_ASSEMBLE_FLAGS =
RELEASE_SPLIT = :
RELEASE_VERIFY_DECODER = :
RELEASE_PACKAGE_BUILD = :
RELEASE_PACKAGE_FLAGS =
endif

# Pinned-catalog asset generation (network fetch of the catalog-pin.json
# commit, sha256-checked; the release workflow's mode).
catalog-assets:
	python3 scripts/release/bundle_catalog.py generate --network --out $(CATALOG_ASSETS_DIR)

# Offline asset generation: the synthetic full-gate fixture snapshot.
catalog-assets-fixture:
	python3 scripts/release/bundle_catalog.py generate --fixture --out $(CATALOG_ASSETS_DIR)

# Move the catalog pin (scripts/release/catalog-pin.json) to the catalog
# repo's current CATALOG_REF (default main): resolves the commit, fetches
# both files at it, runs the full validation gates, and records the commit
# and both sha256. Review the diff before committing it.
CATALOG_REF ?= main
catalog-pin:
	python3 scripts/release/bundle_catalog.py pin --ref $(CATALOG_REF)

release-dry-run:
	cargo build --release --locked --workspace
	$(RELEASE_SPLIT)
	$(MAKE) glibc-gate
	python3 scripts/release/bundle_catalog.py generate --$(CATALOG_ASSETS_MODE) --out $(CATALOG_ASSETS_DIR)
	python3 scripts/release/assemble_artifacts.py \
		--repo-root . --version "$(VERSION)" --target "$(TARGET)" $(RUNTIME_FLAG) \
		$(RELEASE_ASSEMBLE_FLAGS) $(CATALOG_ASSETS_FLAG) --out-dir target/release/dist
	$(RELEASE_VERIFY_DECODER)
	python3 scripts/release/verify_release.py \
		--dist-dir target/release/dist --version "$(VERSION)" --target "$(TARGET)"

# Optional hardening: embed the dependency list in the binary for incident
# response.
audit-build:
	@command -v cargo-auditable >/dev/null 2>&1 || { echo "cargo-auditable not installed (cargo install cargo-auditable --locked)"; exit 1; }
	cargo auditable build --release --locked --workspace

# Packaging dry-run: stage the exe-adjacent release layout, version-pin,
# hash, and tar the artifact under target/release-package. Generates the
# bundled catalog assets first (same modes as the dry-runs above).
package:
	$(RELEASE_PACKAGE_BUILD)
	$(RELEASE_SPLIT)
	python3 scripts/release/bundle_catalog.py generate --$(CATALOG_ASSETS_MODE) --out $(CATALOG_ASSETS_DIR)
	python3 scripts/package_release.py $(RELEASE_PACKAGE_FLAGS) $(CATALOG_ASSETS_FLAG)

# Bundled-catalog gates (scripts/release/test_catalog_assets.py): the
# offline fixture passes the full packer validation, the packer hard-fails
# on missing/invalid assets, network mode is verified against a local HTTP
# server (including the pinned-sha256 check), and the assets land in the
# tarball layout the binary expects. test_stamp_version.py covers the
# rolling-version Cargo.toml/Cargo.lock stamp.
catalog-assets-gates:
	python3 scripts/release/test_catalog_assets.py
	python3 scripts/release/test_stamp_version.py

# The CI shard tooling's contract battery (ci.yml's PR smoke): the stable
# crc32 assignment under the narrowed selection, the scope-aware summary
# audit, the selection resolver the conditional bins build reads, and the
# fail-safe PR-files mapping the changes job feeds it.
shard-gates:
	python3 scripts/test_ci_test_shard.py
	python3 scripts/test_ci_pr_crates.py

# The kernel venv's hash-locked requirements: eukhe-runtime/uv.lock exported
# to eukhe-runtime/requirements-kernel.txt (the only file the venv bootstrap
# installs from). runtime-lock re-resolves (network) and re-exports;
# runtime-lock-check is offline: uv.lock must match pyproject.toml, the
# committed export must equal a fresh frozen export, and every pin must be
# exact, hashed, and in uv.lock (scripts/release/runtime_lock.py).
RUNTIME_LOCK_EXPORT = uv export --frozen --no-header --format requirements-txt --no-emit-project --no-default-groups --group kernel

runtime-lock:
	cd eukhe-runtime && uv lock && $(RUNTIME_LOCK_EXPORT) > requirements-kernel.txt

runtime-lock-check:
	cd eukhe-runtime && uv lock --check --offline
	cd eukhe-runtime && $(RUNTIME_LOCK_EXPORT) | diff -u requirements-kernel.txt -
	python3 scripts/release/test_runtime_lock.py

.PHONY: check deny windows-cross actionlint glibc-gate release-dry-run audit-build package catalog-assets catalog-assets-fixture catalog-pin catalog-assets-gates shard-gates runtime-lock runtime-lock-check
