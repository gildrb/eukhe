# Merge gate (AGENTS.md): fmt + clippy + test + release build must pass before every merge.
check:
	cargo fmt --all --check
	cargo clippy --workspace --all-targets --locked -- -D warnings
	@command -v uv >/dev/null 2>&1 || { echo "uv not installed: the real-kernel tests build their venv from eukhe-runtime/uv.lock"; exit 1; }
	cargo test --workspace --locked
	$(MAKE) runtime-test
	cargo build --release --workspace --locked

# The CI gates (scripts/ci_local.sh). GitHub runs no gate: they run only
# here. ci-fast is the pre-commit gate: rustfmt, the secrets scan of the
# staged diff (when gitleaks is installed), clippy on the crates the staged
# change touches (scripts/ci_pr_crates.py). The pre-push gate checks the
# pushed commits: rustfmt, their secrets scan, clippy and tests on the
# crates they touch, `bend PROOF.bend`. ci-local is the full gate; the
# nightly run (scripts/ci_nightly.sh, a systemd user timer) runs it on
# origin/main and starts the release only when it passes.
# `make hooks` makes git run the hooks through prek (.pre-commit-config.yaml;
# the hooks are in the git common dir, so every worktree shares them; a
# worktree of an older commit, without the config, skips them).
ci-fast:
	@scripts/ci_local.sh fast

ci-local:
	@scripts/ci_local.sh full

nightly:
	@scripts/ci_nightly.sh run

nightly-status:
	@scripts/ci_nightly.sh status

hooks:
	@command -v prek >/dev/null 2>&1 || { echo "prek not installed (docs/develop.md: mise use -g github:j178/prek@0.5.7)"; exit 1; }
	prek install --allow-missing-config --hook-type pre-commit --hook-type pre-push

# The eukhe-runtime Python suite on the uv-locked kernel env (the env the
# real-kernel cargo tests build: crates/eukhe-core/tests/support/kernel_runtime.rs).
runtime-test:
	UV_PROJECT_ENVIRONMENT=$(CURDIR)/target/runtime-venv uv run --no-config --locked --group kernel --python 3.11 --project eukhe-runtime python -m unittest discover -s eukhe-runtime/test

# The pinned Bend and Lean releases: BEND_VERSION, LEAN_VERSION.
include scripts/toolchain.env

# The laws (LAWS.bend, proven in PROOF.bend; docs/memory.md). The full gate
# (ci-local) runs them too. --verdict needs Lean $(LEAN_VERSION).
laws:
	@command -v bend >/dev/null 2>&1 || { echo "bend not installed (Bend $(BEND_VERSION): https://bend-lang.com/install.sh)"; exit 1; }
	bend PROOF.bend | tee /dev/stderr | grep -qx 'ALL PROOFS CHECK'
	bend PROOF.bend --verdict | tee /dev/stderr | grep -qx 'ALL PROOFS CHECK'

# The compiled Bend core (crates/eukhe-bend): bend-core regenerates
# bend/core.bend, crates/eukhe-bend/src/entries.rs and
# crates/eukhe-bend/c/core.c from bend/core_entries.txt and bend/ffi_*.bend;
# bend-core-check fails when a committed one differs (or bend is not
# $(BEND_VERSION)). Run bend-core after every change to a bend/ file.
bend-core:
	python3 scripts/bend_core.py generate

bend-core-check:
	python3 scripts/bend_core.py check

# The token blocks of crates/eukhe-dashboard/ui/src/tokens.stylex.ts, as
# the compiled core writes them from bend/tokens.bend (run bend-core first).
dashboard-tokens:
	cargo test -p eukhe-bend --lib rules::tokens::tests::regenerate_dashboard_tokens -- --ignored --exact


# Supply-chain gates. They fail loudly when the tool is missing instead of
# silently skipping the gate.

deny:
	@command -v cargo-deny >/dev/null 2>&1 || { echo "cargo-deny not installed (cargo install cargo-deny --locked)"; exit 1; }
	cargo deny --all-features --workspace check advisories bans licenses sources

# Lints the one workflow file (.github/workflows/eukhe-release.yml).
actionlint:
	@command -v actionlint >/dev/null 2>&1 || { echo "actionlint not installed (see rhysd/actionlint releases)"; exit 1; }
	actionlint .github/workflows/eukhe-release.yml

# GLIBC baseline gate (eukhe-release.yml's build-linux job): a
# GNU/Linux artifact must not require symbols above GLIBC_2.35, the Ubuntu
# 22.04 release baseline. No-op on non-GNU hosts; the authoritative gate runs
# in eukhe-release.yml inside the ubuntu:22.04 build container. POSIX sh throughout: make
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
# (kernel-packaging lane); pass RUNTIME_DIR to re-anchor it. A local build
# reports <workspace version>-dev (eukhe-build-info; only the release
# workflow names a release), so the dry runs package that version.
VERSION := $(shell sed -n 's/^version *= *"\([^"]*\)".*/\1/p' Cargo.toml | head -1)-dev
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
RELEASE_PACKAGE_BUILD = $(RELEASE_CARGO_BUILD)
RELEASE_PACKAGE_FLAGS = --binary $(RELEASE_BINARY) --decoder $(RELEASE_DECODER) --skip-build
GLIBC_BINARY = $(RELEASE_BINARY)
RELEASE_LINK_FLAGS = -C link-arg=-Wl,--build-id
else
RELEASE_ASSEMBLE_FLAGS =
RELEASE_SPLIT = :
RELEASE_VERIFY_DECODER = :
RELEASE_PACKAGE_BUILD = :
RELEASE_PACKAGE_FLAGS =
RELEASE_LINK_FLAGS =
endif

# The release build environment of eukhe-release.yml: commit-time
# SOURCE_DATE_EPOCH, checkout and cargo paths remapped, and on Linux an
# explicit GNU build ID (the split and decoder gates need one; Ubuntu's
# linker adds it by default, Nix's does not). Same commit, toolchain and
# checkout path give the same bytes (Cargo's symbol hashes include the path).
CARGO_HOME_DIR := $(or $(CARGO_HOME),$(HOME)/.cargo)
RELEASE_RUSTFLAGS = --remap-path-prefix=$(CURDIR)=/eukhe --remap-path-prefix=$(CARGO_HOME_DIR)=/cargo $(RELEASE_LINK_FLAGS)
RELEASE_CARGO_BUILD = SOURCE_DATE_EPOCH="$$(git log -1 --format=%ct)" RUSTFLAGS="$(RELEASE_RUSTFLAGS)" cargo build --release --locked --workspace

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
	$(RELEASE_CARGO_BUILD)
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
# tarball layout the binary expects.
catalog-assets-gates:
	python3 scripts/release/test_catalog_assets.py

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

# The dashboard web app: install the locked packages, check (format, lint,
# types), test (`vp test`) and build crates/eukhe-dashboard/ui into
# crates/eukhe-dashboard/web, the committed output that build.rs embeds.
# Run after every UI change.
dashboard-ui:
	cd crates/eukhe-dashboard/ui && npm ci --no-audit --no-fund && npx vp check && npx vp test run && npx vp build

.PHONY: check ci-fast ci-local nightly nightly-status hooks runtime-test laws bend-core bend-core-check dashboard-tokens deny actionlint glibc-gate release-dry-run audit-build package catalog-assets catalog-assets-fixture catalog-pin catalog-assets-gates runtime-lock runtime-lock-check dashboard-ui
