# Merge gate (AGENTS.md): fmt + clippy + test + release build must pass before every merge.
# The tests run as every gate runs them: nextest, one process per test
# (.config/nextest.toml), then the doctests, which nextest does not run.
check:
	cargo fmt --all --check
	cargo clippy --workspace --all-targets --locked -- -D warnings
	@command -v uv >/dev/null 2>&1 || { echo "uv not installed: the real-kernel tests build their venv from eukhe-runtime/uv.lock"; exit 1; }
	cargo nextest run --workspace --locked
	cargo test --workspace --doc --locked
	$(MAKE) runtime-test
	cargo build --release --workspace --locked

# The CI gates (scripts/ci_local.sh). GitHub runs no gate: they run only
# here. ci-fast is the pre-commit gate (< 1 min): rustfmt, the crate
# layering (scripts/check_crate_layers.py), the secrets scan of the staged
# diff (when gitleaks is installed), clippy on the crates the staged change
# touches (scripts/ci_pr_crates.py). The pre-push gate
# (< 5 min) checks the pushed commits: rustfmt, their secrets scan, clippy
# and the unit tests (nextest profile pre-push, .config/nextest.toml: no
# e2e suite) of the crates they touch, the proofs their Bend change can
# reach (scripts/bend_proofs.py), the laws against LAWS.lock. ci-local is
# the full gate (< 30 min): every test (nextest profile nightly) and `bend
# PROOF.bend --verdict`; the nightly run (scripts/ci_nightly.sh, a systemd
# user timer) runs it on origin/main and starts the release only when it
# passes. lock re-locks the laws in seconds: the proofs the change since
# origin/main can reach, then LAWS.lock. Tools: mise.toml.
# `make hooks` makes git run the hooks through prek (.pre-commit-config.yaml;
# the hooks are in the git common dir, so every worktree shares them; a
# worktree of an older commit, without the config, skips them).
ci-fast:
	@scripts/ci_local.sh fast

ci-local:
	@scripts/ci_local.sh full

lock:
	@scripts/ci_local.sh lock

nightly:
	@scripts/ci_nightly.sh run

nightly-status:
	@scripts/ci_nightly.sh status

hooks:
	@command -v prek >/dev/null 2>&1 || { echo "prek not installed (mise use -g github:j178/prek@0.5.7)"; exit 1; }
	prek install --allow-missing-config --hook-type pre-commit --hook-type pre-push

# The eukhe-runtime Python suite on the uv-locked kernel env (the env the
# real-kernel cargo tests build: crates/eukhe-core/tests/support/kernel_runtime.rs).
runtime-test:
	UV_PROJECT_ENVIRONMENT=$(CURDIR)/target/runtime-venv uv run --no-config --locked --group kernel --python 3.14 --project eukhe-runtime python -m unittest discover -s eukhe-runtime/test

# The Home Manager module's settings merge (nix/merge-settings.sh): the
# declared settings never drop the model choice eukhe saved. Needs jq.
nix-test:
	python3 nix/test_merge_settings.py

# The pinned Bend and Lean releases: BEND_VERSION, LEAN_VERSION.
include scripts/toolchain.env

# The laws (LAWS.bend, proven in PROOF.bend). The full gate
# (ci-local) runs them too. --verdict needs Lean $(LEAN_VERSION). Every Bend
# target runs the pinned Bend $(BEND_VERSION) (scripts/pinned_bend.sh).
laws:
	@bend="$$(scripts/pinned_bend.sh)" && \
	"$$bend" PROOF.bend | tee /dev/stderr | grep -qx 'ALL PROOFS CHECK' && \
	"$$bend" PROOF.bend --verdict | tee /dev/stderr | grep -qx 'ALL PROOFS CHECK'

# The compiled Bend core (crates/eukhe-bend): bend-core regenerates
# bend/core.bend, crates/eukhe-bend/src/entries.rs and
# crates/eukhe-bend/c/core.c from bend/core_entries.txt and bend/ffi_*.bend;
# bend-core-check fails when a committed one differs. Run bend-core after
# every change to a bend/ file.
bend-core:
	BEND_BIN="$$(scripts/pinned_bend.sh)" && export BEND_BIN && python3 scripts/bend_core.py generate

bend-core-check:
	BEND_BIN="$$(scripts/pinned_bend.sh)" && export BEND_BIN && python3 scripts/bend_core.py check

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
# time, never committed. The models asset is always made offline from the
# pinned models.dev snapshot in crates/eukhe-models/catalog
# (scripts/release/models_dev.py). The release workflow fetches the MCP
# services at the catalog commit pinned in scripts/release/catalog-pin.json
# and checks its sha256 (`--network`). The local dry-runs default to the
# synthetic services fixture (it passes the full packer gates: >= 20
# transport tuples, >= 68 services); CATALOG_ASSETS_MODE=network switches
# them to the pinned fetch for packaging parity.
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

# Offline asset generation: the synthetic full-gate services fixture.
catalog-assets-fixture:
	python3 scripts/release/bundle_catalog.py generate --fixture --out $(CATALOG_ASSETS_DIR)

# Move the catalog pin (scripts/release/catalog-pin.json) to the catalog
# repo's current CATALOG_REF (default main): resolves the commit, fetches
# the services file at it, runs the full validation gates, and records the
# commit and its sha256. Review the diff before committing it.
CATALOG_REF ?= main
catalog-pin:
	python3 scripts/release/bundle_catalog.py pin --ref $(CATALOG_REF)

# Move the models.dev snapshot (crates/eukhe-models/catalog) to MODELS_DEV_REF
# (default main; needs git and bun): builds models.dev's v1 API at that
# commit, rewrites the snapshot and its pin (commit, date, sha256), and
# regenerates the catalog fixture. Review the diff before committing it.
MODELS_DEV_REF ?= main
models-dev-pin:
	python3 scripts/release/models_dev.py refresh --commit $(MODELS_DEV_REF)
	python3 scripts/generate-catalog-fixture.py

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

# Bundled-catalog gates (scripts/release/test_catalog_assets.py and
# test_models_dev.py): the offline fixture passes the full packer
# validation, the packer hard-fails on missing/invalid assets, network mode
# is verified against a local HTTP server (including the pinned-sha256
# check), the assets land in the tarball layout the binary expects, and the
# models.dev mapping and its committed fixture agree.
catalog-assets-gates:
	python3 scripts/release/test_catalog_assets.py
	python3 scripts/release/test_models_dev.py

# Eukhe's package lock: eukhe-runtime/uv.lock (the `kernel` group, resolved
# for the pinned Python of eukhe-runtime/kernel-toolchain.json) exported to
# eukhe-runtime/requirements-kernel.txt, the only file a kernel installs
# Eukhe's packages from, on demand. runtime-lock re-resolves (network) and re-exports;
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

# The benchmark suite (bench/README.md): real model calls that cost money,
# never run by CI. The release build lands in this checkout's target/ (not
# $CARGO_TARGET_DIR): a binary inside its checkout finds the checkout's
# skills/ and eukhe-runtime/. BENCH_FLAGS passes bench flags (--dir, --model, …).
BENCH_TOOLS ?= eukhe
BENCH_TASKS ?= all
BENCH_RUNS ?= 1
BENCH_PAR ?= 4
BENCH_FLAGS ?=
BENCH_QUICK_TASKS ?= crm

bench-build:
	cargo build --release --locked -p eukhe-cli --target-dir target

bench: bench-build
	python3 bench/batch.py --tools $(BENCH_TOOLS) --tasks $(BENCH_TASKS) --runs $(BENCH_RUNS) --par $(BENCH_PAR) $(BENCH_FLAGS)
	python3 bench/report.py $(BENCH_FLAGS)

# A cheap check that the suite runs end to end: BENCH_QUICK_TASKS once, every
# model call on claude-haiku-5-5.
bench-quick: bench-build
	python3 bench/batch.py --tools eukhe --tasks $(BENCH_QUICK_TASKS) --runs 1 --par $(BENCH_PAR) --model haiku --rerun $(BENCH_FLAGS)
	python3 bench/report.py --tasks $(BENCH_QUICK_TASKS) --labels eukhe-haiku $(BENCH_FLAGS)

# The website (site/, eukhe.com; site/README.md): apart from eukhe but for
# reading the repository's files (README.md and what it links to) when it
# builds. Its own toolchain (npm, site/package-lock.json), laws
# (site/LAWS.bend, site/LAWS.lock) and check; no gate, hook, nightly run or
# release runs these. site-check: install, format/lint/types, the site's
# laws, the build. site-deploy: install, the build, then `wrangler deploy`
# (site/wrangler.jsonc: the eukhe-site Worker on eukhe.com and
# www.eukhe.com). A deploy happens only here, by hand.
site-check:
	cd site && npm ci --no-audit --no-fund && npm run check && npm run laws && npm run build

site-deploy:
	cd site && npm ci --no-audit --no-fund && npm run deploy

.PHONY: check ci-fast ci-local lock nightly nightly-status hooks runtime-test nix-test laws bend-core bend-core-check dashboard-tokens deny actionlint glibc-gate release-dry-run audit-build package catalog-assets catalog-assets-fixture catalog-pin models-dev-pin catalog-assets-gates runtime-lock runtime-lock-check dashboard-ui bench-build bench bench-quick site-check site-deploy
