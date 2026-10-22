//! Compiles the compiled Bend core: `c/shim.c`, which includes the generated
//! `c/core.c` (`make bend-core`).

use std::path::PathBuf;

fn main() {
    println!("cargo:rerun-if-changed=c/shim.c");
    println!("cargo:rerun-if-changed=c/core.c");
    let mut build = cc::Build::new();
    build
        .file("c/shim.c")
        .include("c")
        .std("gnu11")
        .opt_level(2);
    // The emitted C jumps between its segments with `__attribute__((musttail))
    // return`: clang compiles it (Bend asks for clang 14+), GCC only from 15
    // (GCC 11, Ubuntu 22.04's cc, rejects it). A cc that cannot, unless CC
    // names it, gives way to `clang`.
    if !musttail() && !explicit_cc() {
        build.compiler("clang");
    }
    build.compile("eukhe_bend");
}

/// Whether the default C compiler (the one `cc::Build::new` picks) takes a
/// `musttail` return statement.
fn musttail() -> bool {
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("cargo sets OUT_DIR"));
    let probe = out.join("musttail_probe.c");
    std::fs::write(
        &probe,
        "int eukhe_bend_probe_f(int x);\n\
         int eukhe_bend_probe_g(int x) { __attribute__((musttail)) return eukhe_bend_probe_f(x); }\n",
    )
    .expect("write the musttail probe");
    cc::Build::new()
        .file(&probe)
        .std("gnu11")
        .cargo_metadata(false)
        .warnings(false)
        .try_compile("eukhe_bend_musttail_probe")
        .is_ok()
}

/// Whether the environment names the C compiler (cc's own lookup keys).
fn explicit_cc() -> bool {
    let target = std::env::var("TARGET").unwrap_or_default();
    [
        "CC".to_owned(),
        "TARGET_CC".to_owned(),
        format!("CC_{target}"),
        format!("CC_{}", target.replace('-', "_")),
    ]
    .iter()
    .any(|key| std::env::var_os(key).is_some())
}
