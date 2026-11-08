// mimalloc returns freed pages to the OS and keeps no per-thread glibc
// arena sprawl, so session-load and attach-snapshot bursts do not stay
// resident (it replaces the glibc mallopt/malloc_trim tuning, which had
// no safe binding).
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    // A closed stdout (`eukhe list | head -1`) must end the run quietly
    // with exit 0, not a panic report (exit 101): every print macro panics
    // on the broken pipe, so the hook recognizes it and exits before any
    // error output. Everything else keeps the default report.
    let default_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        let broken_pipe = info
            .payload()
            .downcast_ref::<String>()
            .is_some_and(|message| message.contains("Broken pipe"))
            || info
                .payload()
                .downcast_ref::<&str>()
                .is_some_and(|message| message.contains("Broken pipe"));
        if broken_pipe {
            std::process::exit(0);
        }
        default_hook(info);
    }));
    // A launcher that asked for a detached session (the daemon spawn)
    // gets it before anything else runs, while the process is still
    // single-threaded.
    if let Err(error) = eukhe_core::platform::process::enter_requested_session() {
        eprintln!("Error: starting a new session failed: {error}");
        std::process::exit(1);
    }
    // The cvar table is checked here, before any session runs: a table that
    // declares an id twice or a default of the wrong type stops eukhe now.
    let _ = eukhe_core::settings::cvar::registry();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let code = eukhe_cli::main_with_runtime(&args, &eukhe_cli::PrintRuntime);
    std::process::exit(code);
}
