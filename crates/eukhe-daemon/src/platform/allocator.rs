//! The allocator options of the daemon's processes: the supervisor the
//! client launches and the session workers the supervisor spawns.
//!
//! mimalloc (the global allocator of the `eukhe` and `eukhe-daemon`
//! images) reads its options from the environment once, at its first
//! allocation, before `main`; an option-setting call would need `unsafe`
//! FFI, which the workspace forbids. So each launch hands its child the
//! options through the child's environment.

/// mimalloc's purge delay in milliseconds: how long a page a free empties
/// stays committed before mimalloc returns it to the OS. A purge runs only
/// when a later allocation needs a fresh page past the delay, so with the
/// default (1 s) the transient peaks of a run or an attach (request JSON,
/// attach snapshots) mostly stayed resident while the process idled. At
/// 250 ms more of them go back; shorter delays return more still but
/// re-fault the pages each turn reuses (`ram_map.py` turns-50 worker: 0
/// ms cut 27 MB at +30 % CPU, 250 ms 11 MB within the run-to-run CPU spread).
const PURGE_DELAY: (&str, &str) = ("MIMALLOC_PURGE_DELAY", "250");

/// Marks a launch env whose options [`set_allocator_options`] added (not
/// the user), so the child takes them back out ([`take_allocator_options`]).
const SET_BY_LAUNCH_ENV: &str = "EUKHE_ALLOCATOR_OPTIONS_SET";

/// Gives `command` the daemon processes' allocator options, unless this
/// process's own environment sets the option (the user's setting reaches
/// the child unchanged).
pub fn set_allocator_options(command: &mut std::process::Command) {
    let (name, value) = PURGE_DELAY;
    if std::env::var_os(name).is_none() {
        command.env(name, value).env(SET_BY_LAUNCH_ENV, "1");
    }
}

/// Removes the options a launch added from this process's environment;
/// call it at the start of `main`, while the process is single-threaded.
/// mimalloc read them before `main`; the process's own children (tool
/// commands, kernels, tiny workers) never see them, and a supervisor's
/// workers get them again from [`set_allocator_options`]. A user's own
/// setting carries no marker and stays.
pub fn take_allocator_options() {
    if std::env::var_os(SET_BY_LAUNCH_ENV).is_some() {
        std::env::remove_var(PURGE_DELAY.0);
        std::env::remove_var(SET_BY_LAUNCH_ENV);
    }
}
