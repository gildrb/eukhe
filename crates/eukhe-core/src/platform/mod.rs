//! eukhe-core platform wall: every OS-specific behavior behind small
//! functions in dedicated modules (MISSION.md). Linux and macOS differences
//! live behind the same signatures; call sites in the session engine never
//! branch on `cfg` themselves.

pub mod browser;
pub mod fs;
pub mod local_time;
pub mod lock_dir;
pub mod perms;
pub mod process;
pub mod shell;

pub use fs::fsync;
pub use local_time::{local_time, parse_utc_iso, LocalTime};
pub use lock_dir::LockDir;
pub use perms::{
    file_mode, is_executable, is_readable_writable, restrict_dir, restrict_file, set_private_mode,
};
pub use process::{
    kill_pid, kill_process_group_or_pid, pid_exists, set_new_process_group, termination_signal,
    Signal,
};
pub use shell::{get_shell_config, resolve_kernel_bash_shell, ShellConfig};
