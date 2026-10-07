//! Built-in coding tools (`pi-durable/tools`). Port of `tools/index.ts`.

mod bash;
mod edit;
mod edit_diff;
mod env;
mod file_mutation_queue;
mod image;
mod path_utils;
mod read;
#[cfg(test)]
mod tests;
mod write;

use std::sync::{Arc, LazyLock};

pub use bash::{
    create_bash_tool, create_powershell_tool, BashExecution, BashPrepare, BashToolInput,
    BashToolOptions, PowerShellToolInput, PowerShellToolOptions,
};
pub use edit::{create_edit_tool, EditToolDetails, EditToolInput, ReplaceEdit};
pub use read::{create_read_tool, ReadToolDetails, ReadToolInput, ReadTruncation};
pub use write::{create_write_tool, WriteToolInput};

use crate::harness::define::define_extension;
use crate::harness::types::Extension;

/// `read`, `write`, `edit`, and `bash`; nothing installs it automatically.
/// `create_powershell_tool()` adds `powershell`.
pub static CODING_TOOLS: LazyLock<Arc<Extension>> = LazyLock::new(|| {
    define_extension(Extension {
        name: "coding-tools".to_owned(),
        tools: vec![
            create_read_tool(),
            create_write_tool(),
            create_edit_tool(),
            create_bash_tool(BashToolOptions::default()),
        ],
        ..Extension::default()
    })
});
