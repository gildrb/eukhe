//! Settings subsystem: typed settings documents, global/project storage,
//! legacy migrations, the cvar layers (`cvar`, `cfg`), and the manager.

pub(crate) mod cfg;
pub mod cvar;
pub(crate) mod getters;
pub(crate) mod interactive_settings;
pub(crate) mod load;
pub(crate) mod manager;
pub(crate) mod merge;
pub(crate) mod storage;
pub(crate) mod trust;
pub(crate) mod types;

pub use manager::{IdleEviction, SessionArchivePolicy, SettingsError, SettingsManager};
pub use storage::{
    FileSettingsStorage, InMemorySettingsStorage, SettingsScope, SettingsStorage, CONFIG_DIR_NAME,
};
pub use trust::{ProjectTrust, TrustLevel};
pub use types::{
    AutoRefineSettings, AutonomousSettings, CompactionSettings, GatewaySettings, McpServerConfig,
    MemorySettings, QueueModeSetting, Settings, SignalGatewaySettings, ThinkingLevelSetting,
    TransportSetting,
};
