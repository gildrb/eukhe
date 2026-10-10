//! The `/mcp` view's row model: the service-catalog cards the daemon's
//! `get_mcp_connections` response carries (TS `McpPluginView`), with their
//! render/search projection (the label line, the trailing status, the
//! detail copy, the Enter action hint, and the search-band fields).

use serde_json::Value;

use crate::theme::ThemeColor;

/// One service-catalog card (the daemon's resolved `services` array; TS
/// `McpPluginView`): a catalog service or a user-declared server with its
/// honestly-computed connection state.
#[derive(Debug, Clone, PartialEq)]
pub(super) struct McpServiceRow {
    pub service_id: String,
    pub label: String,
    pub connection_status: String,
    pub connectable: bool,
    pub login_pending: bool,
    pub uses_oauth: bool,
    pub source: String,
    pub connection_ids: Vec<String>,
    /// The paste-panel marker: a requires-setup token service collecting
    /// exactly one credential. Never a connected/verified claim.
    pub paste_token: bool,
    pub aliases: Vec<String>,
    pub description: Option<String>,
    pub category: Option<String>,
    pub publisher: Option<String>,
    pub docs_url: Option<String>,
    pub setup_hint: Option<String>,
    pub tool_count: Option<usize>,
    pub verified_at: Option<u64>,
}

impl McpServiceRow {
    /// Parse one legacy roster entry (a daemon that predates the catalog
    /// surface serves only `connections`): the row keeps the roster's
    /// honest connected state; a not-connected row stays connectable.
    pub(super) fn from_roster_entry(value: &Value) -> Option<Self> {
        let connected = value
            .get("connected")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        Some(McpServiceRow {
            service_id: value.get("server")?.as_str()?.to_string(),
            label: value
                .get("label")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string(),
            connection_status: if connected {
                "connected"
            } else {
                "not_connected"
            }
            .to_string(),
            connectable: !connected,
            login_pending: false,
            uses_oauth: value
                .get("usesOAuth")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            source: "catalog".to_string(),
            connection_ids: Vec::new(),
            paste_token: false,
            aliases: Vec::new(),
            description: None,
            category: None,
            publisher: None,
            docs_url: None,
            setup_hint: None,
            tool_count: None,
            verified_at: None,
        })
    }

    /// Parse one daemon `services` entry.
    pub(super) fn from_value(value: &Value) -> Option<Self> {
        let connection_ids = value
            .get("connectionIds")
            .and_then(Value::as_array)
            .map(|ids| {
                ids.iter()
                    .filter_map(Value::as_str)
                    .map(str::to_string)
                    .collect()
            })
            .unwrap_or_default();
        Some(McpServiceRow {
            service_id: value.get("serviceId")?.as_str()?.to_string(),
            label: value
                .get("label")
                .and_then(Value::as_str)
                .unwrap_or_default()
                .to_string(),
            connection_status: value
                .get("connectionStatus")
                .and_then(Value::as_str)
                .unwrap_or("not_connected")
                .to_string(),
            connectable: value
                .get("connectable")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            login_pending: value
                .get("loginPending")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            uses_oauth: value
                .get("usesOAuth")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            source: value
                .get("source")
                .and_then(Value::as_str)
                .unwrap_or("catalog")
                .to_string(),
            connection_ids,
            paste_token: value
                .get("pasteToken")
                .and_then(Value::as_bool)
                .unwrap_or(false),
            aliases: value
                .get("aliases")
                .and_then(Value::as_array)
                .map(|aliases| {
                    aliases
                        .iter()
                        .filter_map(Value::as_str)
                        .map(str::to_string)
                        .collect()
                })
                .unwrap_or_default(),
            description: value
                .get("description")
                .and_then(Value::as_str)
                .map(str::to_string),
            category: value
                .get("category")
                .and_then(Value::as_str)
                .map(str::to_string),
            publisher: value
                .get("publisher")
                .and_then(Value::as_str)
                .map(str::to_string),
            docs_url: value
                .get("docsUrl")
                .and_then(Value::as_str)
                .map(str::to_string),
            setup_hint: value
                .get("setupHint")
                .and_then(Value::as_str)
                .map(str::to_string),
            tool_count: value
                .get("toolCount")
                .and_then(Value::as_u64)
                .map(|c| c as usize),
            verified_at: value.get("verifiedAt").and_then(Value::as_u64),
        })
    }

    /// The trailing status text (TS `statusText`, catalog mode): the honest
    /// state vocabulary, with the record-carried tool count on connected
    /// rows (the picker reads local state only, like TS).
    pub(super) fn status_text(&self) -> (ThemeColor, String) {
        if self.login_pending {
            return (ThemeColor::Warning, "Login in progress".to_string());
        }
        match self.connection_status.as_str() {
            "connected" => (
                ThemeColor::Success,
                match self.tool_count {
                    Some(tool_count) => format!("Connected - {tool_count} tools"),
                    None => "Connected".to_string(),
                },
            ),
            "pending" => (ThemeColor::Warning, "Needs verification".to_string()),
            "error" => (
                ThemeColor::Error,
                if self.connectable {
                    "Reconnect"
                } else {
                    "Needs attention"
                }
                .to_string(),
            ),
            "setup_required" => (ThemeColor::Warning, "Requires setup".to_string()),
            "disabled" => (ThemeColor::Muted, "Disabled".to_string()),
            _ => (
                if self.connectable {
                    ThemeColor::Text
                } else {
                    ThemeColor::Muted
                },
                if self.connectable {
                    "Connect"
                } else {
                    "Not connected"
                }
                .to_string(),
            ),
        }
    }

    /// The selected row's detail copy (TS `secondaryText`, catalog mode):
    /// the honest setup guidance for setup-required/error rows, the
    /// description otherwise.
    pub(super) fn detail_text(&self) -> Option<String> {
        if self.connection_status == "setup_required" || self.connection_status == "error" {
            self.setup_hint.clone().or_else(|| self.description.clone())
        } else {
            self.description.clone().or_else(|| self.setup_hint.clone())
        }
    }

    /// The action target (the service id).
    pub(super) fn target(&self) -> &str {
        self.service_id.as_str()
    }

    /// The paste-panel decision (TS: a requires-setup token service with
    /// exactly one credential and no installed account).
    pub(super) fn wants_paste(&self) -> bool {
        self.paste_token && self.connection_ids.is_empty()
    }

    /// The Enter action hint (TS `actionText`, catalog mode, in the TS
    /// order): the paste step for pasteable token services, the accounts
    /// step for rows with an account, `manage` for user-declared
    /// non-OAuth servers, then the connection-state verbs.
    pub(super) fn action_text(&self) -> &'static str {
        if self.paste_token && self.connection_ids.is_empty() {
            return "paste token";
        }
        if !self.connection_ids.is_empty() {
            return "manage accounts";
        }
        if self.source == "user" && !self.uses_oauth {
            return "manage";
        }
        match self.connection_status.as_str() {
            "connected" => "re-verify",
            "pending" => "verify",
            _ if !self.connectable => "setup guidance",
            "error" => "reconnect",
            _ => "connect",
        }
    }
}

impl McpServiceRow {
    /// The rendered row's primary line (TS `MenuRow` primary: the label
    /// alone, flattened).
    pub(super) fn primary_line(&self) -> String {
        flatten_to_single_line(&self.label)
    }

    /// The identity fields the search bands rank first.
    pub(super) fn identity_fields(&self) -> Vec<&str> {
        let mut fields = vec![self.label.as_str(), self.service_id.as_str()];
        fields.extend(self.aliases.iter().map(String::as_str));
        fields
    }

    /// The description-band fields (matched only when no identity field
    /// matched).
    pub(super) fn description_fields(&self) -> Vec<&str> {
        self.description
            .iter()
            .chain(self.setup_hint.iter())
            .map(String::as_str)
            .collect()
    }
}

/// Flatten all whitespace runs to one space (TS `flattenToSingleLine`):
/// catalog copy routinely contains newlines, and a rendered row must stay
/// exactly one terminal line.
pub(super) fn flatten_to_single_line(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}
