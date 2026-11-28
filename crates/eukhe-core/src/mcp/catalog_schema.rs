//! Strict schema for one MCP service entry: the compiled built-ins and the
//! user-authored `mcp-services.json` local sources (v1), validated with the
//! shipped TS contract (`packages/ai/src/mcp/catalog.ts`
//! `validateMcpServiceEntry`).
//!
//! Fail-closed: any unknown key, wrong type, or broken invariant rejects the
//! entry (`deny_unknown_fields`: additive schema changes require a version
//! bump).

use serde::Deserialize;

/// One catalog entry = one reviewed connection (endpoint) of a service
/// (spec §1.2; TS `McpServiceEntry`). `server` is the stable id, the kernel
/// dispatch id, and the `mcp:<server>` credential key.
#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct McpServiceEntry {
    pub server: String,
    /// Brand grouping id; defaults to `server` in the aggregate.
    pub service: String,
    pub label: String,
    /// Default reviewed endpoint; empty for stdio/tenant-template transports.
    pub url: String,
    pub description: Option<String>,
    pub category: Option<String>,
    pub publisher: Option<String>,
    pub homepage: Option<String>,
    pub docs_url: Option<String>,
    pub privacy_url: Option<String>,
    pub support_url: Option<String>,
    /// Lowercase, sorted, distinct from the server id.
    pub aliases: Vec<String>,
    pub transport: McpServiceTransport,
    pub auth: McpServiceAuth,
    pub setup: McpServiceSetup,
    pub verification: McpServiceVerification,
    /// True only for legacy built-in integrations (linear, notion); their ids
    /// stay reserved — local sources can never shadow them.
    pub legacy_builtin: bool,
    pub provenance: Vec<McpServiceProvenance>,
    /// OAuth-strategy entries only; never carries a client id or secret
    /// (both keys are rejected).
    pub oauth: Option<McpServiceOauth>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(tag = "type", rename_all = "kebab-case", deny_unknown_fields)]
pub enum McpServiceTransport {
    #[serde(rename_all = "camelCase")]
    Http { url: String },
    #[serde(rename_all = "camelCase")]
    HttpTemplate {
        template: String,
        variables: Vec<TemplateVariable>,
    },
    #[serde(rename_all = "camelCase")]
    Sse { url: String },
    #[serde(rename_all = "camelCase")]
    Stdio { servers: Vec<StdioServerDef> },
}

impl McpServiceTransport {
    /// The concrete HTTP/SSE endpoint when the transport carries one.
    pub fn endpoint(&self) -> Option<&str> {
        match self {
            McpServiceTransport::Http { url } | McpServiceTransport::Sse { url } => {
                Some(url.as_str())
            }
            McpServiceTransport::HttpTemplate { .. } | McpServiceTransport::Stdio { .. } => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TemplateVariable {
    pub name: String,
    pub description: String,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StdioServerDef {
    pub name: String,
    pub command: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub args: Option<Vec<String>>,
    #[serde(default)]
    pub env: Option<std::collections::BTreeMap<String, String>>,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct McpServiceAuth {
    pub strategy: AuthStrategy,
    pub client_registration: ClientRegistration,
    /// Reviewed upstream scope hints; the connect flow joins them into the
    /// requested scopes only when nothing is configured.
    #[serde(default)]
    pub reviewed_scopes: Option<Vec<String>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthStrategy {
    Oauth,
    ApiKey,
    None,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ClientRegistration {
    Dynamic,
    #[serde(rename = "pre-registered")]
    PreRegistered,
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct McpServiceSetup {
    pub status: SetupStatus,
    /// Required on `requires-setup` entries (picker copy).
    pub reason: Option<String>,
    /// Setup fields the entry collects; credential kinds drive the paste flow.
    #[serde(default)]
    pub fields: Option<Vec<McpSetupField>>,
    /// INFORMATIONAL readiness; never a connect gate.
    pub readiness: Option<Readiness>,
    pub requirement: Option<SetupRequirement>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SetupStatus {
    Ready,
    #[serde(rename = "requires-setup")]
    RequiresSetup,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Readiness {
    #[serde(rename = "oauth-ready")]
    OauthReady,
    #[serde(rename = "user-setup")]
    UserSetup,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SetupRequirement {
    #[serde(rename = "api-key")]
    ApiKey,
    #[serde(rename = "bearer-token")]
    BearerToken,
    #[serde(rename = "registered-client")]
    RegisteredClient,
    Tenant,
    #[serde(rename = "unsupported-transport")]
    UnsupportedTransport,
    #[serde(rename = "local-runtime")]
    LocalRuntime,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct McpSetupField {
    pub id: String,
    pub label: String,
    pub description: Option<String>,
    pub required: bool,
    /// What the field collects; absent means the importer had no signal.
    pub kind: Option<SetupFieldKind>,
    /// Fields sharing a credential-set id are ALTERNATIVE NAMES for one
    /// credential (GitHub's `GITHUB_PAT_TOKEN` / `GITHUB_PERSONAL_ACCESS_TOKEN`).
    #[serde(rename = "credentialSet", default)]
    pub credential_set: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum SetupFieldKind {
    #[serde(rename = "env-var")]
    EnvVar,
    Url,
    #[serde(rename = "client-id")]
    ClientId,
    #[serde(rename = "client-secret")]
    ClientSecret,
    #[serde(rename = "bearer-token")]
    BearerToken,
    #[serde(rename = "api-key")]
    ApiKey,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct McpServiceVerification {
    pub status: VerificationStatus,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum VerificationStatus {
    #[serde(rename = "metadata-reviewed")]
    MetadataReviewed,
    Unverified,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct McpServiceProvenance {
    pub source: ProvenanceSource,
    pub repository: Option<String>,
    pub commit: Option<String>,
    pub path: Option<String>,
    pub url: Option<String>,
    pub license: Option<String>,
    pub note: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ProvenanceSource {
    Builtin,
    User,
}

#[derive(Debug, Clone, PartialEq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct McpServiceOauth {
    /// Literal `"oauth"` marker.
    pub kind: OauthKind,
    pub scopes: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Deserialize)]
pub enum OauthKind {
    #[serde(rename = "oauth")]
    Oauth,
}

/// A bounded echo of an entry id in errors: never reprint untrusted long
/// (possibly secret-ish) input.
fn safe_entry_id(entry_id: &str) -> String {
    if entry_id.len() > 64 {
        format!("{}...", &entry_id[..entry_id.floor_char_boundary(64)])
    } else {
        entry_id.to_string()
    }
}

/// Why one catalog entry is invalid: its (bounded) id and the broken rule.
#[derive(Debug, thiserror::Error)]
#[error("catalog entry {entry}: {fault}")]
pub struct CatalogEntryError {
    /// The entry id, bounded by [`safe_entry_id`].
    pub entry: String,
    #[source]
    pub fault: CatalogEntryFault,
}

/// The rule a catalog entry breaks. Never echoes the input value: it may
/// carry query tokens or secrets.
#[derive(Debug, thiserror::Error)]
pub enum CatalogEntryFault {
    #[error("{field} must be a non-empty string")]
    Empty { field: &'static str },
    #[error("{field} is not an absolute URL")]
    NotAbsoluteUrl {
        field: &'static str,
        #[source]
        source: url::ParseError,
    },
    #[error("{field} must be an absolute HTTPS URL without credentials or a fragment")]
    UnsafeUrl { field: &'static str },
    #[error("{field} host could not be checked: {source}")]
    HostCheck {
        field: &'static str,
        #[source]
        source: eukhe_bend::Error,
    },
    #[error("{field} must not be a literal loopback, private, link-local or unspecified endpoint")]
    PrivateHost { field: &'static str },
    #[error("server id must match ^[a-z0-9][a-z0-9-]{{0,63}}$")]
    ServerId,
    #[error("url must equal transport.url")]
    UrlMismatch,
    #[error("http-template transports need at least one variable")]
    NoTemplateVariables,
    #[error("url must be empty for http-template transports")]
    TemplateUrl,
    #[error("stdio transports need at least one server")]
    NoStdioServers,
    #[error("url must be empty for stdio transports")]
    StdioUrl,
    #[error("requires-setup entries need a reason")]
    SetupReason,
    #[error("oauth is only allowed on oauth-strategy entries")]
    OauthStrategy,
    #[error("aliases must be lowercase strings distinct from the server id")]
    AliasCase,
    #[error("aliases must be sorted and unique")]
    AliasOrder,
    #[error("provenance must be a non-empty array")]
    NoProvenance,
}

impl CatalogEntryError {
    fn new(entry_id: &str, fault: CatalogEntryFault) -> Self {
        CatalogEntryError {
            entry: safe_entry_id(entry_id),
            fault,
        }
    }
}

fn require_string(
    entry_id: &str,
    field: &'static str,
    value: &str,
) -> Result<String, CatalogEntryError> {
    if value.is_empty() {
        Err(CatalogEntryError::new(
            entry_id,
            CatalogEntryFault::Empty { field },
        ))
    } else {
        Ok(value.to_string())
    }
}

fn require_https_url(
    entry_id: &str,
    field: &'static str,
    url: &str,
) -> Result<String, CatalogEntryError> {
    require_string(entry_id, field, url)?;
    let fail = |fault| CatalogEntryError::new(entry_id, fault);
    let parsed = url::Url::parse(url)
        .map_err(|source| fail(CatalogEntryFault::NotAbsoluteUrl { field, source }))?;
    let has_credentials = parsed.username().is_empty() && parsed.password().is_none();
    if parsed.scheme() != "https" || !has_credentials || parsed.fragment().is_some() {
        return Err(fail(CatalogEntryFault::UnsafeUrl { field }));
    }
    let refused = eukhe_bend::rules::mcp_url::literal_private_or_loopback(
        parsed.host_str().unwrap_or_default(),
    )
    .map_err(|source| fail(CatalogEntryFault::HostCheck { field, source }))?;
    if refused {
        return Err(fail(CatalogEntryFault::PrivateHost { field }));
    }
    Ok(url.to_string())
}

impl McpServiceEntry {
    /// Structural validation for one entry (TS `validateMcpServiceEntry`):
    /// id pattern, transport/url consistency, aliases rules, setup honesty,
    /// and the no-secrets invariant. Unknown keys were already rejected by
    /// `deny_unknown_fields` at the serde layer.
    pub fn validate(&self) -> Result<(), CatalogEntryError> {
        let at = safe_entry_id(&self.server);
        let fail = |fault| Err(CatalogEntryError::new(&at, fault));
        require_string(&at, "server", &self.server)?;
        if !server_id_valid(&self.server) {
            return fail(CatalogEntryFault::ServerId);
        }
        require_string(&at, "label", &self.label)?;
        require_string(&at, "service", &self.service)?;
        match &self.transport {
            McpServiceTransport::Http { url } | McpServiceTransport::Sse { url } => {
                let endpoint = require_https_url(&at, "transport.url", url)?;
                if self.url != endpoint {
                    return fail(CatalogEntryFault::UrlMismatch);
                }
            }
            McpServiceTransport::HttpTemplate {
                template,
                variables,
            } => {
                require_string(&at, "transport.template", template)?;
                if variables.is_empty() {
                    return fail(CatalogEntryFault::NoTemplateVariables);
                }
                for variable in variables {
                    require_string(&at, "transport.variables[].name", &variable.name)?;
                    require_string(
                        &at,
                        "transport.variables[].description",
                        &variable.description,
                    )?;
                }
                if !self.url.is_empty() {
                    return fail(CatalogEntryFault::TemplateUrl);
                }
            }
            McpServiceTransport::Stdio { servers } => {
                if servers.is_empty() {
                    return fail(CatalogEntryFault::NoStdioServers);
                }
                for server in servers {
                    require_string(&at, "transport.servers[].name", &server.name)?;
                    require_string(&at, "transport.servers[].command", &server.command)?;
                }
                if !self.url.is_empty() {
                    return fail(CatalogEntryFault::StdioUrl);
                }
            }
        }
        for scope in self.auth.reviewed_scopes.iter().flatten() {
            require_string(&at, "auth.reviewedScopes[]", scope)?;
        }
        if self.setup.status == SetupStatus::RequiresSetup
            && self.setup.reason.as_deref().is_none_or(str::is_empty)
        {
            return fail(CatalogEntryFault::SetupReason);
        }
        for field in self.setup.fields.iter().flatten() {
            require_string(&at, "setup.fields[].id", &field.id)?;
            require_string(&at, "setup.fields[].label", &field.label)?;
            if let Some(credential_set) = &field.credential_set {
                require_string(&at, "setup.fields[].credentialSet", credential_set)?;
            }
        }
        if let Some(oauth) = &self.oauth {
            if self.auth.strategy != AuthStrategy::Oauth {
                return fail(CatalogEntryFault::OauthStrategy);
            }
            if let Some(scopes) = &oauth.scopes {
                require_string(&at, "oauth.scopes", scopes)?;
            }
        }
        let server = &self.server;
        for alias in &self.aliases {
            if alias.to_lowercase() != *alias || alias == server {
                return fail(CatalogEntryFault::AliasCase);
            }
        }
        for pair in self.aliases.windows(2) {
            if pair[0] >= pair[1] {
                return fail(CatalogEntryFault::AliasOrder);
            }
        }
        if self.provenance.is_empty() {
            return fail(CatalogEntryFault::NoProvenance);
        }
        Ok(())
    }
}

/// Stable service id pattern (also the kernel dispatch id grammar).
pub(crate) fn server_id_valid(server: &str) -> bool {
    let mut chars = server.chars();
    let first = match chars.next() {
        Some(first) if first.is_ascii_lowercase() || first.is_ascii_digit() => first,
        _ => return false,
    };
    let _ = first;
    let rest = chars.as_str();
    rest.chars().count() <= 63
        && rest
            .chars()
            .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

/// The compiled built-in services: the integrations whose ids stay reserved
/// (`linear`, `notion`; metadata-reviewed OAuth dynamic-client services).
pub fn compiled_builtin_services() -> Vec<McpServiceEntry> {
    let json = serde_json::json!([
        {
            "server": "linear",
            "service": "linear",
            "label": "Linear",
            "url": "https://mcp.linear.app/mcp",
            "description": "Search, create and update Linear issues, projects, and initiatives. Draft PRDs, write updates, analyze customer requests, and keep plans up to date \u{2014} all from within ChatGPT",
            "category": "Productivity",
            "publisher": "Linear",
            "homepage": "https://linear.app/",
            "privacyUrl": "https://linear.app/privacy",
            "supportUrl": "https://linear.app/contact",
            "aliases": ["linear-app"],
            "transport": { "type": "http", "url": "https://mcp.linear.app/mcp" },
            "auth": { "strategy": "oauth", "clientRegistration": "dynamic" },
            "setup": { "status": "ready", "readiness": "oauth-ready" },
            "verification": { "status": "metadata-reviewed" },
            "legacyBuiltin": true,
            "provenance": [{ "source": "builtin" }],
            "oauth": { "kind": "oauth" }
        },
        {
            "server": "notion",
            "service": "notion",
            "label": "Notion",
            "url": "https://mcp.notion.com/mcp",
            "description": "Notion workflows for implementation planning, research synthesis, meeting preparation, and knowledge capture.",
            "category": "Productivity",
            "publisher": "Notion",
            "homepage": "https://www.notion.so/",
            "privacyUrl": "https://www.notion.com/help/privacy",
            "aliases": ["notion-workspace"],
            "transport": { "type": "http", "url": "https://mcp.notion.com/mcp" },
            "auth": { "strategy": "oauth", "clientRegistration": "dynamic" },
            "setup": { "status": "ready", "readiness": "oauth-ready" },
            "verification": { "status": "metadata-reviewed" },
            "legacyBuiltin": true,
            "provenance": [{ "source": "builtin" }],
            "oauth": { "kind": "oauth" }
        }
    ]);
    let entries: Vec<McpServiceEntry> =
        serde_json::from_value(json).expect("compiled builtin catalog entries are valid");
    for entry in &entries {
        entry.validate().expect("compiled builtin entries validate");
    }
    entries
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression: an IPv4-mapped loopback endpoint is refused. The url
    /// crate spells `[::ffff:127.0.0.1]` as `[::ffff:7f00:1]`, which the
    /// Rust check passed (its mapped test could never hold); the compiled
    /// core (`laws/mcp_url.bend`) refuses it, like the plain loopback, and
    /// a public host passes.
    #[test]
    fn mapped_loopback_endpoints_are_refused() {
        let check =
            |url: &str| require_https_url("svc", "url", url).map_err(|error| error.to_string());
        let refused = "catalog entry svc: url must not be a literal loopback, private, link-local or unspecified endpoint".to_string();
        assert_eq!(
            [
                check("https://[::ffff:127.0.0.1]/mcp"),
                check("https://127.0.0.1/mcp"),
                check("https://mcp.linear.app/mcp"),
            ],
            [
                Err(refused.clone()),
                Err(refused),
                Ok("https://mcp.linear.app/mcp".to_string()),
            ]
        );
    }

    /// A long id whose 64th byte falls inside a multi-byte char truncates
    /// at the char boundary instead of panicking.
    #[test]
    fn safe_entry_id_cuts_long_ids_on_a_char_boundary() {
        let id = format!("{}{}", "a".repeat(63), "\u{e9}".repeat(4));
        assert_eq!(safe_entry_id(&id), format!("{}...", "a".repeat(63)));
    }
}
