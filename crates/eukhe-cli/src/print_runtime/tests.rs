// --- print-mode MCP wiring (TS `createAgentSessionServices` parity) ---

/// The arm records the routed target it writes, so the settle
/// restores the captured session target only while the slot still
/// holds the route; a mid-run `/model` switch rewrote the slot with
/// the new session target, and the settle must leave it (the
/// regression this pins: the arm once skipped the `armed_to` write,
/// so the settle's still-routed guard always passed and dragged the
/// slot back to the pre-route session target).
#[test]
fn headless_image_router_settle_preserves_a_mid_run_model_switch() {
    fn fixture_model(id: &str) -> eukhe_types::ai::Model {
        eukhe_types::ai::Model {
            id: id.to_string(),
            name: id.to_string(),
            api: "anthropic-messages".to_string(),
            provider: "anthropic".to_string(),
            base_url: "https://x".to_string(),
            reasoning: true,
            thinking_level_map: None,
            input: vec![
                eukhe_types::ai::ModelInput::Text,
                eukhe_types::ai::ModelInput::Image,
            ],
            cost: eukhe_types::ai::ModelCost {
                input: 1.0.into(),
                output: 2.0.into(),
                cache_read: 0.0.into(),
                cache_write: 0.0.into(),
            },
            context_window: 200_000,
            max_tokens: 8192,
            featured: None,
            headers: None,
            compat: None,
        }
    }
    fn target(
        model: eukhe_types::ai::Model,
    ) -> eukhe_core::session_engine::provider_adapter::ProviderTarget {
        eukhe_core::session_engine::provider_adapter::ProviderTarget {
            model,
            service_tier: None,
        }
    }
    let home = tempfile::TempDir::new().unwrap();
    let agent_dir = home.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    let session_model = fixture_model("session-model");
    let provider_target =
        std::sync::Arc::new(std::sync::RwLock::new(Some(target(session_model.clone()))));
    let armed_target: std::sync::Arc<
        std::sync::Mutex<Option<eukhe_core::session_engine::provider_adapter::ProviderTarget>>,
    > = std::sync::Arc::new(std::sync::Mutex::new(None));
    let router = super::headless_image_model_router(
        &provider_target,
        std::sync::Arc::clone(&armed_target),
        home.path().to_path_buf(),
        agent_dir,
        session_model,
    );
    let expected_route = eukhe_core::models::ResolvedImageModel {
        model: fixture_model("image-model"),
        thinking_level: eukhe_types::ai::ModelThinkingLevel::High,
        service_tier: None,
    };
    // Arm: the slot now serves the routed image model.
    (router.swap_target)(Some(&expected_route));
    assert_eq!(
        provider_target.read().unwrap().as_ref().unwrap().model.id,
        "image-model"
    );
    // A mid-run `/model` switch rewrites the live slot with the new
    // session target while the route is still armed.
    let switched_to = target(fixture_model("switched-model"));
    *provider_target.write().unwrap() = Some(switched_to);
    // Settle: the switch wins; the settle must not drag the slot back
    // to the pre-route session target.
    (router.swap_target)(None);
    assert_eq!(
        provider_target.read().unwrap().as_ref().unwrap().model.id,
        "switched-model"
    );
    // The next episode captures the live slot at ITS first arm, so its
    // baseline is the post-switch session model: the plain arm ->
    // serve -> settle contract restores that baseline (the
    // capture-at-arm, restore-at-settle pair).
    (router.swap_target)(Some(&expected_route));
    (router.swap_target)(None);
    assert_eq!(
        provider_target.read().unwrap().as_ref().unwrap().model.id,
        "switched-model"
    );
}

/// The print session's MCP manager serves a settings-declared server
/// through the `mcp.config` host request the kernel dispatches
/// (`rlm/mcp.py` resolution), and resolves its settings LIVE: a
/// settings rewrite reaches the next `refresh()` -- the re-resolver
/// the remote-catalog change subscription drives mid-session. The
/// `mcp.config` handler itself keeps the registration-time
/// integrations (the eukhe-core handler design, shared with the daemon
/// worker), so the pre-refresh handler still answers the old roster --
/// asserted here so the test states the real production behavior.
#[tokio::test]
async fn print_mode_mcp_manager_serves_settings_servers_and_resolves_live() {
    let home = tempfile::TempDir::new().unwrap();
    let cwd = home.path().to_path_buf();
    let agent_dir = home.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "mcpServers": {
                "fixture-echo": {
                    "type": "stdio",
                    "command": "python3",
                    "args": ["echo.py"]
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    let built_manager = crate::mcp_login::cli_mcp_manager(&cwd, &agent_dir);
    assert_eq!(
        built_manager.get_enabled_persistent_generic_servers(),
        vec!["fixture-echo".to_string()]
    );
    let manager = std::sync::Arc::new(std::sync::Mutex::new(built_manager));
    // The kernel's config host request serves the declared server with
    // the declared stdio config (registration-time integrations).
    let mut handlers = eukhe_core::kernel::shared::HostRequestHandlers::default();
    eukhe_core::mcp::McpManager::register_host_handlers(&manager, &mut handlers);
    let config = handlers.get("mcp.config").unwrap().clone();
    let result = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "fixture-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert_eq!(result["type"], "stdio");
    assert_eq!(result["command"], "python3");
    assert_eq!(result["args"], serde_json::json!(["echo.py"]));
    // A settings rewrite reaches the same manager on the next refresh:
    // the closures re-read settings per resolution.
    std::fs::write(
        agent_dir.join("settings.json"),
        serde_json::json!({
            "mcpServers": {
                "second-echo": {
                    "type": "stdio",
                    "command": "node",
                    "args": ["echo.mjs"]
                }
            }
        })
        .to_string(),
    )
    .unwrap();
    {
        let mut manager = manager.lock().unwrap();
        manager.refresh();
        assert_eq!(
            manager.get_enabled_persistent_generic_servers(),
            vec!["second-echo".to_string()]
        );
    }
    // The already-registered handler keeps its registration-time
    // integrations -- the registration shape a live session dispatches.
    let result = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "fixture-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert_eq!(
        result["command"], "python3",
        "the registered handler serves its registration-time integrations"
    );
    let missing = config(eukhe_core::kernel::shared::HostRequestPayload {
        data: serde_json::json!({ "server": "second-echo" }),
        cell_source_code: None,
    })
    .await
    .unwrap();
    assert!(
        missing.as_object().unwrap().is_empty(),
        "the pre-refresh handler does not know the new server"
    );
}

/// Local service-catalog sources (`mcpCatalogSources`) reach the print
/// manager's catalog resolution (TS `getCatalogSources`): the declared
/// file's entry surfaces as a local descriptor, and dropping the
/// declaration withdraws it on the next resolve -- the same live
/// settings read as the user-server closure.
#[test]
fn print_mode_mcp_manager_resolves_declared_catalog_sources() {
    let home = tempfile::TempDir::new().unwrap();
    let agent_dir = home.path().join("agent");
    std::fs::create_dir_all(&agent_dir).unwrap();
    let catalog = home.path().join("local-catalog.json");
    std::fs::write(
        &catalog,
        serde_json::json!({
            "version": 1,
            "entries": [{
                "server": "my-local", "service": "my-local", "label": "My Local",
                "url": "https://my-local.example/mcp", "aliases": [],
                "transport": { "type": "http", "url": "https://my-local.example/mcp" },
                "auth": { "strategy": "oauth", "clientRegistration": "dynamic" },
                "setup": { "status": "ready" },
                "verification": { "status": "unverified" },
                "legacyBuiltin": false,
                "provenance": [{ "source": "user" }]
            }]
        })
        .to_string(),
    )
    .unwrap();
    let settings = |sources: &[&str]| {
        serde_json::json!({
            "mcpCatalogSources": sources
                .iter()
                .map(std::string::ToString::to_string)
                .collect::<Vec<_>>()
        })
        .to_string()
    };
    std::fs::write(
        agent_dir.join("settings.json"),
        settings(&[&catalog.display().to_string()]),
    )
    .unwrap();
    let mut manager = crate::mcp_login::cli_mcp_manager(home.path(), &agent_dir);
    let my_local = manager
        .service_descriptors()
        .iter()
        .find(|service| service.service_id == "my-local")
        .expect("declared source entry resolved");
    assert!(my_local.local_source);
    // Live: dropping the declaration withdraws the entry on refresh.
    std::fs::write(agent_dir.join("settings.json"), settings(&[])).unwrap();
    manager.refresh();
    assert!(
        !manager
            .service_descriptors()
            .iter()
            .any(|service| service.service_id == "my-local"),
        "the dropped source no longer resolves"
    );
}
