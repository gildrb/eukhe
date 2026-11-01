use serde_json::{json, Value};

use super::*;
use crate::settings::cvar::{registry, Set, Sets};

fn cvars(sets: &[(&str, Value)]) -> Cvars {
    Cvars::new(
        registry(),
        Sets(
            sets.iter()
                .map(|(id, value)| Set {
                    id: (*id).to_owned(),
                    value: value.clone(),
                })
                .collect(),
        ),
    )
}

fn row(role: ModelRole, source: RoleSource, selector: Option<&str>) -> RoleModel {
    RoleModel {
        role,
        source,
        selector: selector.map(str::to_owned),
    }
}

/// The table with only `modelRoles.all` set: every role but speech and
/// dictation runs on it; those two keep their defaults.
#[test]
fn the_all_roles_model_serves_every_role_without_its_own() {
    let all = Some("p/all");
    assert_eq!(
        role_table(&cvars(&[("modelRoles.all", json!(" p/all "))])),
        vec![
            row(ModelRole::Chat, RoleSource::All, all),
            row(ModelRole::Memory, RoleSource::All, all),
            row(ModelRole::Auxiliary, RoleSource::All, all),
            row(ModelRole::Image, RoleSource::All, all),
            row(ModelRole::Subagent, RoleSource::All, all),
            row(ModelRole::Gateway, RoleSource::All, all),
            row(ModelRole::Query, RoleSource::All, all),
            row(ModelRole::Titles, RoleSource::All, all),
            row(ModelRole::Judge, RoleSource::All, all),
            row(ModelRole::Translate, RoleSource::All, all),
            row(ModelRole::Speech, RoleSource::Default, None),
            row(ModelRole::Dictation, RoleSource::Default, None),
        ]
    );
}

/// Every role's own setting wins over `modelRoles.all`.
#[test]
fn every_own_setting_wins_over_the_all_roles_model() {
    let configured = cvars(&[
        ("modelRoles.all", json!("p/all")),
        ("defaultProvider", json!("p")),
        ("defaultModel", json!("chat")),
        ("memory.model", json!("p/memory")),
        ("auxiliaryModel", json!("p/aux")),
        ("imageModel", json!("p/image")),
        ("subagentDefaultModel", json!("p/sub")),
        ("gateway.signal.model", json!("p/gateway")),
        ("rlm.queryModel", json!("p/query")),
        ("modelRoles.tiny", json!("local/titles")),
        ("modelRoles.judge", json!("local/judge")),
        ("modelRoles.translate", json!("local/translate")),
        ("modelRoles.speech", json!("local/speech")),
        ("modelRoles.dictation", json!("local/dictation")),
    ]);
    assert_eq!(
        role_table(&configured),
        vec![
            row(ModelRole::Chat, RoleSource::Own, Some("p/chat")),
            row(ModelRole::Memory, RoleSource::Own, Some("p/memory")),
            row(ModelRole::Auxiliary, RoleSource::Own, Some("p/aux")),
            row(ModelRole::Image, RoleSource::Own, Some("p/image")),
            row(ModelRole::Subagent, RoleSource::Own, Some("p/sub")),
            row(ModelRole::Gateway, RoleSource::Own, Some("p/gateway")),
            row(ModelRole::Query, RoleSource::Own, Some("p/query")),
            row(ModelRole::Titles, RoleSource::Own, Some("local/titles")),
            row(ModelRole::Judge, RoleSource::Own, Some("local/judge")),
            row(
                ModelRole::Translate,
                RoleSource::Own,
                Some("local/translate")
            ),
            row(ModelRole::Speech, RoleSource::Own, Some("local/speech")),
            row(
                ModelRole::Dictation,
                RoleSource::Own,
                Some("local/dictation")
            ),
        ]
    );
}

/// The chat role owns its model only with both `defaultProvider` and
/// `defaultModel` set; the other roles take `modelRoles.all`. Nothing set:
/// every role defaults.
#[test]
fn chat_owns_its_model_with_provider_and_model_set() {
    let all = Some("p/all");
    let others = |chat: RoleModel| {
        let mut rows = vec![chat];
        rows.extend(
            [
                ModelRole::Memory,
                ModelRole::Auxiliary,
                ModelRole::Image,
                ModelRole::Subagent,
                ModelRole::Gateway,
                ModelRole::Query,
                ModelRole::Titles,
                ModelRole::Judge,
                ModelRole::Translate,
            ]
            .map(|role| row(role, RoleSource::All, all)),
        );
        rows.extend(
            [ModelRole::Speech, ModelRole::Dictation]
                .map(|role| row(role, RoleSource::Default, None)),
        );
        rows
    };
    assert_eq!(
        [
            role_table(&cvars(&[
                ("modelRoles.all", json!("p/all")),
                ("defaultProvider", json!("p")),
                ("defaultModel", json!("chat")),
            ])),
            role_table(&cvars(&[
                ("modelRoles.all", json!("p/all")),
                ("defaultProvider", json!("p")),
                ("defaultModel", json!("  ")),
            ])),
            role_table(&cvars(&[])),
        ],
        [
            others(row(ModelRole::Chat, RoleSource::Own, Some("p/chat"))),
            others(row(ModelRole::Chat, RoleSource::All, all)),
            ModelRole::ALL
                .map(|role| row(role, RoleSource::Default, None))
                .to_vec(),
        ]
    );
    assert_eq!(
        role_model(
            &cvars(&[("modelRoles.all", json!("p/all"))]),
            ModelRole::Speech
        ),
        row(ModelRole::Speech, RoleSource::Default, None)
    );
}
