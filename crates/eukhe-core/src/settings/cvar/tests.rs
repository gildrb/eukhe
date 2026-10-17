use eukhe_types::cvar::{parse_script, Aliases, Binds, ExpandError};
use serde_json::json;

use super::table::{DECLS, STEERING_MODE};
use super::*;

const FLAG: Decl = Decl {
    id: "flag",
    ty: CvarType::Bool,
    scope: CvarScope::Local,
    persist: true,
    replicate: false,
    init: Init::Bool(false),
};
const LIMIT: Decl = Decl {
    id: "limit",
    ty: CvarType::Nat,
    scope: CvarScope::Global,
    persist: false,
    replicate: true,
    init: Init::Nat(7),
};
const MODE: Decl = Decl {
    id: "nested.mode",
    ty: CvarType::Choice(&["a", "b"]),
    scope: CvarScope::Local,
    persist: false,
    replicate: true,
    init: Init::Text("a"),
};
static TEST_DECLS: &[Decl] = &[FLAG, LIMIT, MODE];
static TEST_REGISTRY: LazyLock<Registry> =
    LazyLock::new(|| Registry::new(TEST_DECLS).expect("the test table is a registry"));

fn set(id: &str, value: Value) -> Set {
    Set {
        id: id.to_string(),
        value,
    }
}

/// Run a cfg script into `target` and return the errors.
fn run(cvars: &mut Cvars, target: Target, script: &str) -> Vec<CvarError> {
    let (commands, parse_errors) = parse_script(script);
    assert_eq!(parse_errors, Vec::new());
    cvars.execute(
        target,
        &commands,
        &mut Aliases::default(),
        &mut Binds::default(),
    )
}

#[test]
fn the_table_is_a_registry() {
    assert!(Registry::new(DECLS).is_ok());
    assert_eq!(registry().find(STEERING_MODE.id), Some(&STEERING_MODE));
}

#[test]
fn a_second_declaration_or_a_default_of_the_wrong_type_is_rejected() {
    static DUPLICATE: &[Decl] = &[FLAG, LIMIT, FLAG];
    static WRONG_DEFAULT: &[Decl] = &[
        FLAG,
        Decl {
            init: Init::Text("c"),
            ..MODE
        },
    ];
    static WRONG_TYPE: &[Decl] = &[Decl {
        init: Init::Nat(1),
        ..FLAG
    }];
    assert_eq!(
        [
            Registry::new(DUPLICATE).err(),
            Registry::new(WRONG_DEFAULT).err(),
            Registry::new(WRONG_TYPE).err(),
        ],
        [
            Some(RegistryError::Duplicate { id: "flag" }),
            Some(RegistryError::BadDefault { id: "nested.mode" }),
            Some(RegistryError::BadDefault { id: "flag" }),
        ]
    );
}

const EFFECTS: Decl = Decl {
    id: "effects",
    ty: CvarType::ChoiceList(&["read", "write"]),
    scope: CvarScope::Local,
    persist: false,
    replicate: false,
    init: Init::List(&["read"]),
};

#[test]
fn a_choice_list_admits_only_its_options() {
    static BAD_ITEM: &[Decl] = &[Decl {
        init: Init::List(&["read", "fly"]),
        ..EFFECTS
    }];
    static GOOD: &[Decl] = &[EFFECTS];
    static REGISTRY: LazyLock<Registry> =
        LazyLock::new(|| Registry::new(GOOD).expect("a registry"));
    let cvars = Cvars::new(&REGISTRY, Sets::default());
    assert_eq!(
        (
            Registry::new(BAD_ITEM).err(),
            cvars.value(&EFFECTS),
            cvars.check(LayerKind::Agent, "effects", "read, write"),
            cvars.check(LayerKind::Agent, "effects", r#"["write"]"#),
            cvars.check(LayerKind::Agent, "effects", "read,fly"),
        ),
        (
            Some(RegistryError::BadDefault { id: "effects" }),
            json!(["read"]),
            Ok(set("effects", json!(["read", "write"]))),
            Ok(set("effects", json!(["write"]))),
            Err(CvarError::BadValue {
                id: "effects".to_string(),
                value: "read,fly".to_string(),
                expected: "a list of read, write".to_string(),
            }),
        )
    );
}

#[test]
fn layers_resolve_default_config_profile_and_sets_in_order() {
    let config = document_sets(
        &TEST_REGISTRY,
        &json!({"limit": 9, "nested": {"mode": "b"}, "flag": "not a bool"}),
        &json!({"limit": 3}),
    );
    assert_eq!(
        config,
        Sets(vec![set("limit", json!(3)), set("nested.mode", json!("b"))])
    );
    let mut root = Cvars::new(&TEST_REGISTRY, config);
    let errors = run(
        &mut root,
        Target::Sets,
        "set nested.mode a; set limit 1; set flag maybe; set nope 1",
    );
    assert_eq!(
        errors,
        vec![
            CvarError::Global {
                id: "limit".to_string()
            },
            CvarError::BadValue {
                id: "flag".to_string(),
                value: "maybe".to_string(),
                expected: "a bool".to_string()
            },
            CvarError::Undeclared {
                id: "nope".to_string()
            },
        ]
    );
    let mut child = root.child();
    let inherited = (child.value(&MODE), child.value(&LIMIT), child.value(&FLAG));
    run(
        &mut child,
        Target::Profile,
        "set flag true; set nested.mode b",
    );
    let profiled = (child.value(&MODE), child.value(&FLAG));
    run(&mut child, Target::Sets, "set nested.mode a");
    assert_eq!(
        (inherited, profiled, child.value(&MODE), root.value(&FLAG)),
        (
            (json!("a"), json!(3), json!(false)),
            (json!("b"), json!(true)),
            json!("a"),
            json!(false)
        )
    );
}

#[test]
fn a_toggle_twice_gives_back_the_value() {
    let mut cvars = Cvars::new(&TEST_REGISTRY, Sets::default());
    let before = cvars.value(&FLAG);
    let errors = [
        run(&mut cvars, Target::Sets, "toggle flag"),
        run(&mut cvars, Target::Sets, "toggle limit; toggle nested.mode"),
    ];
    let once = cvars.value(&FLAG);
    run(&mut cvars, Target::Sets, "toggle flag");
    assert_eq!(
        (before.clone(), once, cvars.value(&FLAG), errors),
        (
            json!(false),
            json!(true),
            before,
            [
                Vec::new(),
                vec![
                    CvarError::Global {
                        id: "limit".to_string()
                    },
                    CvarError::NotBool {
                        id: "nested.mode".to_string()
                    }
                ]
            ]
        )
    );
}

#[test]
fn the_written_cfg_read_back_as_a_profile_gives_the_same_persisting_values() {
    let mut agent = Cvars::new(&TEST_REGISTRY, Sets::default());
    run(&mut agent, Target::Sets, "set flag true; set nested.mode b");
    let written = agent.agent().sets.written(&TEST_REGISTRY, Flag::Persist);
    assert_eq!(written, Sets(vec![set("flag", json!(true))]));
    let mut reread = Cvars::new(&TEST_REGISTRY, Sets::default());
    run(&mut reread, Target::Profile, &written.render());
    assert_eq!(reread.value(&FLAG), agent.value(&FLAG));
}

#[test]
fn an_alias_runs_its_body_and_a_cycle_or_an_unknown_alias_runs_nothing() {
    let mut cvars = Cvars::new(&TEST_REGISTRY, Sets::default());
    let (commands, _) = parse_script(
        "alias on \"set flag true; set nested.mode b\"\n\
         alias loop \"loop\"\n\
         on\n\
         loop\n\
         gone",
    );
    let errors = cvars.execute(
        Target::Sets,
        &commands,
        &mut Aliases::default(),
        &mut Binds::default(),
    );
    assert_eq!(
        (errors, cvars.agent().sets.clone()),
        (
            vec![
                CvarError::Expand(ExpandError::Cycle {
                    alias: "loop".to_string()
                }),
                CvarError::Expand(ExpandError::Unknown {
                    alias: "gone".to_string()
                }),
            ],
            Sets(vec![
                set("flag", json!(true)),
                set("nested.mode", json!("b"))
            ])
        )
    );
}
