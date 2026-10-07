//! Port of the definition cases of `test/session-definitions.test.ts`, plus
//! the address and materialization helpers of `documents.ts`. The TS
//! `@ts-expect-error` overload cases are `compile_fail` doctests in
//! `types::compile_checks`; the Session-level overloads (`tx.doc`,
//! `snapshot`, `documentState`, `watchDoc`) are tested with the Session.

use std::sync::Arc;

use eukhe_chord::delta::Op;
use eukhe_chord::json::{to_json, JsonObject, JsonValue};
use serde::{Deserialize, Serialize};

use super::*;
use crate::types::{DocumentRecord, Seq};

#[derive(Debug, Default, PartialEq, Serialize, Deserialize)]
struct State {
    value: i64,
}

fn initial() -> State {
    State { value: 0 }
}

fn seeded(value: i64) -> State {
    State { value }
}

const fn singleton(kind: &'static str) -> DocDefinition<State> {
    DocDefinition {
        kind,
        version: 1,
        initial,
        migrate: None,
        checkpoint_when: None,
    }
}

const fn family(kind: &'static str) -> DocFamilyDefinition<State, i64> {
    DocFamilyDefinition {
        kind,
        version: 1,
        initial: seeded,
        migrate: None,
        checkpoint_when: None,
    }
}

macro_rules! token {
    ($expr:expr) => {
        match $expr {
            Ok(token) => token,
            Err(_) => panic!("invalid test definition"),
        }
    };
}

static SESSION_DOC: SessionDoc<State> = token!(SessionDoc::define(singleton("t.session")));
static LATEST_DOC: ConversationDoc<State> = token!(ConversationDoc::define(
    singleton("t.latest"),
    LatestFork::Current
));
static REWINDABLE_DOC: RewindableConversationDoc<State> = token!(
    RewindableConversationDoc::define(singleton("t.rewindable"), RewindableFork::AsOf)
);
static TASK_DOC: TaskDoc<State> = token!(TaskDoc::define(singleton("t.task")));
static SESSION_FAMILY: SessionDocFamily<State, i64> =
    token!(SessionDocFamily::define(family("t.session-family")));
static CONVERSATION_FAMILY: RewindableConversationDocFamily<State, i64> =
    token!(RewindableConversationDocFamily::define(
        family("t.conversation-family"),
        RewindableFork::Initial
    ));
static TASK_FAMILY: TaskDocFamily<State, i64> =
    token!(TaskDocFamily::define(family("t.task-family")));

fn object(text: &str) -> Arc<JsonObject> {
    match JsonValue::parse(text).unwrap() {
        JsonValue::Object(object) => object,
        other => panic!("not an object: {other}"),
    }
}

fn record(id: u64, kind: &str, scope: DocumentRecordScope) -> DocumentRecord {
    DocumentRecord {
        id: DocumentId::from_number(id),
        kind: kind.to_owned(),
        key: None,
        scope,
        created_at: Seq::from_number(1),
        retired_at: None,
    }
}

#[test]
fn validates_persisted_version_semantics() {
    let error = SessionDoc::define(DocDefinition {
        version: 0,
        ..singleton("k")
    })
    .unwrap_err();
    assert_eq!(
        error.to_string(),
        "Document k version must be a positive integer"
    );
    let error = SessionDoc::define(DocDefinition {
        version: 1 << 53,
        ..singleton("k")
    })
    .unwrap_err();
    assert!(error.to_string().contains("positive integer"));
    // `version: 1.5` is not a `u64`; the TS runtime check has no Rust counterpart.
    assert_eq!(
        SessionDoc::define(singleton("")).unwrap().definition().kind,
        ""
    );
    assert_eq!(SESSION_DOC.definition().kind, "t.session");
    let error = TaskDocFamily::define(DocFamilyDefinition {
        version: 0,
        ..family("f")
    })
    .unwrap_err();
    assert_eq!(error, DefinitionError { kind: "f" });
}

#[test]
fn types_every_owner_key_and_seed_overload() {
    fn singleton_token<D: SingletonDocToken<Value = State>>(
        token: &D,
        locator: D::Locator<'_>,
    ) -> DocumentAddress {
        token.address(locator)
    }
    fn family_token<D: FamilyDocToken<Value = State, Seed = i64>>(
        token: &D,
        locator: D::Locator<'_>,
    ) -> DocumentAddress {
        assert_eq!(token.encode_seed(&1).unwrap(), Some(JsonValue::from(1)));
        token.address(locator)
    }
    let conversation_id = ConversationId::from_number(2);
    let task_id = TaskId::<u32>::from_number(3).erase();
    let address = |text: &str| -> DocumentAddress { serde_json::from_str(text).unwrap() };

    assert_eq!(
        singleton_token(&SESSION_DOC, ()),
        address(r#"{"kind":"t.session","scope":{"kind":"session"}}"#)
    );
    assert_eq!(
        singleton_token(&LATEST_DOC, conversation_id),
        address(r#"{"kind":"t.latest","scope":{"kind":"conversation","conversationId":2}}"#)
    );
    assert_eq!(
        singleton_token(&REWINDABLE_DOC, conversation_id),
        address(r#"{"kind":"t.rewindable","scope":{"kind":"conversation","conversationId":2}}"#)
    );
    assert_eq!(
        singleton_token(&TASK_DOC, task_id),
        address(r#"{"kind":"t.task","scope":{"kind":"task","taskId":3}}"#)
    );
    assert_eq!(
        family_token(&SESSION_FAMILY, "k"),
        address(r#"{"kind":"t.session-family","scope":{"kind":"session"},"key":"k"}"#)
    );
    assert_eq!(
        family_token(&CONVERSATION_FAMILY, (conversation_id, "k")),
        address(
            r#"{"kind":"t.conversation-family","scope":{"kind":"conversation","conversationId":2},"key":"k"}"#
        )
    );
    assert_eq!(
        family_token(&TASK_FAMILY, (task_id, "k")),
        address(r#"{"kind":"t.task-family","scope":{"kind":"task","taskId":3},"key":"k"}"#)
    );
    assert_eq!(SESSION_DOC.encode_seed(&()).unwrap(), None);
}

#[test]
fn types_historical_reads() {
    fn as_of<D: RewindableDocToken>(token: &D) -> DocumentSemantics {
        token.semantics()
    }
    assert_eq!(
        as_of(&REWINDABLE_DOC),
        DocumentSemantics::Conversation(ConversationSemantics::Rewindable(RewindableFork::AsOf))
    );
    assert_eq!(
        as_of(&CONVERSATION_FAMILY),
        DocumentSemantics::Conversation(ConversationSemantics::Rewindable(RewindableFork::Initial))
    );
    assert_eq!(
        LATEST_DOC.semantics(),
        DocumentSemantics::Conversation(ConversationSemantics::Latest(LatestFork::Current))
    );
    assert_eq!(SESSION_DOC.semantics(), DocumentSemantics::Session);
    assert_eq!(TASK_FAMILY.semantics(), DocumentSemantics::Task);
}

#[test]
fn erases_definitions_for_the_session() {
    let erased: Vec<Arc<dyn AnyDocDefinition>> =
        vec![Arc::new(SESSION_DOC), Arc::new(SESSION_FAMILY)];
    assert_eq!(erased[0].kind(), "t.session");
    assert!(!erased[0].is_family());
    assert!(erased[1].is_family());
    assert_eq!(
        *erased[0].initial(Some(&JsonValue::from(5))).unwrap(),
        *object(r#"{"value":0}"#)
    );
    assert_eq!(
        *erased[1].initial(Some(&JsonValue::from(5))).unwrap(),
        *object(r#"{"value":5}"#)
    );
    assert!(matches!(
        erased[1].initial(Some(&JsonValue::from("x"))),
        Err(DocumentError::Json(_))
    ));
    assert!(erased[0].migrate(&JsonObject::new(), 0).is_none());
    assert!(!erased[0].checkpoint_when(
        &JsonObject::new(),
        &[],
        CheckpointInfo {
            deltas_since_base: 9
        }
    ));

    let every_third: CheckpointWhenFn = |_, _, info| info.deltas_since_base % 3 == 2;
    let checkpointed = SessionDoc::define(DocDefinition {
        checkpoint_when: Some(every_third),
        ..singleton("c")
    })
    .unwrap();
    let ops = [Op::Replace(JsonValue::object())];
    assert!(checkpointed.checkpoint_when(
        &JsonObject::new(),
        &ops,
        CheckpointInfo {
            deltas_since_base: 2
        }
    ));
    assert!(!checkpointed.checkpoint_when(
        &JsonObject::new(),
        &ops,
        CheckpointInfo {
            deltas_since_base: 3
        }
    ));

    let not_object = SessionDoc::<i64>::define(DocDefinition {
        kind: "n",
        version: 1,
        initial: || 1,
        migrate: None,
        checkpoint_when: None,
    })
    .unwrap();
    assert_eq!(
        not_object.initial(None).unwrap_err().to_string(),
        "Document n value is not a JSON object"
    );
}

#[test]
fn identifies_addresses_like_json_stringify() {
    // Expected strings are `JSON.stringify([kind, scope.kind, owner, key ?? null])` from node.
    let resolved = resolve_token_address(&SESSION_DOC, ());
    assert_eq!(resolved.id, r#"["t.session","session",null,null]"#);
    let address = DocumentAddress {
        kind: "t.family".to_owned(),
        scope: DocumentScope::Conversation {
            conversation_id: ConversationId::from_number(2),
        },
        key: Some("k\"ey".to_owned()),
    };
    assert_eq!(
        address_id(&address),
        r#"["t.family","conversation",2,"k\"ey"]"#
    );
    let address = DocumentAddress {
        kind: "t.task".to_owned(),
        scope: DocumentScope::Task {
            task_id: TaskId::from_number(16),
        },
        key: Some("é😀\u{2028}".to_owned()),
    };
    assert_eq!(
        address_id(&address),
        "[\"t.task\",\"task\",16,\"é😀\u{2028}\"]"
    );
    let address = DocumentAddress {
        kind: "x".to_owned(),
        scope: DocumentScope::Conversation {
            conversation_id: ConversationId::from_number(9_007_199_254_740_991),
        },
        key: None,
    };
    assert_eq!(
        address_id(&address),
        r#"["x","conversation",9007199254740991,null]"#
    );
}

#[test]
fn resolves_erased_arguments() {
    let resolved = resolve_address(&CONVERSATION_FAMILY, Some(2), Some("k")).unwrap();
    assert_eq!(
        resolved,
        resolve_token_address(&CONVERSATION_FAMILY, (ConversationId::from_number(2), "k"))
    );
    // Singletons ignore the key; Session documents take no owner.
    assert_eq!(
        resolve_address(&LATEST_DOC, Some(2), Some("k"))
            .unwrap()
            .address
            .key,
        None
    );
    assert_eq!(
        resolve_address(&SESSION_FAMILY, None, Some("k"))
            .unwrap()
            .id,
        r#"["t.session-family","session",null,"k"]"#
    );
    assert_eq!(
        resolve_address(&LATEST_DOC, None, None)
            .unwrap_err()
            .to_string(),
        "Document t.latest requires a conversation ID"
    );
    assert_eq!(
        resolve_address(&TASK_DOC, Some(1 << 53), None)
            .unwrap_err()
            .to_string(),
        "Document t.task requires a task ID"
    );
}

#[test]
fn builds_create_records_and_checks_persisted_semantics() {
    let id = DocumentId::from_number(6);
    let conversation_id = ConversationId::from_number(2);
    let address = resolve_token_address(&REWINDABLE_DOC, conversation_id).address;
    let create = document_create(&REWINDABLE_DOC, &address, id).unwrap();
    assert_eq!(
        to_json(&create).unwrap().to_string(),
        r#"{"id":6,"kind":"t.rewindable","scope":{"kind":"conversation","conversationId":2},"history":"rewindable","fork":"asOf"}"#
    );
    let address = resolve_token_address(&SESSION_FAMILY, "k").address;
    assert_eq!(
        to_json(&document_create(&SESSION_FAMILY, &address, id).unwrap())
            .unwrap()
            .to_string(),
        r#"{"id":6,"kind":"t.session-family","key":"k","scope":{"kind":"session"}}"#
    );
    let conversation_address = resolve_token_address(&LATEST_DOC, conversation_id).address;
    assert!(matches!(
        document_create(&SESSION_DOC, &conversation_address, id),
        Err(DocumentError::SemanticsMismatch { .. })
    ));

    check_record_scope(&REWINDABLE_DOC, &create).unwrap();
    let latest = record(
        7,
        "t.rewindable",
        DocumentRecordScope::Conversation {
            conversation_id,
            semantics: ConversationSemantics::Rewindable(RewindableFork::Current),
        },
    );
    assert_eq!(
        check_record_scope(&REWINDABLE_DOC, &latest)
            .unwrap_err()
            .to_string(),
        "Document 7 (t.rewindable) does not match the supplied definition semantics"
    );
    assert!(check_record_scope(
        &TASK_DOC,
        &record(8, "t.task", DocumentRecordScope::Session)
    )
    .is_err());
}

fn migrate_v1(value: &JsonObject, from_version: u64) -> Result<State, CallbackError> {
    match value.get("count").and_then(JsonValue::as_i64) {
        Some(count) => Ok(State {
            value: count * 10 + i64::try_from(from_version)?,
        }),
        None => Err("missing count".into()),
    }
}

#[test]
fn checks_versions_and_materializes_with_migrate() {
    let stored_record = record(9, "t.session", DocumentRecordScope::Session);
    let value = object(r#"{"count":4}"#);
    assert_eq!(
        check_record_version(&SESSION_DOC, &stored_record, 2)
            .unwrap_err()
            .to_string(),
        "Document 9 (t.session) has newer version 2 than 1"
    );
    let v2 = SessionDoc::define(DocDefinition {
        version: 2,
        ..singleton("t.session")
    })
    .unwrap();
    assert_eq!(
        check_record_version(&v2, &stored_record, 1)
            .unwrap_err()
            .to_string(),
        "Document 9 (t.session) requires migration from version 1"
    );
    // The current version is returned as the same shared value.
    let same = materialize_document_value(&SESSION_DOC, &stored_record, 1, &value).unwrap();
    assert!(Arc::ptr_eq(&same, &value));

    let migrating = SessionDoc::define(DocDefinition {
        version: 2,
        migrate: Some(migrate_v1),
        ..singleton("t.session")
    })
    .unwrap();
    let stored = StoredDocument {
        record: stored_record,
        version: 1,
        value: Arc::clone(&value),
        deltas_since_base: 0,
    };
    assert_eq!(
        *materialize_document(&migrating, &stored).unwrap(),
        *object(r#"{"value":41}"#)
    );
    let broken = StoredDocument {
        value: object("{}"),
        ..stored
    };
    assert_eq!(
        materialize_document(&migrating, &broken)
            .unwrap_err()
            .to_string(),
        "missing count"
    );
    let task_record = record(
        10,
        "t.session",
        DocumentRecordScope::Task {
            task_id: TaskId::from_number(1),
        },
    );
    assert!(matches!(
        materialize_document_value(&migrating, &task_record, 1, &value),
        Err(DocumentError::SemanticsMismatch { .. })
    ));
}
