//! Port of `test/service-wire.test.ts`.
//!
//! TS `toBe` identity checks on parsed values (`parse(x)` returns `x`) become
//! JSON equality: the Rust parsers build typed values from borrowed JSON.

use std::sync::Arc;

use serde_json::json as j;

use super::{json, Recorder};
use crate::context::{Context, BACKGROUND_CONTEXT};
use crate::error::BoxError;
use crate::json::JsonValue;
use crate::{
    create_remote_service_endpoint, create_service_catalogue_call, create_service_state_decoder,
    create_service_state_encoder, create_service_subscribe_call, create_service_unsubscribe_call,
    decode_service_control_call, define_service, parse_service_call, parse_service_catalogue,
    parse_service_provider_update, parse_service_subscription_snapshot,
    parse_wire_service_provider_update, parse_wire_service_subscription_snapshot, replicated_state,
    Outcome, RemoteServiceProvider, ServiceCatalogueEntry, ServiceControlCall, ServiceMode,
    ServiceObject, ServiceProviderDefinition, ServiceProviderUpdate, ServiceSubscriptionSnapshot,
    ServiceUpdatePublisher,
};

type Parse = fn(&JsonValue) -> Result<(), crate::ChordError>;

fn snapshot(value: &serde_json::Value) -> ServiceSubscriptionSnapshot {
    parse_service_subscription_snapshot(&json(value.clone())).unwrap()
}

fn update(value: &serde_json::Value) -> ServiceProviderUpdate {
    parse_service_provider_update(&json(value.clone())).unwrap()
}

#[test]
fn encodes_control_calls_and_validates_service_values() -> Result<(), BoxError> {
    assert_eq!(
        decode_service_control_call(&create_service_catalogue_call()),
        Some(ServiceControlCall::Catalogue)
    );
    assert_eq!(
        parse_service_catalogue(&json(j!([
            { "serviceId": "pi.models", "mode": "singleton" },
            { "serviceId": "pi.dialogs", "mode": "keyed" },
        ])))?,
        vec![
            ServiceCatalogueEntry {
                service_id: "pi.models".into(),
                mode: ServiceMode::Singleton
            },
            ServiceCatalogueEntry {
                service_id: "pi.dialogs".into(),
                mode: ServiceMode::Keyed
            },
        ]
    );
    let subscribe =
        create_service_subscribe_call("subscription-1", "pi.models", ServiceMode::Singleton);
    assert_eq!(
        decode_service_control_call(&subscribe),
        Some(ServiceControlCall::Subscribe {
            subscription_id: "subscription-1".into(),
            service_id: "pi.models".into(),
            mode: ServiceMode::Singleton,
        })
    );
    assert_eq!(
        decode_service_control_call(&create_service_unsubscribe_call("subscription-1")),
        Some(ServiceControlCall::Unsubscribe {
            subscription_id: "subscription-1".into()
        })
    );
    let call = parse_service_call(&json(j!({
        "serviceId": "pi.question-dialog",
        "instance": { "key": "invocation-1", "generation": 2 },
        "member": "submit",
        "args": [{ "outcome": "selected", "index": 0 }],
    })))?;
    assert_eq!(call.member, "submit");
    Ok(())
}

#[test]
fn rejects_malformed_service_values() {
    let error = parse_service_call(&json(
        j!({ "serviceId": "pi.models", "member": "list", "args": [], "extra": true }),
    ))
    .unwrap_err();
    assert!(
        error.to_string().contains("Invalid service call"),
        "{error}"
    );
    let error =
        parse_service_catalogue(&json(j!([{ "serviceId": "pi.models", "mode": "unknown" }])))
            .unwrap_err();
    assert!(
        error.to_string().contains("Invalid service catalogue"),
        "{error}"
    );
    let error = parse_service_provider_update(&json(
        j!({ "type": "state", "member": "state", "sequence": 0, "ops": [] }),
    ))
    .unwrap_err();
    assert!(
        error.to_string().contains("Invalid service state update"),
        "{error}"
    );
    assert!(parse_wire_service_provider_update(&json(
        j!({ "type": "state", "member": "state", "sequence": 1, "ops": [["?", 0]] })
    ))
    .is_err());
}

#[test]
fn validates_decoded_and_wire_snapshots_and_updates() -> Result<(), BoxError> {
    let snapshot_json = json(j!({
        "serviceId": "pi.models",
        "mode": "singleton",
        "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": 0, "ops": [["r", { "revision": 1 }]] }] }],
    }));
    let parsed = parse_service_subscription_snapshot(&snapshot_json)?;
    assert_eq!(parsed.to_json(), snapshot_json);
    let mut encoder = create_service_state_encoder();
    let wire_snapshot = encoder.encode_snapshot(&parsed)?;
    assert_eq!(
        parse_wire_service_subscription_snapshot(&wire_snapshot.to_json())?,
        wire_snapshot
    );
    let update_json = json(
        j!({ "type": "state", "member": "state", "sequence": 1, "ops": [["s", ["revision"], 2]] }),
    );
    let parsed_update = parse_service_provider_update(&update_json)?;
    assert_eq!(parsed_update.to_json(), update_json);
    let wire_update = encoder.encode_update(&parsed_update)?;
    assert_eq!(
        parse_wire_service_provider_update(&wire_update.to_json())?,
        wire_update
    );
    Ok(())
}

fn state_update(member: &str, sequence: u64, revision: i64) -> ServiceProviderUpdate {
    update(
        &j!({ "type": "state", "member": member, "sequence": sequence, "ops": [["s", ["revision"], revision]] }),
    )
}

#[test]
fn keeps_one_operation_codec_pair_for_one_subscription_state() -> Result<(), BoxError> {
    let mut enc = create_service_state_encoder();
    let mut dec = create_service_state_decoder();
    let snap = snapshot(&j!({
        "serviceId": "pi.models",
        "mode": "singleton",
        "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": 0, "ops": [["r", { "revision": 0 }]] }] }],
    }));
    assert_eq!(dec.decode_snapshot(&enc.encode_snapshot(&snap)?)?, snap);

    let first = state_update("state", 1, 1);
    let second = state_update("state", 2, 2);
    let first_wire = enc.encode_update(&first)?;
    let second_wire = enc.encode_update(&second)?;
    assert_eq!(
        first_wire.to_json()["ops"],
        json(j!([["s", ["revision"], 1]]))
    );
    assert_eq!(
        second_wire.to_json()["ops"],
        json(j!([["#", 0, ["revision"]], ["s", 0, 2]]))
    );
    assert_eq!(dec.decode_update(&first_wire)?, first);
    assert_eq!(dec.decode_update(&second_wire)?, second);
    Ok(())
}

#[test]
fn validates_explicit_resets_and_restarts_path_dictionaries_at_the_new_baseline(
) -> Result<(), BoxError> {
    let mut enc = create_service_state_encoder();
    let mut dec = create_service_state_decoder();
    let snap = snapshot(&j!({
        "serviceId": "pi.states",
        "mode": "singleton",
        "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": 0, "ops": [["r", { "before": 0 }]] }] }],
    }));
    dec.decode_snapshot(&enc.encode_snapshot(&snap)?)?;
    for sequence in 1..=2 {
        dec.decode_update(&enc.encode_update(&update(&j!({
            "type": "state", "member": "state", "sequence": sequence, "ops": [["s", ["before"], sequence]],
        })))?)?;
    }
    let reset_json = j!({
        "type": "reset",
        "snapshot": {
            "serviceId": "pi.states",
            "mode": "singleton",
            "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": 103, "ops": [["r", { "after": 103 }]] }] }],
        },
    });
    let reset = update(&reset_json);
    assert_eq!(reset.to_json(), json(reset_json.clone()));
    let wire_reset = enc.encode_update(&reset)?;
    assert_eq!(
        parse_wire_service_provider_update(&wire_reset.to_json())?,
        wire_reset
    );
    assert_eq!(dec.decode_update(&wire_reset)?, reset);
    for sequence in 104..=106 {
        let next = update(&j!({
            "type": "state", "member": "state", "sequence": sequence, "ops": [["s", ["after"], sequence]],
        }));
        assert_eq!(dec.decode_update(&enc.encode_update(&next)?)?, next);
    }
    let mut extra = reset_json;
    extra["extra"] = j!(true);
    let partial = j!({
        "type": "reset",
        "snapshot": {
            "serviceId": "pi.states",
            "mode": "singleton",
            "instances": [{ "members": [{ "name": "state", "kind": "state", "sequence": 103, "ops": [["s", ["before"], 103]] }] }],
        },
    });
    let parsers: [Parse; 2] = [
        |value| parse_service_provider_update(value).map(drop),
        |value| parse_wire_service_provider_update(value).map(drop),
    ];
    for parse in parsers {
        assert!(parse(&json(extra.clone())).is_err());
        assert!(parse(&json(j!({ "type": "reset", "snapshot": {} }))).is_err());
        let error = parse(&json(partial.clone())).unwrap_err();
        assert!(
            error.to_string().contains("full root replacements"),
            "{error}"
        );
    }
    Ok(())
}

#[test]
fn isolates_operation_dictionaries_between_states_and_subscriptions() -> Result<(), BoxError> {
    let snap = snapshot(&j!({
        "serviceId": "pi.states",
        "mode": "singleton",
        "instances": [{ "members": [
            { "name": "left", "kind": "state", "sequence": 0, "ops": [["r", { "revision": 0 }]] },
            { "name": "right", "kind": "state", "sequence": 0, "ops": [["r", { "revision": 0 }]] },
        ] }],
    }));
    let mut first_encoder = create_service_state_encoder();
    let mut first_decoder = create_service_state_decoder();
    let mut second_encoder = create_service_state_encoder();
    let mut second_decoder = create_service_state_decoder();
    first_decoder.decode_snapshot(&first_encoder.encode_snapshot(&snap)?)?;
    second_decoder.decode_snapshot(&second_encoder.encode_snapshot(&snap)?)?;

    let first_left = first_encoder.encode_update(&state_update("left", 1, 1))?;
    let first_right = first_encoder.encode_update(&state_update("right", 1, 1))?;
    let second_left = first_encoder.encode_update(&state_update("left", 2, 2))?;
    let second_right = first_encoder.encode_update(&state_update("right", 2, 2))?;
    let inline = json(j!([["s", ["revision"], 1]]));
    let defined = json(j!([["#", 0, ["revision"]], ["s", 0, 2]]));
    assert_eq!(first_left.to_json()["ops"], inline);
    assert_eq!(first_right.to_json()["ops"], inline);
    assert_eq!(second_left.to_json()["ops"], defined);
    assert_eq!(second_right.to_json()["ops"], defined);
    assert_eq!(
        first_decoder.decode_update(&first_left)?,
        state_update("left", 1, 1)
    );
    assert_eq!(
        first_decoder.decode_update(&first_right)?,
        state_update("right", 1, 1)
    );
    assert_eq!(
        first_decoder.decode_update(&second_left)?,
        state_update("left", 2, 2)
    );
    assert_eq!(
        first_decoder.decode_update(&second_right)?,
        state_update("right", 2, 2)
    );

    let independent_left = second_encoder.encode_update(&state_update("left", 1, 1))?;
    assert_eq!(independent_left.to_json()["ops"], inline);
    assert_eq!(
        second_decoder.decode_update(&independent_left)?,
        state_update("left", 1, 1)
    );

    let left_base = update(
        &j!({ "type": "state", "member": "left", "sequence": 3, "ops": [["r", { "revision": 3 }]] }),
    );
    assert_eq!(
        first_decoder.decode_update(&first_encoder.encode_update(&left_base)?)?,
        left_base
    );
    let third_right = first_encoder.encode_update(&state_update("right", 3, 3))?;
    assert_eq!(third_right.to_json()["ops"], json(j!([["s", 0, 3]])));
    assert_eq!(
        first_decoder.decode_update(&third_right)?,
        state_update("right", 3, 3)
    );
    Ok(())
}

#[test]
fn creates_and_removes_keyed_instance_codecs_with_their_lifecycle() -> Result<(), BoxError> {
    let mut enc = create_service_state_encoder();
    let mut dec = create_service_state_decoder();
    let snap = snapshot(&j!({ "serviceId": "pi.dialogs", "mode": "keyed", "instances": [] }));
    assert_eq!(dec.decode_snapshot(&enc.encode_snapshot(&snap)?)?, snap);
    let address = j!({ "key": "dialog-1", "generation": 1 });
    let spawned = update(&j!({
        "type": "spawned",
        "instance": {
            "instance": address,
            "members": [{ "name": "request", "kind": "state", "sequence": 0, "ops": [["r", { "value": 0 }]] }],
        },
    }));
    assert_eq!(dec.decode_update(&enc.encode_update(&spawned)?)?, spawned);
    let state = update(&j!({
        "type": "state", "instance": address, "member": "request", "sequence": 1, "ops": [["s", ["value"], 1]],
    }));
    assert_eq!(dec.decode_update(&enc.encode_update(&state)?)?, state);
    let closed = update(&j!({ "type": "closed", "instance": address }));
    assert_eq!(dec.decode_update(&enc.encode_update(&closed)?)?, closed);
    let late = update(&j!({
        "type": "state", "instance": address, "member": "request", "sequence": 2, "ops": [["s", ["value"], 1]],
    }));
    let error = enc.encode_update(&late).unwrap_err();
    assert!(
        error.to_string().contains("Unknown service state"),
        "{error}"
    );
    Ok(())
}

#[tokio::test]
async fn remote_service_endpoints_publish_and_clean_up_provider_subscriptions(
) -> Result<(), BoxError> {
    let counter = define_service::<()>("test.counter")?;
    let provider = RemoteServiceProvider::new([ServiceProviderDefinition::singleton(&counter)])?;
    let state = replicated_state(json(j!({ "value": 0 })))?;
    provider.provide(&counter, ServiceObject::new().state("state", &state))?;
    let endpoint = create_remote_service_endpoint(provider.clone());
    let updates: Recorder<ServiceProviderUpdate> = Recorder::default();
    let record = updates.clone();
    let publish: ServiceUpdatePublisher = Arc::new(
        move |_id: &str, update: ServiceProviderUpdate, _cx: &Context| {
            record.push(update);
            Outcome::Done
        },
    );
    let bg = BACKGROUND_CONTEXT.clone();

    let catalogue = endpoint
        .invoke(create_service_catalogue_call(), &publish, &bg)
        .await?;
    assert_eq!(
        catalogue,
        Some(json(
            j!([{ "serviceId": "test.counter", "mode": "singleton" }])
        ))
    );
    let subscribed = endpoint
        .invoke(
            create_service_subscribe_call("subscription-1", counter.id(), ServiceMode::Singleton),
            &publish,
            &bg,
        )
        .await?
        .unwrap();
    assert_eq!(subscribed["serviceId"], json(j!("test.counter")));
    assert_eq!(subscribed["mode"], json(j!("singleton")));

    state.change(&bg, |draft| draft.set("value", 1).map(drop))?;
    let recorded: Vec<JsonValue> = updates
        .get()
        .iter()
        .map(ServiceProviderUpdate::to_json)
        .collect();
    assert_eq!(
        recorded,
        vec![json(
            j!({ "type": "state", "member": "state", "sequence": 1, "ops": [["s", ["value"], 1]] })
        )]
    );
    endpoint.dispose();
    state.change(&bg, |draft| draft.set("value", 2).map(drop))?;
    assert_eq!(updates.len(), 1);
    provider.dispose()?;
    Ok(())
}
