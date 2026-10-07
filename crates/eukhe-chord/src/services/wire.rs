//! The transport-independent service wire grammar: `$chord.service` control
//! calls, JSON forms of service values, and their validating parsers (port
//! of `services/wire.ts`).
//!
//! TS parsers take `unknown` and return the same object typed. Rust parsers
//! take a [`JsonValue`] and build the typed value; `to_json` methods produce
//! the JSON the TS code builds, in the same key order.

use std::collections::HashSet;
use std::sync::Arc;

use crate::delta::{DeltaError, Op, WireOp};
use crate::error::ChordError;
use crate::json::{JsonObject, JsonValue, NULL};
use crate::types::{
    ServiceCall, ServiceCatalogueEntry, ServiceInstanceAddress, ServiceInstanceSnapshot,
    ServiceMemberSnapshot, ServiceMode, ServiceProviderUpdate, ServiceSubscriptionSnapshot,
};

/// A decoded member snapshot on the wire (`WireServiceMemberSnapshot`).
pub type WireServiceMemberSnapshot = ServiceMemberSnapshot<WireOp>;
/// A wire instance snapshot (`WireServiceInstanceSnapshot`).
pub type WireServiceInstanceSnapshot = ServiceInstanceSnapshot<WireOp>;
/// A wire subscription snapshot (`WireServiceSubscriptionSnapshot`).
pub type WireServiceSubscriptionSnapshot = ServiceSubscriptionSnapshot<WireOp>;
/// A wire provider update (`WireServiceProviderUpdate`).
pub type WireServiceProviderUpdate = ServiceProviderUpdate<WireOp>;

const SERVICE_CONTROL_ID: &str = "$chord.service";
const SERVICE_CATALOGUE_MEMBER: &str = "catalogue";
const SERVICE_SUBSCRIBE_MEMBER: &str = "subscribe";
const SERVICE_UNSUBSCRIBE_MEMBER: &str = "unsubscribe";

mod sealed {
    pub trait Sealed {}
    impl Sealed for crate::delta::Op {}
    impl Sealed for crate::delta::WireOp {}
}

/// The operation types a service value can carry: [`Op`] and [`WireOp`].
pub trait ServiceOp: Clone + sealed::Sealed + Send + Sync + 'static {
    /// The op's JSON tuple.
    fn op_json(&self) -> JsonValue;
    /// Validate and build an op from its JSON tuple.
    ///
    /// # Errors
    ///
    /// The TS `assertValidOp` / `assertValidWireOp` failure.
    fn parse_op(value: &JsonValue) -> Result<Self, DeltaError>;
    /// Whether the op is a root replacement (`["r", value]`).
    fn is_root_replace(&self) -> bool;
}

impl ServiceOp for Op {
    fn op_json(&self) -> JsonValue {
        self.to_json()
    }

    fn parse_op(value: &JsonValue) -> Result<Self, DeltaError> {
        Op::from_json(value)
    }

    fn is_root_replace(&self) -> bool {
        self.is_replace()
    }
}

impl ServiceOp for WireOp {
    fn op_json(&self) -> JsonValue {
        self.to_json()
    }

    fn parse_op(value: &JsonValue) -> Result<Self, DeltaError> {
        WireOp::from_json(value)
    }

    fn is_root_replace(&self) -> bool {
        self.is_replace()
    }
}

/// A decoded `$chord.service` control call.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ServiceControlCall {
    /// `{ type: "catalogue" }`.
    Catalogue,
    /// `{ type: "subscribe", subscriptionId, serviceId, mode }`.
    Subscribe {
        /// The consumer-chosen subscription ID.
        subscription_id: String,
        /// The service ID.
        service_id: String,
        /// The mode the consumer expects.
        mode: ServiceMode,
    },
    /// `{ type: "unsubscribe", subscriptionId }`.
    Unsubscribe {
        /// The subscription ID.
        subscription_id: String,
    },
}

/// The control call returning the provider catalogue.
#[must_use]
pub fn create_service_catalogue_call() -> ServiceCall {
    control_call(SERVICE_CATALOGUE_MEMBER, Vec::new())
}

/// The control call opening one subscription.
#[must_use]
pub fn create_service_subscribe_call(
    subscription_id: &str,
    service_id: &str,
    mode: ServiceMode,
) -> ServiceCall {
    control_call(
        SERVICE_SUBSCRIBE_MEMBER,
        vec![
            JsonValue::from(subscription_id),
            JsonValue::from(service_id),
            JsonValue::from(mode.as_str()),
        ],
    )
}

/// The control call closing one subscription.
#[must_use]
pub fn create_service_unsubscribe_call(subscription_id: &str) -> ServiceCall {
    control_call(
        SERVICE_UNSUBSCRIBE_MEMBER,
        vec![JsonValue::from(subscription_id)],
    )
}

fn control_call(member: &str, args: Vec<JsonValue>) -> ServiceCall {
    ServiceCall {
        service_id: SERVICE_CONTROL_ID.to_owned(),
        instance: None,
        member: member.to_owned(),
        args,
    }
}

/// Recognize a `$chord.service` control call; `None` for a service call.
#[must_use]
pub fn decode_service_control_call(call: &ServiceCall) -> Option<ServiceControlCall> {
    if call.service_id != SERVICE_CONTROL_ID || call.instance.is_some() {
        return None;
    }
    let args = &call.args;
    if call.member == SERVICE_CATALOGUE_MEMBER && args.is_empty() {
        return Some(ServiceControlCall::Catalogue);
    }
    if call.member == SERVICE_SUBSCRIBE_MEMBER && args.len() == 3 {
        if let (Some(subscription_id), Some(service_id), Some(mode)) = (
            id(&args[0]),
            id(&args[1]),
            args[2].as_str().and_then(ServiceMode::parse),
        ) {
            return Some(ServiceControlCall::Subscribe {
                subscription_id: subscription_id.to_owned(),
                service_id: service_id.to_owned(),
                mode,
            });
        }
    }
    if call.member == SERVICE_UNSUBSCRIBE_MEMBER && args.len() == 1 {
        if let Some(subscription_id) = id(&args[0]) {
            return Some(ServiceControlCall::Unsubscribe {
                subscription_id: subscription_id.to_owned(),
            });
        }
    }
    None
}

/// Validate a service call.
///
/// # Errors
///
/// `TypeError("Invalid service call")` and the address errors.
pub fn parse_service_call(value: &JsonValue) -> Result<ServiceCall, ChordError> {
    let call = record(value, "service call")?;
    assert_keys(
        call,
        &["serviceId", "member", "args"],
        &["instance"],
        "service call",
    )?;
    let (Some(service_id), Some(member), Some(args)) = (
        call.get("serviceId").and_then(id),
        call.get("member").and_then(id),
        call.get("args").and_then(JsonValue::as_array),
    ) else {
        return Err(ChordError::type_error("Invalid service call"));
    };
    let instance = call.get("instance").map(parse_address).transpose()?;
    Ok(ServiceCall {
        service_id: service_id.to_owned(),
        instance,
        member: member.to_owned(),
        args: args.to_vec(),
    })
}

/// Validate a provider catalogue.
///
/// # Errors
///
/// `TypeError("Invalid service catalogue")` for a malformed or duplicate
/// entry.
pub fn parse_service_catalogue(
    value: &JsonValue,
) -> Result<Vec<ServiceCatalogueEntry>, ChordError> {
    let Some(candidates) = value.as_array() else {
        return Err(ChordError::type_error("Invalid service catalogue"));
    };
    let mut ids = HashSet::new();
    let mut entries = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let entry = record(candidate, "service catalogue entry")?;
        assert_keys(
            entry,
            &["serviceId", "mode"],
            &[],
            "service catalogue entry",
        )?;
        let (Some(service_id), Some(mode)) = (
            entry.get("serviceId").and_then(id),
            entry.get("mode").and_then(mode),
        ) else {
            return Err(ChordError::type_error("Invalid service catalogue"));
        };
        if !ids.insert(service_id) {
            return Err(ChordError::type_error("Invalid service catalogue"));
        }
        entries.push(ServiceCatalogueEntry {
            service_id: service_id.to_owned(),
            mode,
        });
    }
    Ok(entries)
}

/// Validate a decoded subscription snapshot.
///
/// # Errors
///
/// A malformed snapshot or op.
pub fn parse_service_subscription_snapshot(
    value: &JsonValue,
) -> Result<ServiceSubscriptionSnapshot, ChordError> {
    parse_subscription_snapshot(value)
}

/// Validate a wire subscription snapshot.
///
/// # Errors
///
/// A malformed snapshot or wire op.
pub fn parse_wire_service_subscription_snapshot(
    value: &JsonValue,
) -> Result<WireServiceSubscriptionSnapshot, ChordError> {
    parse_subscription_snapshot(value)
}

/// Validate a decoded provider update.
///
/// # Errors
///
/// A malformed update or op.
pub fn parse_service_provider_update(
    value: &JsonValue,
) -> Result<ServiceProviderUpdate, ChordError> {
    parse_provider_update(value)
}

/// Validate a wire provider update.
///
/// # Errors
///
/// A malformed update or wire op.
pub fn parse_wire_service_provider_update(
    value: &JsonValue,
) -> Result<WireServiceProviderUpdate, ChordError> {
    parse_provider_update(value)
}

fn parse_subscription_snapshot<O: ServiceOp>(
    value: &JsonValue,
) -> Result<ServiceSubscriptionSnapshot<O>, ChordError> {
    let snapshot = record(value, "service subscription snapshot")?;
    assert_keys(
        snapshot,
        &["serviceId", "mode", "instances"],
        &[],
        "service subscription snapshot",
    )?;
    let (Some(service_id), Some(mode), Some(instances)) = (
        snapshot.get("serviceId").and_then(id),
        snapshot.get("mode").and_then(mode),
        snapshot.get("instances").and_then(JsonValue::as_array),
    ) else {
        return Err(ChordError::type_error(
            "Invalid service subscription snapshot",
        ));
    };
    Ok(ServiceSubscriptionSnapshot {
        service_id: service_id.to_owned(),
        mode,
        instances: instances
            .iter()
            .map(parse_instance)
            .collect::<Result<_, _>>()?,
    })
}

fn parse_provider_update<O: ServiceOp>(
    value: &JsonValue,
) -> Result<ServiceProviderUpdate<O>, ChordError> {
    let update = record(value, "service provider update")?;
    match update.get("type").and_then(JsonValue::as_str) {
        Some("state") => {
            assert_keys(
                update,
                &["type", "member", "sequence", "ops"],
                &["instance"],
                "state update",
            )?;
            let (Some(member), Some(sequence), Some(ops)) = (
                update.get("member").and_then(id),
                update
                    .get("sequence")
                    .and_then(|sequence| integer(sequence, 1)),
                update.get("ops").and_then(JsonValue::as_array),
            ) else {
                return Err(ChordError::type_error("Invalid service state update"));
            };
            let instance = update.get("instance").map(parse_address).transpose()?;
            Ok(ServiceProviderUpdate::State {
                instance,
                member: member.to_owned(),
                sequence,
                ops: parse_ops(ops)?,
            })
        }
        Some("reset") => {
            assert_keys(update, &["type", "snapshot"], &[], "reset update")?;
            let snapshot: ServiceSubscriptionSnapshot<O> =
                parse_subscription_snapshot(field(update, "snapshot"))?;
            for instance in &snapshot.instances {
                for member in &instance.members {
                    if let ServiceMemberSnapshot::State { ops, .. } = member {
                        if ops.len() != 1 || !ops[0].is_root_replace() {
                            return Err(ChordError::type_error(
                                "Service reset must contain full root replacements",
                            ));
                        }
                    }
                }
            }
            Ok(ServiceProviderUpdate::Reset { snapshot })
        }
        Some("unavailable") => {
            assert_keys(update, &["type"], &[], "unavailable update")?;
            Ok(ServiceProviderUpdate::Unavailable)
        }
        Some("replaced") => {
            assert_keys(update, &["type", "snapshot"], &[], "replacement update")?;
            Ok(ServiceProviderUpdate::Replaced {
                snapshot: parse_instance(field(update, "snapshot"))?,
            })
        }
        Some("spawned") => {
            assert_keys(update, &["type", "instance"], &[], "spawn update")?;
            Ok(ServiceProviderUpdate::Spawned {
                instance: parse_instance(field(update, "instance"))?,
            })
        }
        Some("closed") => {
            assert_keys(update, &["type", "instance"], &[], "close update")?;
            Ok(ServiceProviderUpdate::Closed {
                instance: parse_address(field(update, "instance"))?,
            })
        }
        _ => Err(ChordError::type_error("Invalid service provider update")),
    }
}

/// A property asserted present (`update.snapshot`).
fn field<'a>(value: &'a JsonObject, key: &str) -> &'a JsonValue {
    value.get(key).unwrap_or(&NULL)
}

fn parse_instance<O: ServiceOp>(
    value: &JsonValue,
) -> Result<ServiceInstanceSnapshot<O>, ChordError> {
    let instance = record(value, "service instance snapshot")?;
    assert_keys(
        instance,
        &["members"],
        &["instance"],
        "service instance snapshot",
    )?;
    let address = instance.get("instance").map(parse_address).transpose()?;
    let Some(candidates) = instance.get("members").and_then(JsonValue::as_array) else {
        return Err(ChordError::type_error("Invalid service instance snapshot"));
    };
    let mut members = Vec::with_capacity(candidates.len());
    for candidate in candidates {
        let member = record(candidate, "service member snapshot")?;
        match member.get("kind").and_then(JsonValue::as_str) {
            Some("method") => {
                assert_keys(member, &["name", "kind"], &[], "service method snapshot")?;
                let Some(name) = member.get("name").and_then(id) else {
                    return Err(ChordError::type_error("Invalid service method snapshot"));
                };
                members.push(ServiceMemberSnapshot::Method {
                    name: name.to_owned(),
                });
            }
            Some("state") => {
                assert_keys(
                    member,
                    &["name", "kind", "sequence", "ops"],
                    &[],
                    "service state snapshot",
                )?;
                let (Some(name), Some(sequence), Some(ops)) = (
                    member.get("name").and_then(id),
                    member
                        .get("sequence")
                        .and_then(|sequence| integer(sequence, 0)),
                    member.get("ops").and_then(JsonValue::as_array),
                ) else {
                    return Err(ChordError::type_error("Invalid service state snapshot"));
                };
                members.push(ServiceMemberSnapshot::State {
                    name: name.to_owned(),
                    sequence,
                    ops: parse_ops(ops)?,
                });
            }
            _ => return Err(ChordError::type_error("Invalid service member snapshot")),
        }
    }
    Ok(ServiceInstanceSnapshot {
        instance: address,
        members,
    })
}

fn parse_ops<O: ServiceOp>(ops: &[JsonValue]) -> Result<Arc<[O]>, ChordError> {
    ops.iter()
        .map(|op| O::parse_op(op).map_err(ChordError::from))
        .collect()
}

fn parse_address(value: &JsonValue) -> Result<ServiceInstanceAddress, ChordError> {
    let address = record(value, "service instance address")?;
    assert_keys(
        address,
        &["key", "generation"],
        &[],
        "service instance address",
    )?;
    let (Some(key), Some(generation)) = (
        address.get("key").and_then(id),
        address
            .get("generation")
            .and_then(|generation| integer(generation, 1)),
    ) else {
        return Err(ChordError::type_error("Invalid service instance address"));
    };
    Ok(ServiceInstanceAddress {
        key: key.to_owned(),
        generation,
    })
}

fn record<'a>(value: &'a JsonValue, description: &str) -> Result<&'a JsonObject, ChordError> {
    value
        .as_object()
        .ok_or_else(|| ChordError::type_error(format!("Invalid {description}")))
}

fn assert_keys(
    value: &JsonObject,
    required: &[&str],
    optional: &[&str],
    description: &str,
) -> Result<(), ChordError> {
    let missing = required.iter().any(|key| !value.contains_key(key));
    let extra = value
        .keys()
        .any(|key| !required.contains(&key) && !optional.contains(&key));
    if missing || extra {
        return Err(ChordError::type_error(format!("Invalid {description}")));
    }
    Ok(())
}

fn id(value: &JsonValue) -> Option<&str> {
    value.as_str().filter(|value| !value.is_empty())
}

fn mode(value: &JsonValue) -> Option<ServiceMode> {
    value.as_str().and_then(ServiceMode::parse)
}

/// TS `Number.isInteger(value) && value >= minimum`. Integers beyond
/// `u64` (which JS would accept but cannot represent exactly) are rejected.
fn integer(value: &JsonValue, minimum: u64) -> Option<u64> {
    value.as_u64().filter(|value| *value >= minimum)
}

/// A non-negative integer as a JSON number.
pub(crate) fn integer_json(value: u64) -> JsonValue {
    JsonValue::try_from(value).unwrap_or_else(|_| {
        // JS numbers past 2^53 are already approximate; print the double.
        #[allow(
            clippy::cast_precision_loss,
            reason = "JS numbers beyond 2^53 are approximate too"
        )]
        let approximate = value as f64;
        JsonValue::try_from(approximate).unwrap_or(JsonValue::Null)
    })
}

impl ServiceCatalogueEntry {
    /// `{ serviceId, mode }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(2);
        object.insert("serviceId", JsonValue::from(self.service_id.as_str()));
        object.insert("mode", JsonValue::from(self.mode.as_str()));
        object.into()
    }
}

/// A catalogue as its JSON array.
#[must_use]
pub fn catalogue_json(catalogue: &[ServiceCatalogueEntry]) -> JsonValue {
    catalogue
        .iter()
        .map(ServiceCatalogueEntry::to_json)
        .collect()
}

impl ServiceInstanceAddress {
    /// `{ key, generation }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(2);
        object.insert("key", JsonValue::from(self.key.as_str()));
        object.insert("generation", integer_json(self.generation));
        object.into()
    }
}

impl<O: ServiceOp> ServiceMemberSnapshot<O> {
    /// `{ name, kind: "method" }` or `{ name, kind: "state", sequence, ops }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(4);
        match self {
            Self::Method { name } => {
                object.insert("name", JsonValue::from(name.as_str()));
                object.insert("kind", JsonValue::from("method"));
            }
            Self::State {
                name,
                sequence,
                ops,
            } => {
                object.insert("name", JsonValue::from(name.as_str()));
                object.insert("kind", JsonValue::from("state"));
                object.insert("sequence", integer_json(*sequence));
                object.insert("ops", ops_json(ops));
            }
        }
        object.into()
    }
}

impl<O: ServiceOp> ServiceInstanceSnapshot<O> {
    /// `{ instance?, members }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(2);
        if let Some(instance) = &self.instance {
            object.insert("instance", instance.to_json());
        }
        object.insert(
            "members",
            self.members
                .iter()
                .map(ServiceMemberSnapshot::to_json)
                .collect(),
        );
        object.into()
    }
}

impl<O: ServiceOp> ServiceSubscriptionSnapshot<O> {
    /// `{ serviceId, mode, instances }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(3);
        object.insert("serviceId", JsonValue::from(self.service_id.as_str()));
        object.insert("mode", JsonValue::from(self.mode.as_str()));
        object.insert(
            "instances",
            self.instances
                .iter()
                .map(ServiceInstanceSnapshot::to_json)
                .collect(),
        );
        object.into()
    }
}

impl<O: ServiceOp> ServiceProviderUpdate<O> {
    /// The update object, `type` first.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(5);
        object.insert("type", JsonValue::from(self.kind()));
        match self {
            Self::State {
                instance,
                member,
                sequence,
                ops,
            } => {
                if let Some(instance) = instance {
                    object.insert("instance", instance.to_json());
                }
                object.insert("member", JsonValue::from(member.as_str()));
                object.insert("sequence", integer_json(*sequence));
                object.insert("ops", ops_json(ops));
            }
            Self::Reset { snapshot } => {
                object.insert("snapshot", snapshot.to_json());
            }
            Self::Unavailable => {}
            Self::Replaced { snapshot } => {
                object.insert("snapshot", snapshot.to_json());
            }
            Self::Spawned { instance } => {
                object.insert("instance", instance.to_json());
            }
            Self::Closed { instance } => {
                object.insert("instance", instance.to_json());
            }
        }
        object.into()
    }
}

impl ServiceCall {
    /// `{ serviceId, instance?, member, args }`.
    #[must_use]
    pub fn to_json(&self) -> JsonValue {
        let mut object = JsonObject::with_capacity(4);
        object.insert("serviceId", JsonValue::from(self.service_id.as_str()));
        if let Some(instance) = &self.instance {
            object.insert("instance", instance.to_json());
        }
        object.insert("member", JsonValue::from(self.member.as_str()));
        object.insert("args", JsonValue::from(self.args.clone()));
        object.into()
    }
}

fn ops_json<O: ServiceOp>(ops: &[O]) -> JsonValue {
    ops.iter().map(ServiceOp::op_json).collect()
}
