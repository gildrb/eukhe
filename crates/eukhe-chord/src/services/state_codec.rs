//! Per-subscription operation encoders and decoders for every replicated
//! state in one service subscription (port of `services/state-codec.ts`).
//!
//! Each state member of each instance has its own path dictionary. Snapshots,
//! resets, singleton replacements, and unavailability restart every
//! dictionary; a closed instance drops its own.

use std::collections::HashMap;
use std::sync::Arc;

use crate::delta::{decoder, encoder, Decoder, Encoder, Op, WireOp};
use crate::error::ChordError;
use crate::types::{
    ServiceInstanceAddress, ServiceInstanceSnapshot, ServiceMemberSnapshot, ServiceProviderUpdate,
    ServiceSubscriptionSnapshot,
};

use super::wire::{
    WireServiceInstanceSnapshot, WireServiceProviderUpdate, WireServiceSubscriptionSnapshot,
};

/// TS `stateKey`: `[instance?.key ?? null, instance?.generation ?? null, member]`.
type StateKey = (Option<String>, Option<u64>, String);

struct CodecEntry<C> {
    instance: Option<ServiceInstanceAddress>,
    codec: C,
}

struct StateCodecRegistry<C> {
    create: fn() -> C,
    entries: HashMap<StateKey, CodecEntry<C>>,
}

impl<C> StateCodecRegistry<C> {
    fn new(create: fn() -> C) -> Self {
        Self {
            create,
            entries: HashMap::new(),
        }
    }

    fn reset(&mut self) {
        self.entries.clear();
    }

    fn add(
        &mut self,
        instance: Option<&ServiceInstanceAddress>,
        member: &str,
    ) -> Result<&mut C, ChordError> {
        let key = state_key(instance, member);
        if self.entries.contains_key(&key) {
            return Err(ChordError::error(format!(
                "Duplicate service state {}",
                describe_state(instance, member)
            )));
        }
        let entry = self.entries.entry(key).or_insert(CodecEntry {
            instance: instance.cloned(),
            codec: (self.create)(),
        });
        Ok(&mut entry.codec)
    }

    fn get(
        &mut self,
        instance: Option<&ServiceInstanceAddress>,
        member: &str,
    ) -> Result<&mut C, ChordError> {
        match self.entries.get_mut(&state_key(instance, member)) {
            Some(entry) => Ok(&mut entry.codec),
            None => Err(ChordError::error(format!(
                "Unknown service state {}",
                describe_state(instance, member)
            ))),
        }
    }

    fn remove_instance(&mut self, instance: &ServiceInstanceAddress) {
        self.entries
            .retain(|_, entry| entry.instance.as_ref() != Some(instance));
    }
}

/// Stateful operation encoders for every replicated state in one service
/// subscription.
pub struct ServiceStateEncoder {
    codecs: StateCodecRegistry<Encoder>,
}

/// Stateful operation decoders for every replicated state in one service
/// subscription.
pub struct ServiceStateDecoder {
    codecs: StateCodecRegistry<Decoder>,
}

/// A fresh encoder for one subscription.
#[must_use]
pub fn create_service_state_encoder() -> ServiceStateEncoder {
    ServiceStateEncoder {
        codecs: StateCodecRegistry::new(encoder),
    }
}

/// A fresh decoder for one subscription.
#[must_use]
pub fn create_service_state_decoder() -> ServiceStateDecoder {
    ServiceStateDecoder {
        codecs: StateCodecRegistry::new(decoder),
    }
}

impl Default for ServiceStateEncoder {
    fn default() -> Self {
        create_service_state_encoder()
    }
}

impl Default for ServiceStateDecoder {
    fn default() -> Self {
        create_service_state_decoder()
    }
}

impl ServiceStateEncoder {
    /// Encode a subscription baseline, restarting every dictionary.
    ///
    /// # Errors
    ///
    /// A duplicate state member.
    pub fn encode_snapshot(
        &mut self,
        snapshot: &ServiceSubscriptionSnapshot,
    ) -> Result<WireServiceSubscriptionSnapshot, ChordError> {
        self.codecs.reset();
        encode_subscription(snapshot, &mut self.codecs)
    }

    /// Encode one update.
    ///
    /// # Errors
    ///
    /// A duplicate or unknown state member.
    pub fn encode_update(
        &mut self,
        update: &ServiceProviderUpdate,
    ) -> Result<WireServiceProviderUpdate, ChordError> {
        Ok(match update {
            ServiceProviderUpdate::Reset { snapshot } => {
                self.codecs.reset();
                ServiceProviderUpdate::Reset {
                    snapshot: encode_subscription(snapshot, &mut self.codecs)?,
                }
            }
            ServiceProviderUpdate::State {
                instance,
                member,
                sequence,
                ops,
            } => ServiceProviderUpdate::State {
                instance: instance.clone(),
                member: member.clone(),
                sequence: *sequence,
                ops: Arc::from(self.codecs.get(instance.as_ref(), member)?.encode(ops)),
            },
            ServiceProviderUpdate::Replaced { snapshot } => {
                self.codecs.reset();
                ServiceProviderUpdate::Replaced {
                    snapshot: encode_instance(snapshot, &mut self.codecs)?,
                }
            }
            ServiceProviderUpdate::Spawned { instance } => ServiceProviderUpdate::Spawned {
                instance: encode_instance(instance, &mut self.codecs)?,
            },
            ServiceProviderUpdate::Unavailable => {
                self.codecs.reset();
                ServiceProviderUpdate::Unavailable
            }
            ServiceProviderUpdate::Closed { instance } => {
                self.codecs.remove_instance(instance);
                ServiceProviderUpdate::Closed {
                    instance: instance.clone(),
                }
            }
        })
    }
}

impl ServiceStateDecoder {
    /// Decode a subscription baseline, restarting every dictionary.
    ///
    /// # Errors
    ///
    /// A duplicate state member or an undecodable op.
    pub fn decode_snapshot(
        &mut self,
        snapshot: &WireServiceSubscriptionSnapshot,
    ) -> Result<ServiceSubscriptionSnapshot, ChordError> {
        self.codecs.reset();
        decode_subscription(snapshot, &mut self.codecs)
    }

    /// Decode one update.
    ///
    /// # Errors
    ///
    /// A duplicate or unknown state member, or an undecodable op.
    pub fn decode_update(
        &mut self,
        update: &WireServiceProviderUpdate,
    ) -> Result<ServiceProviderUpdate, ChordError> {
        Ok(match update {
            ServiceProviderUpdate::Reset { snapshot } => {
                self.codecs.reset();
                ServiceProviderUpdate::Reset {
                    snapshot: decode_subscription(snapshot, &mut self.codecs)?,
                }
            }
            ServiceProviderUpdate::State {
                instance,
                member,
                sequence,
                ops,
            } => ServiceProviderUpdate::State {
                instance: instance.clone(),
                member: member.clone(),
                sequence: *sequence,
                ops: Arc::from(self.codecs.get(instance.as_ref(), member)?.decode(ops)?),
            },
            ServiceProviderUpdate::Replaced { snapshot } => {
                self.codecs.reset();
                ServiceProviderUpdate::Replaced {
                    snapshot: decode_instance(snapshot, &mut self.codecs)?,
                }
            }
            ServiceProviderUpdate::Spawned { instance } => ServiceProviderUpdate::Spawned {
                instance: decode_instance(instance, &mut self.codecs)?,
            },
            ServiceProviderUpdate::Unavailable => {
                self.codecs.reset();
                ServiceProviderUpdate::Unavailable
            }
            ServiceProviderUpdate::Closed { instance } => {
                self.codecs.remove_instance(instance);
                ServiceProviderUpdate::Closed {
                    instance: instance.clone(),
                }
            }
        })
    }
}

fn encode_subscription(
    snapshot: &ServiceSubscriptionSnapshot,
    codecs: &mut StateCodecRegistry<Encoder>,
) -> Result<WireServiceSubscriptionSnapshot, ChordError> {
    Ok(ServiceSubscriptionSnapshot {
        service_id: snapshot.service_id.clone(),
        mode: snapshot.mode,
        instances: snapshot
            .instances
            .iter()
            .map(|instance| encode_instance(instance, codecs))
            .collect::<Result<_, _>>()?,
    })
}

fn decode_subscription(
    snapshot: &WireServiceSubscriptionSnapshot,
    codecs: &mut StateCodecRegistry<Decoder>,
) -> Result<ServiceSubscriptionSnapshot, ChordError> {
    Ok(ServiceSubscriptionSnapshot {
        service_id: snapshot.service_id.clone(),
        mode: snapshot.mode,
        instances: snapshot
            .instances
            .iter()
            .map(|instance| decode_instance(instance, codecs))
            .collect::<Result<_, _>>()?,
    })
}

fn encode_instance(
    instance: &ServiceInstanceSnapshot,
    codecs: &mut StateCodecRegistry<Encoder>,
) -> Result<WireServiceInstanceSnapshot, ChordError> {
    let mut members = Vec::with_capacity(instance.members.len());
    for member in &instance.members {
        members.push(match member {
            ServiceMemberSnapshot::Method { name } => {
                ServiceMemberSnapshot::Method { name: name.clone() }
            }
            ServiceMemberSnapshot::State {
                name,
                sequence,
                ops,
            } => {
                let encoded: Vec<WireOp> =
                    codecs.add(instance.instance.as_ref(), name)?.encode(ops);
                ServiceMemberSnapshot::State {
                    name: name.clone(),
                    sequence: *sequence,
                    ops: Arc::from(encoded),
                }
            }
        });
    }
    Ok(ServiceInstanceSnapshot {
        instance: instance.instance.clone(),
        members,
    })
}

fn decode_instance(
    instance: &WireServiceInstanceSnapshot,
    codecs: &mut StateCodecRegistry<Decoder>,
) -> Result<ServiceInstanceSnapshot, ChordError> {
    let mut members = Vec::with_capacity(instance.members.len());
    for member in &instance.members {
        members.push(match member {
            ServiceMemberSnapshot::Method { name } => {
                ServiceMemberSnapshot::Method { name: name.clone() }
            }
            ServiceMemberSnapshot::State {
                name,
                sequence,
                ops,
            } => {
                let decoded: Vec<Op> = codecs.add(instance.instance.as_ref(), name)?.decode(ops)?;
                ServiceMemberSnapshot::State {
                    name: name.clone(),
                    sequence: *sequence,
                    ops: Arc::from(decoded),
                }
            }
        });
    }
    Ok(ServiceInstanceSnapshot {
        instance: instance.instance.clone(),
        members,
    })
}

fn state_key(instance: Option<&ServiceInstanceAddress>, member: &str) -> StateKey {
    (
        instance.map(|instance| instance.key.clone()),
        instance.map(|instance| instance.generation),
        member.to_owned(),
    )
}

fn describe_state(instance: Option<&ServiceInstanceAddress>, member: &str) -> String {
    match instance {
        None => member.to_owned(),
        Some(instance) => format!("{}@{}.{member}", instance.key, instance.generation),
    }
}
