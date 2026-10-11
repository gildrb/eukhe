//! Time-ordered `UUIDv7` generation.

use std::sync::{Mutex, PoisonError};

const MAX_UUID_V7_TIMESTAMP: f64 = 281_474_976_710_655.0; // 0xffffffffffff
const MAX_SEQUENCE: u64 = (1 << 41) - 1;

/// Errors of [`uuidv7`].
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum UuidError {
    /// TS `RangeError`: invalid timestamp or exhausted sequence.
    #[error("{0}")]
    Range(String),
    /// The OS random source failed (JS `getRandomValues` cannot fail).
    #[error("random source failed: {0}")]
    Random(String),
}

/// The process-wide generator state: the last ordinary timestamp (so ids stay
/// ordered when the clock goes back) and the 41-bit sequence seeded from the
/// first id's random bytes.
#[derive(Debug, Default)]
pub(crate) struct UuidV7Generator {
    last_ordinary_timestamp: Option<u64>,
    sequence: Option<u64>,
}

impl UuidV7Generator {
    /// Generate one id. `timestamp_ms` is preserved for follower ids; without
    /// it the id uses `now_ms`, never older than the previous ordinary id.
    pub(crate) fn generate(
        &mut self,
        timestamp_ms: Option<f64>,
        now_ms: f64,
        fill_random: &mut dyn FnMut(&mut [u8; 16]) -> Result<(), UuidError>,
    ) -> Result<String, UuidError> {
        let requested = timestamp_ms.unwrap_or(now_ms);
        if requested.fract() != 0.0 || !(0.0..=MAX_UUID_V7_TIMESTAMP).contains(&requested) {
            return Err(UuidError::Range(
                "UUIDv7 timestamp must be an integer between 0 and 281474976710655".to_owned(),
            ));
        }
        // Validated: a whole number in 0..=2^48 - 1.
        #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
        let requested = requested as u64;
        let effective = if timestamp_ms.is_some() {
            requested
        } else {
            let effective = self
                .last_ordinary_timestamp
                .map_or(requested, |last| requested.max(last));
            self.last_ordinary_timestamp = Some(effective);
            effective
        };

        let mut bytes = [0u8; 16];
        fill_random(&mut bytes)?;
        let sequence = match self.sequence {
            None => {
                (u64::from(bytes[1]) << 32)
                    | (u64::from(bytes[2]) << 24)
                    | (u64::from(bytes[3]) << 16)
                    | (u64::from(bytes[4]) << 8)
                    | u64::from(bytes[5])
            }
            Some(MAX_SEQUENCE) => {
                return Err(UuidError::Range(
                    "UUIDv7 generator sequence exhausted".to_owned(),
                ));
            }
            Some(previous) => previous + 1,
        };
        self.sequence = Some(sequence);

        for (index, byte) in bytes.iter_mut().take(6).enumerate() {
            *byte = effective.to_be_bytes()[index + 2];
        }
        // Each value is masked to its byte width first.
        #[allow(clippy::cast_possible_truncation)]
        {
            bytes[6] = 0x70 | ((sequence >> 37) & 0x0f) as u8;
            bytes[7] = ((sequence >> 29) & 0xff) as u8;
            bytes[8] = 0x80 | ((sequence >> 23) & 0x3f) as u8;
            bytes[9] = ((sequence >> 15) & 0xff) as u8;
            bytes[10] = ((sequence >> 7) & 0xff) as u8;
            bytes[11] = (((sequence & 0x7f) << 1) as u8) | (bytes[11] & 0x01);
        }

        let hex: String = bytes
            .iter()
            .fold(String::with_capacity(32), |mut hex, byte| {
                use std::fmt::Write as _;
                // Writing to a `String` cannot fail.
                let _ = write!(hex, "{byte:02x}");
                hex
            });
        Ok(format!(
            "{}-{}-{}-{}-{}",
            &hex[0..8],
            &hex[8..12],
            &hex[12..16],
            &hex[16..20],
            &hex[20..32]
        ))
    }
}

static GENERATOR: Mutex<UuidV7Generator> = Mutex::new(UuidV7Generator {
    last_ordinary_timestamp: None,
    sequence: None,
});

/// Generate a time-ordered `UUIDv7`. A supplied timestamp is preserved for follower ids.
///
/// # Errors
///
/// [`UuidError::Range`] when the timestamp is not an integer in `0..=2^48 - 1`
/// or the 41-bit sequence is exhausted.
pub fn uuidv7(timestamp_ms: Option<f64>) -> Result<String, UuidError> {
    // `Date.now()` is a whole number of milliseconds, far below 2^53.
    #[allow(clippy::cast_precision_loss)]
    let now = super::now_ms() as f64;
    GENERATOR
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .generate(timestamp_ms, now, &mut |bytes| {
            getrandom::fill(bytes).map_err(|error| UuidError::Random(error.to_string()))
        })
}

#[cfg(test)]
mod tests {
    use regex::Regex;

    use super::*;

    const TIMESTAMP: f64 = 1_250_999_896_491.0; // 0x0123456789ab

    fn parse_timestamp(uuid: &str) -> u64 {
        u64::from_str_radix(&uuid.replace('-', "")[..12], 16).unwrap()
    }

    fn os_random(bytes: &mut [u8; 16]) -> Result<(), UuidError> {
        getrandom::fill(bytes).map_err(|error| UuidError::Random(error.to_string()))
    }

    #[test]
    fn generates_ordered_uuidv7s_while_preserving_follower_timestamps() {
        let pattern =
            Regex::new("^[0-9a-f]{8}-[0-9a-f]{4}-7[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$")
                .unwrap();
        let mut generator = UuidV7Generator::default();
        let first = generator.generate(None, TIMESTAMP, &mut os_random).unwrap();
        let second = generator.generate(None, TIMESTAMP, &mut os_random).unwrap();
        let after_rollback = generator
            .generate(None, TIMESTAMP - 1.0, &mut os_random)
            .unwrap();
        let after_advance = generator
            .generate(None, TIMESTAMP + 1.0, &mut os_random)
            .unwrap();
        let ordinary = vec![first, second, after_rollback, after_advance];
        let follower_timestamp = TIMESTAMP - 1_000.0;
        let followers = vec![
            generator
                .generate(Some(follower_timestamp), TIMESTAMP + 1.0, &mut os_random)
                .unwrap(),
            generator
                .generate(Some(follower_timestamp), TIMESTAMP + 1.0, &mut os_random)
                .unwrap(),
        ];

        for id in ordinary.iter().chain(&followers) {
            assert!(pattern.is_match(id), "{id}");
        }
        let mut sorted = ordinary.clone();
        sorted.sort();
        assert_eq!(ordinary, sorted);
        assert_eq!(
            ordinary
                .iter()
                .collect::<std::collections::HashSet<_>>()
                .len(),
            ordinary.len()
        );
        let base = 0x0123_4567_89ab;
        assert_eq!(
            ordinary
                .iter()
                .map(|id| parse_timestamp(id))
                .collect::<Vec<_>>(),
            [base, base, base, base + 1]
        );
        assert_eq!(
            followers
                .iter()
                .map(|id| parse_timestamp(id))
                .collect::<Vec<_>>(),
            [base - 1_000, base - 1_000]
        );
        assert_ne!(followers[0], followers[1]);
    }

    #[test]
    fn uses_fresh_randomness_for_every_uuid_tail() {
        let mut generator = UuidV7Generator::default();
        let mut random_byte = 0u8;
        let mut fill = |bytes: &mut [u8; 16]| {
            random_byte += 1;
            bytes.fill(random_byte);
            Ok(())
        };
        let first = generator.generate(Some(TIMESTAMP), 0.0, &mut fill).unwrap();
        let second = generator.generate(Some(TIMESTAMP), 0.0, &mut fill).unwrap();
        assert_eq!(
            [&first[first.len() - 8..], &second[second.len() - 8..]],
            ["01010101", "02020202"]
        );
    }

    #[test]
    fn accepts_timestamp_boundaries() {
        for timestamp in [0.0, 2f64.powi(48) - 1.0] {
            let id = uuidv7(Some(timestamp)).unwrap();
            #[allow(clippy::cast_precision_loss)]
            let parsed = parse_timestamp(&id) as f64;
            assert!((parsed - timestamp).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn rejects_invalid_timestamps() {
        for timestamp in [-1.0, 2f64.powi(48), 1.5, f64::NAN, f64::INFINITY] {
            assert!(uuidv7(Some(timestamp)).is_err(), "{timestamp}");
        }
    }
}
