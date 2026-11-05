//! The xxHash oneshot digests omp uses: the file tag and edit-store digest
//! are persisted, so the digests must stay byte-identical to the
//! `twox-hash` outputs they replaced (reference xxHash32/xxHash64).

const PRIME32_1: u32 = 0x9E37_79B1;
const PRIME32_2: u32 = 0x85EB_CA77;
const PRIME32_3: u32 = 0xC2B2_AE3D;
const PRIME32_4: u32 = 0x27D4_EB2F;
const PRIME32_5: u32 = 0x1656_67B1;

const PRIME64_1: u64 = 0x9E37_79B1_85EB_CA87;
const PRIME64_2: u64 = 0xC2B2_AE3D_27D4_EB4F;
const PRIME64_3: u64 = 0x1656_67B1_9E37_79F9;
const PRIME64_4: u64 = 0x85EB_CA77_C2B2_AE63;
const PRIME64_5: u64 = 0x27D4_EB2F_1656_67C5;

fn round32(acc: u32, lane: u32) -> u32 {
    acc.wrapping_add(lane.wrapping_mul(PRIME32_2))
        .rotate_left(13)
        .wrapping_mul(PRIME32_1)
}

/// xxHash32 of `input` with `seed`. The lane lanes are the 4-byte words of
/// the first `len / 16 * 16` bytes, cycling v1..v4; what remains runs
/// through the 4-byte and byte tails.
pub(crate) fn xxh32(seed: u32, input: &[u8]) -> u32 {
    let (words, bytes) = input.as_chunks::<4>();
    let (lane_words, tail_words) = words.split_at(input.len() / 16 * 4);
    let mut hash = if input.len() >= 16 {
        let mut vs = [
            seed.wrapping_add(PRIME32_1).wrapping_add(PRIME32_2),
            seed.wrapping_add(PRIME32_2),
            seed,
            seed.wrapping_sub(PRIME32_1),
        ];
        for (index, word) in lane_words.iter().enumerate() {
            let slot = index % 4;
            if let Some(value) = vs.get_mut(slot) {
                *value = round32(*value, u32::from_le_bytes(*word));
            }
        }
        let [v1, v2, v3, v4] = vs;
        v1.rotate_left(1)
            .wrapping_add(v2.rotate_left(7))
            .wrapping_add(v3.rotate_left(12))
            .wrapping_add(v4.rotate_left(18))
    } else {
        seed.wrapping_add(PRIME32_5)
    };
    // The reference adds `(u32)len`: past 4 GiB it truncates, like C.
    #[allow(clippy::cast_possible_truncation)]
    {
        hash = hash.wrapping_add(input.len() as u32);
    }
    for word in tail_words {
        hash = hash
            .wrapping_add(u32::from_le_bytes(*word).wrapping_mul(PRIME32_3))
            .rotate_left(17)
            .wrapping_mul(PRIME32_4);
    }
    for byte in bytes {
        hash = hash
            .wrapping_add(u32::from(*byte).wrapping_mul(PRIME32_5))
            .rotate_left(11)
            .wrapping_mul(PRIME32_1);
    }
    hash ^= hash >> 15;
    hash = hash.wrapping_mul(PRIME32_2);
    hash ^= hash >> 13;
    hash = hash.wrapping_mul(PRIME32_3);
    hash ^= hash >> 16;
    hash
}

fn round64(acc: u64, lane: u64) -> u64 {
    acc.wrapping_add(lane.wrapping_mul(PRIME64_2))
        .rotate_left(31)
        .wrapping_mul(PRIME64_1)
}

/// xxHash64 of `input` with `seed`. The lane lanes are the 8-byte words of
/// the first `len / 32 * 32` bytes, cycling v1..v4; what remains runs
/// through the 8-byte, 4-byte and byte tails.
pub(crate) fn xxh64(seed: u64, input: &[u8]) -> u64 {
    let (words, rest) = input.as_chunks::<8>();
    let (lane_words, tail_words) = words.split_at(input.len() / 32 * 4);
    let mut hash = if input.len() >= 32 {
        let mut vs = [
            seed.wrapping_add(PRIME64_1).wrapping_add(PRIME64_2),
            seed.wrapping_add(PRIME64_2),
            seed,
            seed.wrapping_sub(PRIME64_1),
        ];
        for (index, word) in lane_words.iter().enumerate() {
            let slot = index % 4;
            if let Some(value) = vs.get_mut(slot) {
                *value = round64(*value, u64::from_le_bytes(*word));
            }
        }
        let [v1, v2, v3, v4] = vs;
        let mut merged = v1
            .rotate_left(1)
            .wrapping_add(v2.rotate_left(7))
            .wrapping_add(v3.rotate_left(12))
            .wrapping_add(v4.rotate_left(18));
        for value in [v1, v2, v3, v4] {
            merged ^= round64(0, value);
            merged = merged.wrapping_mul(PRIME64_1).wrapping_add(PRIME64_4);
        }
        merged
    } else {
        seed.wrapping_add(PRIME64_5)
    };
    hash = hash.wrapping_add(input.len() as u64);
    for word in tail_words {
        hash ^= round64(0, u64::from_le_bytes(*word));
        hash = hash
            .rotate_left(27)
            .wrapping_mul(PRIME64_1)
            .wrapping_add(PRIME64_4);
    }
    let (fours, bytes) = rest.as_chunks::<4>();
    if let Some(word) = fours.first() {
        hash ^= u64::from(u32::from_le_bytes(*word)).wrapping_mul(PRIME64_1);
        hash = hash
            .rotate_left(23)
            .wrapping_mul(PRIME64_2)
            .wrapping_add(PRIME64_3);
    }
    for byte in bytes {
        hash ^= u64::from(*byte).wrapping_mul(PRIME64_5);
        hash = hash.rotate_left(11).wrapping_mul(PRIME64_1);
    }
    hash ^= hash >> 33;
    hash = hash.wrapping_mul(PRIME64_2);
    hash ^= hash >> 29;
    hash = hash.wrapping_mul(PRIME64_3);
    hash ^= hash >> 32;
    hash
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Vectors captured from `twox-hash` 2 before the swap (the file tag
    /// and store digests persist), headed by the spec's canonical empty
    /// inputs. Tuples: (input, `xxh32` seed 0, `xxh32` seed 1, `xxh64`
    /// seed 0, `xxh64` seed 1, `xxh64` seed `PRIME64_1`).
    #[test]
    fn matches_twox_hash_reference_outputs() {
        type Case = (&'static [u8], u32, u32, u64, u64, u64);
        let unicode = "résumé — ünïcode ✓".as_bytes();
        let cases: [Case; 10] = [
            (
                b"",
                0x02cc_5d05,
                0x0b2c_b792,
                0xef46_db37_51d8_e999,
                0xd5af_ba13_36a3_be4b,
                0x6ec6_d05f_61c7_e7a7,
            ),
            (
                b"a",
                0x550d_7456,
                0xf514_706f,
                0xd24e_c4f1_a98c_6e5b,
                0xdec2_bc81_c3cd_46c6,
                0x727c_10e0_d238_e188,
            ),
            (
                b"abc",
                0x32d1_53ff,
                0xaa3d_a8ff,
                0x44bc_2cf5_ad77_0999,
                0xbea9_ca81_9932_8908,
                0xa7cb_2aac_405e_36c7,
            ),
            (
                b"abcdefgh",
                0x0bb3_c6bb,
                0xb646_e7e3,
                0x3ad3_5177_5b46_34b7,
                0x8305_1257_1021_2a61,
                0x980d_1f27_e25f_8670,
            ),
            (
                b"0123456789abcdef",
                0xc2c4_5b69,
                0xf31f_e1cf,
                0x5c5b_90c3_4e37_6d0b,
                0x9539_8bc8_fb82_b74d,
                0xb887_93e9_2567_83a6,
            ),
            (
                b"0123456789abcdefX",
                0x658e_4f53,
                0x9927_154f,
                0x18c2_127c_fbe6_be0d,
                0xab76_e311_9bf3_9616,
                0xc37e_2f88_935c_ef11,
            ),
            (
                &[b'x'; 32],
                0x25ce_f61d,
                0xcf51_170d,
                0xe2df_261f_c2ec_30eb,
                0x926d_5508_ef68_7acb,
                0xe9d4_d41a_dd98_fbb1,
            ),
            (
                &[b'y'; 33],
                0x2e1b_1f67,
                0x3b07_ba4f,
                0xf27d_5a84_556c_aef4,
                0x37b1_91d6_31bf_575c,
                0x3ad0_aaf4_d62d_0dc4,
            ),
            (
                unicode,
                0x9f73_0466,
                0xfdc5_82b4,
                0xbe21_b614_ad21_c333,
                0xaab8_4860_250b_ae18,
                0x2c2e_d647_0d24_8112,
            ),
            (
                &[b'z'; 1000],
                0x2c53_b734,
                0x50bd_f773,
                0x82ef_f5a2_8992_b6be,
                0xbf01_5eec_fae4_5800,
                0x3f72_efa3_b884_05ee,
            ),
        ];
        for (index, (input, h32_0, h32_1, h64_0, h64_1, h64_seed)) in cases.into_iter().enumerate()
        {
            assert_eq!(xxh32(0, input), h32_0, "xxh32 seed 0, case {index}");
            assert_eq!(xxh32(1, input), h32_1, "xxh32 seed 1, case {index}");
            assert_eq!(xxh64(0, input), h64_0, "xxh64 seed 0, case {index}");
            assert_eq!(xxh64(1, input), h64_1, "xxh64 seed 1, case {index}");
            assert_eq!(
                xxh64(PRIME64_1, input),
                h64_seed,
                "xxh64 prime seed, case {index}"
            );
        }
    }
}
