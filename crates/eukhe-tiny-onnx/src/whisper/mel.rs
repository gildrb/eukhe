//! Whisper's input features: the log-mel spectrogram of one 30 s window,
//! computed like the Hugging Face `WhisperFeatureExtractor`.

use std::f32::consts::PI;

use rustfft::num_complex::Complex;
use rustfft::FftPlanner;

/// The sample rate Whisper hears.
pub(crate) const SAMPLE_RATE: u32 = 16_000;
/// The samples of one window (30 s).
pub(crate) const WINDOW_SAMPLES: usize = 480_000;
/// The mel bands of a frame.
pub(crate) const MEL_BANDS: usize = 80;
/// The frames of one window.
pub(crate) const FRAMES: usize = 3_000;
const FFT_SIZE: usize = 400;
const HOP: usize = 160;
/// The frequency bins of one frame's spectrum.
pub(crate) const FREQUENCY_BINS: usize = FFT_SIZE / 2 + 1;
const MAX_FREQUENCY: f64 = 8_000.0;
/// The width of one frequency bin: `SAMPLE_RATE / FFT_SIZE` hertz.
const BIN_HERTZ: f64 = 40.0;

/// The `[MEL_BANDS, FRAMES]` log-mel features (row-major) of the first
/// 30 s of `samples` (16 kHz), zero-padded when shorter.
pub(crate) fn log_mel(samples: &[f32], filters: &[[f32; FREQUENCY_BINS]]) -> Vec<f32> {
    let clip = &samples[..samples.len().min(WINDOW_SAMPLES)];
    let half = FFT_SIZE / 2;
    // The window zero-padded to 30 s, then reflect-padded by half a frame
    // at both ends (`center=True`, `pad_mode="reflect"`).
    let mut padded = vec![0.0_f32; WINDOW_SAMPLES + FFT_SIZE];
    padded[half..half + clip.len()].copy_from_slice(clip);
    for offset in 1..=half {
        padded[half - offset] = padded[half + offset];
        padded[half + WINDOW_SAMPLES - 1 + offset] = padded[half + WINDOW_SAMPLES - 1 - offset];
    }
    #[allow(clippy::cast_precision_loss, reason = "window indices are below 400")]
    let hann: Vec<f32> = (0..FFT_SIZE)
        .map(|n| 0.5 - 0.5 * (2.0 * PI * n as f32 / FFT_SIZE as f32).cos())
        .collect();
    let fft = FftPlanner::<f32>::new().plan_fft_forward(FFT_SIZE);
    let mut buffer = vec![Complex::new(0.0_f32, 0.0); FFT_SIZE];
    let mut scratch = vec![Complex::new(0.0_f32, 0.0); fft.get_inplace_scratch_len()];
    let mut power = [0.0_f32; FREQUENCY_BINS];
    let mut features = vec![0.0_f32; MEL_BANDS * FRAMES];
    for frame in 0..FRAMES {
        let start = frame * HOP;
        for ((slot, sample), weight) in buffer
            .iter_mut()
            .zip(&padded[start..start + FFT_SIZE])
            .zip(&hann)
        {
            *slot = Complex::new(sample * weight, 0.0);
        }
        fft.process_with_scratch(&mut buffer, &mut scratch);
        for (bin, value) in power.iter_mut().zip(&buffer) {
            *bin = value.norm_sqr();
        }
        for (band, filter) in filters.iter().enumerate() {
            let energy: f32 = filter.iter().zip(&power).map(|(w, p)| w * p).sum();
            features[band * FRAMES + frame] = energy.max(1e-10).log10();
        }
    }
    let ceiling = features.iter().copied().fold(f32::NEG_INFINITY, f32::max) - 8.0;
    for value in &mut features {
        *value = (value.max(ceiling) + 4.0) / 4.0;
    }
    features
}

/// The `[MEL_BANDS, FREQUENCY_BINS]` slaney mel filterbank (row-major)
/// over 0..8 kHz with slaney area normalization (librosa's default, the
/// filters Whisper was trained with).
pub(crate) fn mel_filters() -> Vec<[f32; FREQUENCY_BINS]> {
    let mel_max = hertz_to_mel(MAX_FREQUENCY);
    #[allow(
        clippy::cast_precision_loss,
        reason = "band and bin indices are below 202"
    )]
    let edges: Vec<f64> = (0..MEL_BANDS + 2)
        .map(|index| mel_to_hertz(mel_max * index as f64 / (MEL_BANDS + 1) as f64))
        .collect();
    (0..MEL_BANDS)
        .map(|band| {
            let (low, center, high) = (edges[band], edges[band + 1], edges[band + 2]);
            let norm = 2.0 / (high - low);
            #[allow(
                clippy::cast_precision_loss,
                clippy::cast_possible_truncation,
                reason = "bin indices are below 202; weights fit f32"
            )]
            std::array::from_fn(|bin| {
                let frequency = bin as f64 * BIN_HERTZ;
                let rising = (frequency - low) / (center - low);
                let falling = (high - frequency) / (high - center);
                (rising.min(falling).max(0.0) * norm) as f32
            })
        })
        .collect()
}

const LINEAR_MEL_STEP: f64 = 200.0 / 3.0;
const LOG_START_HERTZ: f64 = 1_000.0;
const LOG_START_MEL: f64 = LOG_START_HERTZ / LINEAR_MEL_STEP;

fn log_step() -> f64 {
    6.4_f64.ln() / 27.0
}

fn hertz_to_mel(hertz: f64) -> f64 {
    if hertz < LOG_START_HERTZ {
        hertz / LINEAR_MEL_STEP
    } else {
        LOG_START_MEL + (hertz / LOG_START_HERTZ).ln() / log_step()
    }
}

fn mel_to_hertz(mel: f64) -> f64 {
    if mel < LOG_START_MEL {
        mel * LINEAR_MEL_STEP
    } else {
        LOG_START_HERTZ * (log_step() * (mel - LOG_START_MEL)).exp()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Values of `librosa.filters.mel(sr=16000, n_fft=400, n_mels=80)`
    /// (Whisper's `mel_filters.npz`): bands 0 and 1 at bins 0..4.
    #[test]
    fn filterbank_matches_librosa() {
        let filters = mel_filters();
        assert_eq!(filters.len(), MEL_BANDS);
        let low: Vec<f32> = filters[..2]
            .iter()
            .flat_map(|band| band[..4].iter().copied())
            .collect();
        let expected = [
            0.0_f32,
            0.024_862_594,
            0.0,
            0.0,
            0.0,
            0.001_990_822,
            0.022_871_772,
            0.0,
        ];
        assert!(
            low.iter()
                .zip(expected)
                .all(|(actual, expected)| (actual - expected).abs() < 1e-7),
            "{low:?}"
        );
        // The wide bands integrate to about 1 (slaney area normalization).
        for band in &filters[60..] {
            let area: f64 = band.iter().map(|w| f64::from(*w) * BIN_HERTZ).sum();
            assert!((area - 1.0).abs() < 0.02, "{area}");
        }
    }

    #[test]
    fn silence_features_are_flat() {
        let features = log_mel(&[], &mel_filters());
        assert_eq!(features, vec![-1.5_f32; MEL_BANDS * FRAMES]);
    }
}
