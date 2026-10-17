//! WAV files in (transcribe) and out (say), and the linear resampler the
//! speech models' fixed rates need.

use std::path::{Path, PathBuf};

use eukhe_tiny::Audio;
use hound::{SampleFormat, WavReader, WavSpec, WavWriter};

/// A WAV file that could not be read or written.
#[derive(Debug, thiserror::Error)]
pub enum AudioFileError {
    /// The file is missing, unreadable, or not a WAV file.
    #[error("{}: {source}", path.display())]
    Read {
        path: PathBuf,
        #[source]
        source: hound::Error,
    },
    /// The WAV's sample encoding is not one this reads.
    #[error("{}: unsupported WAV encoding ({bits}-bit {format})", path.display())]
    Unsupported {
        path: PathBuf,
        bits: u16,
        format: &'static str,
    },
    /// The file could not be written.
    #[error("{}: {source}", path.display())]
    Write {
        path: PathBuf,
        #[source]
        source: hound::Error,
    },
}

/// Reads a WAV file (8/16/24/32-bit integer PCM or 32-bit float) as mono
/// samples: the channels are averaged.
///
/// # Errors
///
/// [`AudioFileError::Read`] when the file is not a readable WAV,
/// [`AudioFileError::Unsupported`] for other sample encodings.
pub fn read_wav(path: &Path) -> Result<Audio, AudioFileError> {
    let read = |source| AudioFileError::Read {
        path: path.to_path_buf(),
        source,
    };
    let reader = WavReader::open(path).map_err(read)?;
    let spec = reader.spec();
    let interleaved: Vec<f32> = match (spec.sample_format, spec.bits_per_sample) {
        (SampleFormat::Float, 32) => reader
            .into_samples::<f32>()
            .collect::<Result<_, _>>()
            .map_err(read)?,
        (SampleFormat::Int, bits @ (8 | 16 | 24 | 32)) => {
            let scale = 1.0 / f64::from(1_u32 << (bits - 1));
            reader
                .into_samples::<i32>()
                .map(|sample| {
                    sample.map(|value| {
                        #[allow(
                            clippy::cast_possible_truncation,
                            reason = "a scaled sample lies in -1.0..=1.0"
                        )]
                        let scaled = (f64::from(value) * scale) as f32;
                        scaled
                    })
                })
                .collect::<Result<_, _>>()
                .map_err(read)?
        }
        (format, bits) => {
            return Err(AudioFileError::Unsupported {
                path: path.to_path_buf(),
                bits,
                format: match format {
                    SampleFormat::Float => "float",
                    SampleFormat::Int => "integer",
                },
            });
        }
    };
    let channels = usize::from(spec.channels.max(1));
    let samples = if channels == 1 {
        interleaved
    } else {
        let share = 1.0 / f32::from(spec.channels);
        interleaved
            .chunks_exact(channels)
            .map(|frame| frame.iter().sum::<f32>() * share)
            .collect()
    };
    Ok(Audio {
        sample_rate: spec.sample_rate,
        samples,
    })
}

/// Writes mono samples as a 16-bit PCM WAV file; samples outside
/// `-1.0..=1.0` are clipped.
///
/// # Errors
///
/// [`AudioFileError::Write`] when the file cannot be written.
pub fn write_wav(path: &Path, audio: &Audio) -> Result<(), AudioFileError> {
    let write = |source| AudioFileError::Write {
        path: path.to_path_buf(),
        source,
    };
    let spec = WavSpec {
        channels: 1,
        sample_rate: audio.sample_rate,
        bits_per_sample: 16,
        sample_format: SampleFormat::Int,
    };
    let mut writer = WavWriter::create(path, spec).map_err(write)?;
    for sample in &audio.samples {
        #[allow(
            clippy::cast_possible_truncation,
            reason = "the clamped, rounded sample lies in i16's range"
        )]
        let value = (sample.clamp(-1.0, 1.0) * f32::from(i16::MAX)).round() as i16;
        writer.write_sample(value).map_err(write)?;
    }
    writer.finalize().map_err(write)
}

/// The clip at `rate` samples a second, linearly interpolated.
pub(crate) fn resample(audio: &Audio, rate: u32) -> Audio {
    if audio.sample_rate == rate || audio.samples.is_empty() || audio.sample_rate == 0 {
        return Audio {
            sample_rate: rate,
            samples: audio.samples.clone(),
        };
    }
    let step = f64::from(audio.sample_rate) / f64::from(rate);
    let input = &audio.samples;
    let len = u64::try_from(input.len()).unwrap_or(u64::MAX);
    let output_len = len * u64::from(rate) / u64::from(audio.sample_rate);
    let last = input.len() - 1;
    #[allow(
        clippy::cast_precision_loss,
        clippy::cast_possible_truncation,
        clippy::cast_sign_loss,
        reason = "sample positions stay far below 2^52 and are non-negative"
    )]
    let samples = (0..output_len)
        .map(|index| {
            let position = index as f64 * step;
            let left = (position.floor() as usize).min(last);
            let right = (left + 1).min(last);
            let fraction = (position - left as f64) as f32;
            input[left] + (input[right] - input[left]) * fraction
        })
        .collect();
    Audio {
        sample_rate: rate,
        samples,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wav_round_trip_keeps_rate_and_16_bit_samples() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("clip.wav");
        let audio = Audio {
            sample_rate: 24_000,
            samples: vec![0.0, 0.5, -0.5, 1.0, -1.0, 0.25],
        };
        write_wav(&path, &audio).expect("write");
        let quantized = Audio {
            sample_rate: 24_000,
            samples: vec![
                0.0,
                16_384.0 / 32_768.0,
                -16_384.0 / 32_768.0,
                32_767.0 / 32_768.0,
                -32_767.0 / 32_768.0,
                8_192.0 / 32_768.0,
            ],
        };
        assert_eq!(read_wav(&path).expect("read"), quantized);
    }

    #[test]
    fn stereo_float_wav_mixes_to_mono() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("stereo.wav");
        let spec = WavSpec {
            channels: 2,
            sample_rate: 8_000,
            bits_per_sample: 32,
            sample_format: SampleFormat::Float,
        };
        let mut writer = WavWriter::create(&path, spec).expect("create");
        for sample in [0.5_f32, 0.25, -1.0, 0.0] {
            writer.write_sample(sample).expect("sample");
        }
        writer.finalize().expect("finalize");
        assert_eq!(
            read_wav(&path).expect("read"),
            Audio {
                sample_rate: 8_000,
                samples: vec![0.375, -0.5],
            }
        );
    }

    #[test]
    fn resample_interpolates_linearly() {
        let audio = Audio {
            sample_rate: 2,
            samples: vec![0.0, 1.0, 0.0, -1.0],
        };
        assert_eq!(
            resample(&audio, 4),
            Audio {
                sample_rate: 4,
                samples: vec![0.0, 0.5, 1.0, 0.5, 0.0, -0.5, -1.0, -1.0],
            }
        );
        assert_eq!(
            resample(&audio, 1),
            Audio {
                sample_rate: 1,
                samples: vec![0.0, 0.0],
            }
        );
    }
}
