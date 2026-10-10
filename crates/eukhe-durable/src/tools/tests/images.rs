//! Port of `test/tools-images.test.ts`.
//!
//! Rust-only: the crate ships no image processor (TS's Photon backend is not
//! ported), so the cases that run TS's Photon processor use a scripted
//! [`ImageProcessor`] here and check what `read` does with its answers; the
//! cases that only test Photon's decoding (pixel output, EXIF rotation of
//! pixels, JPEG re-encoding sizes) have no Rust counterpart. Test images are
//! built byte by byte instead of encoded by Photon.

use std::collections::VecDeque;
use std::io::Write;
use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_pi_ai::models::{create_models, CreateModelsOptions};
use eukhe_pi_ai::providers::faux::{
    faux_provider, FauxModelDefinition, RegisterFauxProviderOptions,
};
use eukhe_types::pi_ai::{
    ImageContent, Modality, ModelImageInputLimits, ModelImageResizeOptions, ModelInputLimits,
    UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;
use serde_json::json;

use super::support::{execute, native, temp_dir, FakeApi, HookedEnv};
use crate::env::{
    BinaryReader, ExecutionEnv, FileError, FileInfo, FileSystem, LineRange, LineScan,
};
use crate::harness::types::{ModelRef, ToolExecutionResult, ToolRegistration};
use crate::images::exif_orientation;
use crate::tools::image::image_dimensions;
use crate::tools::image_processor::to_base64;
use crate::tools::{
    create_coding_tools, create_read_tool, ImageLimits, ImageProcessor, ImageResize, ImageSize,
    PreparedImage, ReadToolOptions, DEFAULT_IMAGE_LIMITS,
};

/// A PNG of `width` by `height`: its IHDR and a stand-in IDAT of `data`
/// bytes. Only the header matters to `read` without a processor.
fn png_with(width: u32, height: u32, data: usize) -> Vec<u8> {
    let chunk = |kind: &[u8], body: &[u8]| -> Vec<u8> {
        let length = u32::try_from(body.len()).expect("chunk length");
        let mut bytes = length.to_be_bytes().to_vec();
        bytes.extend_from_slice(kind);
        bytes.extend_from_slice(body);
        bytes.extend_from_slice(&[0, 0, 0, 0]);
        bytes
    };
    let mut ihdr = width.to_be_bytes().to_vec();
    ihdr.extend_from_slice(&height.to_be_bytes());
    ihdr.extend_from_slice(&[8, 6, 0, 0, 0]);
    let mut bytes = vec![0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a];
    bytes.extend(chunk(b"IHDR", &ihdr));
    // Pseudo-random, like the TS test's noise.
    let mut seed: u32 = 1;
    let idat: Vec<u8> = (0..data)
        .map(|_| {
            seed = seed.wrapping_mul(1_103_515_245).wrapping_add(12345);
            seed.to_be_bytes()[0]
        })
        .collect();
    bytes.extend(chunk(b"IDAT", &idat));
    bytes.extend(chunk(b"IEND", &[]));
    bytes
}

fn png(width: u32, height: u32) -> Vec<u8> {
    png_with(width, height, 16)
}

/// A baseline JPEG header of `width` by `height`: SOI, SOF0, EOI.
fn jpeg(width: u16, height: u16) -> Vec<u8> {
    let mut bytes = vec![0xff, 0xd8, 0xff, 0xc0, 0x00, 0x11, 0x08];
    bytes.extend_from_slice(&height.to_be_bytes());
    bytes.extend_from_slice(&width.to_be_bytes());
    bytes.extend_from_slice(&[3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1, 0xff, 0xd9]);
    bytes
}

/// A 24-bit BMP, which providers do not take inline.
fn bmp(width: u32, height: u32) -> Vec<u8> {
    let row = (width * 3).div_ceil(4) * 4;
    let size = 54 + row * height;
    let mut bytes = vec![0u8; usize::try_from(size).expect("bmp size")];
    bytes[0..2].copy_from_slice(b"BM");
    bytes[2..6].copy_from_slice(&size.to_le_bytes());
    bytes[10..14].copy_from_slice(&54u32.to_le_bytes());
    bytes[14..18].copy_from_slice(&40u32.to_le_bytes());
    bytes[18..22].copy_from_slice(&width.to_le_bytes());
    bytes[22..26].copy_from_slice(&height.to_le_bytes());
    bytes[26..28].copy_from_slice(&1u16.to_le_bytes());
    bytes[28..30].copy_from_slice(&24u16.to_le_bytes());
    bytes[34..38].copy_from_slice(&(row * height).to_le_bytes());
    for y in 0..height {
        for x in 0..width {
            let at = usize::try_from(54 + y * row + x * 3).expect("pixel offset");
            bytes[at..at + 3].copy_from_slice(&[0, 0, 255]);
        }
    }
    bytes
}

/// A 1x1 GIF with its logical screen size set to `width` by `height`.
fn gif(width: u16, height: u16) -> Vec<u8> {
    // "R0lGODlhAQABAIAAAAAAAP///yH5BAEAAAAALAAAAAABAAEAAAIBRAA7", decoded.
    let mut bytes = vec![
        0x47, 0x49, 0x46, 0x38, 0x39, 0x61, 0x01, 0x00, 0x01, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00,
        0x00, 0xff, 0xff, 0xff, 0x21, 0xf9, 0x04, 0x01, 0x00, 0x00, 0x00, 0x00, 0x2c, 0x00, 0x00,
        0x00, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x02, 0x01, 0x44, 0x00, 0x3b,
    ];
    bytes[6..8].copy_from_slice(&width.to_le_bytes());
    bytes[8..10].copy_from_slice(&height.to_le_bytes());
    bytes
}

/// A TIFF header whose first directory holds only Orientation =
/// `orientation`.
fn tiff(orientation: u16, little_endian: bool) -> Vec<u8> {
    let u16b = |value: u16| {
        if little_endian {
            value.to_le_bytes()
        } else {
            value.to_be_bytes()
        }
    };
    let u32b = |value: u32| {
        if little_endian {
            value.to_le_bytes()
        } else {
            value.to_be_bytes()
        }
    };
    let mut bytes = if little_endian {
        vec![0x49, 0x49]
    } else {
        vec![0x4d, 0x4d]
    };
    bytes.extend(u16b(42));
    bytes.extend(u32b(8));
    bytes.extend(u16b(1));
    bytes.extend(u16b(0x0112));
    bytes.extend(u16b(3));
    bytes.extend(u32b(1));
    bytes.extend(u16b(orientation));
    bytes.resize(26, 0);
    bytes
}

const EXIF_HEADER: [u8; 6] = [0x45, 0x78, 0x69, 0x66, 0, 0];

/// `jpeg` with an APP1 segment whose EXIF says `orientation`, after an APP0
/// segment when `app0`.
fn with_orientation(jpeg: &[u8], orientation: u16, little: bool, app0: bool) -> Vec<u8> {
    let mut exif = EXIF_HEADER.to_vec();
    exif.extend(tiff(orientation, little));
    let length = u16::try_from(exif.len() + 2).expect("segment length");
    let mut bytes = jpeg[..2].to_vec();
    if app0 {
        bytes.extend_from_slice(&[
            0xff, 0xe0, 0, 16, 0x4a, 0x46, 0x49, 0x46, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0,
        ]);
    }
    bytes.extend_from_slice(&[0xff, 0xe1]);
    bytes.extend_from_slice(&length.to_be_bytes());
    bytes.extend(exif);
    bytes.extend_from_slice(&jpeg[2..]);
    bytes
}

/// A RIFF WebP with a dummy `VP8 ` chunk and an `EXIF` chunk saying
/// `orientation`, its TIFF data bare or prefixed.
fn webp_with_orientation(orientation: u16, prefixed: bool) -> Vec<u8> {
    let chunk = |kind: &[u8], data: &[u8]| -> Vec<u8> {
        let size = u16::try_from(data.len()).expect("chunk size");
        let mut bytes = kind.to_vec();
        bytes.extend_from_slice(&size.to_le_bytes());
        bytes.extend_from_slice(&[0, 0]);
        bytes.extend_from_slice(data);
        if data.len() % 2 == 1 {
            bytes.push(0);
        }
        bytes
    };
    let mut exif = if prefixed {
        EXIF_HEADER.to_vec()
    } else {
        Vec::new()
    };
    exif.extend(tiff(orientation, true));
    let mut body = b"WEBP".to_vec();
    body.extend(chunk(b"VP8 ", &[1, 2, 3]));
    body.extend(chunk(b"EXIF", &exif));
    let length = u16::try_from(body.len()).expect("body length");
    let mut bytes = b"RIFF".to_vec();
    bytes.extend_from_slice(&length.to_le_bytes());
    bytes.extend_from_slice(&[0, 0]);
    bytes.extend(body);
    bytes
}

type OnRead = Arc<dyn Fn(f64, f64) + Send + Sync>;

/// A reader that records the largest read and calls `on_read` after each
/// positional read.
struct WatchedReader {
    inner: Box<dyn BinaryReader>,
    largest: Arc<Mutex<f64>>,
    on_read: Option<OnRead>,
}

impl BinaryReader for WatchedReader {
    fn info<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        self.inner.info(cx)
    }

    fn read<'a>(
        &'a self,
        offset: f64,
        length: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        async move {
            {
                let mut largest = self.largest.lock().unwrap_or_else(PoisonError::into_inner);
                *largest = largest.max(length);
            }
            let result = self.inner.read(offset, length, cx).await;
            if let Some(on_read) = &self.on_read {
                on_read(offset, length);
            }
            result
        }
        .boxed()
    }

    fn scan_lines<'a>(
        &'a self,
        range: LineRange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<LineScan, FileError>> {
        self.inner.scan_lines(range, cx)
    }

    fn close<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        self.inner.close(cx)
    }
}

/// The environment of a `read` call, with `on_read` seeing each positional
/// read of an opened file, and the largest read so far.
fn read_env(dir: &tempfile::TempDir, on_read: Option<OnRead>) -> (HookedEnv, Arc<Mutex<f64>>) {
    let largest = Arc::new(Mutex::new(0.0));
    let mut env = HookedEnv::new(native(dir));
    let seen = Arc::clone(&largest);
    env.open_binary_reader = Some(Arc::new(move |inner, path, options, cx| {
        let (largest, on_read) = (Arc::clone(&seen), on_read.clone());
        async move {
            let reader = inner.open_binary_reader(path, options, cx).await?;
            Ok(Box::new(WatchedReader {
                inner: reader,
                largest,
                on_read,
            }) as Box<dyn BinaryReader>)
        }
        .boxed()
    }));
    (env, largest)
}

#[derive(Default)]
struct ReadOptions {
    images: Option<Arc<dyn ImageProcessor>>,
    input: Option<Vec<Modality>>,
    resize: Option<ModelImageResizeOptions>,
    env: Option<Arc<dyn ExecutionEnv>>,
    tool: Option<Arc<ToolRegistration>>,
}

/// Run `read` on `bytes` written to `name`, for a conversation whose model
/// takes `input`.
async fn read(
    dir: &tempfile::TempDir,
    name: &str,
    bytes: &[u8],
    options: ReadOptions,
) -> Result<ToolExecutionResult, String> {
    std::fs::write(dir.path().join(name), bytes).expect("write image");
    let faux = faux_provider(RegisterFauxProviderOptions {
        provider: Some("test".to_owned()),
        models: Some(vec![FauxModelDefinition {
            id: "test".to_owned(),
            input: Some(
                options
                    .input
                    .unwrap_or_else(|| vec![Modality::Text, Modality::Image]),
            ),
            input_limits: options.resize.map(|resize| ModelInputLimits {
                images: Some(ModelImageInputLimits {
                    resize: Some(resize),
                    ..ModelImageInputLimits::default()
                }),
                ..ModelInputLimits::default()
            }),
            ..FauxModelDefinition::default()
        }]),
        ..RegisterFauxProviderOptions::default()
    });
    let models = create_models(CreateModelsOptions::default());
    models.set_provider(faux.provider.clone());
    let env = options
        .env
        .unwrap_or_else(|| Arc::new(native(dir)) as Arc<dyn ExecutionEnv>);
    let model = ModelRef {
        provider: "test".to_owned(),
        model_id: "test".to_owned(),
    };
    let api = FakeApi::with_model(Some(env), Some((models, model)));
    let tool = options.tool.unwrap_or_else(|| {
        create_read_tool(ReadToolOptions {
            images: options.images,
        })
    });
    execute(&tool, json!({ "path": name }), &api, &BACKGROUND_CONTEXT)
        .await
        .map_err(|error| error.to_string())
}

fn messages(result: &ToolExecutionResult) -> Vec<String> {
    result
        .diagnostics
        .iter()
        .flatten()
        .map(|diagnostic| diagnostic.message.clone())
        .collect()
}

fn only_image(result: &ToolExecutionResult) -> ImageContent {
    match result.output.as_deref() {
        Some([UserContentBlock::Image(image)]) => image.clone(),
        other => panic!("expected one image block, got {other:?}"),
    }
}

fn image_block(data: String, mime_type: &str) -> Vec<UserContentBlock> {
    vec![UserContentBlock::Image(ImageContent {
        data,
        mime_type: mime_type.to_owned(),
    })]
}

fn assert_refused(result: &ToolExecutionResult) {
    assert_eq!(result.output, Some(Vec::new()));
    assert_eq!(result.is_error, Some(true));
}

type Prepare = dyn Fn(&[u8], &str, ImageLimits) -> Option<PreparedImage> + Send + Sync;

/// A processor answering with `prepare`, recording the limits it saw.
struct ScriptedImages {
    prepare: Box<Prepare>,
    limits: Mutex<VecDeque<ImageLimits>>,
}

impl ScriptedImages {
    fn new(
        prepare: impl Fn(&[u8], &str, ImageLimits) -> Option<PreparedImage> + Send + Sync + 'static,
    ) -> Arc<Self> {
        Arc::new(Self {
            prepare: Box::new(prepare),
            limits: Mutex::new(VecDeque::new()),
        })
    }

    /// One that passes every image through untouched.
    fn identity() -> Arc<Self> {
        Self::new(|bytes, mime_type, _| {
            Some(PreparedImage {
                data: to_base64(bytes),
                mime_type: mime_type.to_owned(),
                resized: None,
                converted_from: None,
            })
        })
    }

    fn seen(&self) -> Vec<ImageLimits> {
        self.limits
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .copied()
            .collect()
    }
}

impl ImageProcessor for ScriptedImages {
    fn prepare<'a>(
        &'a self,
        bytes: &'a [u8],
        mime_type: &'a str,
        limits: ImageLimits,
    ) -> BoxFuture<'a, Option<PreparedImage>> {
        self.limits
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push_back(limits);
        futures::future::ready((self.prepare)(bytes, mime_type, limits)).boxed()
    }
}

/// A BMP converted to a PNG of `"converted"`.
fn bmp_to_png() -> Arc<ScriptedImages> {
    ScriptedImages::new(|_, mime_type, _| {
        Some(PreparedImage {
            data: to_base64(b"converted"),
            mime_type: "image/png".to_owned(),
            resized: None,
            converted_from: (mime_type != "image/png").then(|| mime_type.to_owned()),
        })
    })
}

// read of images, without an image processor

#[tokio::test]
async fn returns_a_supported_image_within_the_limits_as_it_is() {
    let dir = temp_dir();
    let png = png(8, 6);
    let result = read(&dir, "a.png", &png, ReadOptions::default())
        .await
        .unwrap();
    assert_eq!(
        result.output,
        Some(image_block(to_base64(&png), "image/png"))
    );
    assert_eq!(messages(&result), ["Read image file [image/png]."]);
    let tiny = read(&dir, "a.gif", &gif(1, 1), ReadOptions::default())
        .await
        .unwrap();
    assert_eq!(
        only_image(&tiny),
        ImageContent {
            data: to_base64(&gif(1, 1)),
            mime_type: "image/gif".to_owned(),
        }
    );
}

#[tokio::test]
async fn refuses_an_image_too_large_to_send_without_reading_it() {
    let dir = temp_dir();
    let (env, largest) = read_env(&dir, None);
    let result = read(
        &dir,
        "big.png",
        &png_with(1100, 1100, 3_600_000),
        ReadOptions {
            env: Some(Arc::new(env)),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_refused(&result);
    let message = &messages(&result)[0];
    assert!(
        message.starts_with("big.png is an image (image/png) of ")
            && message.contains(", too large to send"),
        "{message}"
    );
    // Only the header and the chunk walk, in blocks of at most 64 KiB.
    assert!(*largest.lock().unwrap_or_else(PoisonError::into_inner) <= 64.0 * 1024.0);
}

#[tokio::test]
async fn refuses_an_image_wider_or_taller_than_the_limits_by_its_header() {
    let dir = temp_dir();
    let wide = read(&dir, "wide.png", &png(2001, 2), ReadOptions::default())
        .await
        .unwrap();
    assert_refused(&wide);
    assert_eq!(
        messages(&wide),
        ["wide.png is an image (image/png) of 2001x2, larger than 2000x2000, and no image processor is configured to shrink it"]
    );
    let tall = read(&dir, "tall.gif", &gif(1, 3000), ReadOptions::default())
        .await
        .unwrap();
    assert!(messages(&tall)[0]
        .starts_with("tall.gif is an image (image/gif) of 1x3000, larger than 2000x2000"));
}

#[tokio::test]
async fn refuses_a_format_that_needs_converting() {
    let dir = temp_dir();
    let result = read(&dir, "a.bmp", &bmp(4, 4), ReadOptions::default())
        .await
        .unwrap();
    assert_refused(&result);
    assert_eq!(
        messages(&result),
        ["a.bmp is an image (image/bmp) that needs converting, and no image processor is configured"]
    );
}

#[tokio::test]
async fn says_when_the_model_sees_a_placeholder_instead_of_the_image() {
    let dir = temp_dir();
    let result = read(
        &dir,
        "a.png",
        &png(4, 4),
        ReadOptions {
            input: Some(vec![Modality::Text]),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(result.output.as_ref().map(Vec::len), Some(1));
    assert_eq!(
        messages(&result),
        ["Read image file [image/png]. The current model does not support images; it sees a placeholder instead."]
    );
}

#[tokio::test]
async fn applies_the_model_s_image_limits_instead_of_the_defaults() {
    let dir = temp_dir();
    let png = png(8, 6);
    let resize = || ModelImageResizeOptions {
        max_width: Some(4),
        ..ModelImageResizeOptions::default()
    };
    let refused = read(
        &dir,
        "a.png",
        &png,
        ReadOptions {
            resize: Some(resize()),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert!(messages(&refused)[0].contains("of 8x6, larger than 4x2000,"));
    let processor = ScriptedImages::identity();
    read(
        &dir,
        "a.png",
        &png,
        ReadOptions {
            resize: Some(resize()),
            images: Some(Arc::clone(&processor) as Arc<dyn ImageProcessor>),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(
        processor.seen(),
        [ImageLimits {
            max_width: 4,
            ..DEFAULT_IMAGE_LIMITS
        }]
    );
}

#[test]
fn lists_bmp_in_the_description_only_with_a_processor() {
    assert!(create_read_tool(ReadToolOptions::default())
        .description
        .contains("(jpg, png, gif, webp)"));
    let images: Arc<dyn ImageProcessor> = ScriptedImages::identity();
    assert!(create_read_tool(ReadToolOptions {
        images: Some(images)
    })
    .description
    .contains("(jpg, png, gif, webp, bmp)"));
}

// read of an image that changes while it is read

fn append(path: &std::path::Path, bytes: &[u8]) {
    std::fs::OpenOptions::new()
        .append(true)
        .open(path)
        .expect("open image")
        .write_all(bytes)
        .expect("append image");
}

#[expect(
    clippy::cast_precision_loss,
    reason = "test image sizes are far below 2^53"
)]
fn length_of(bytes: &[u8]) -> f64 {
    bytes.len() as f64
}

#[tokio::test]
async fn reads_it_again_rather_than_return_a_cut_off_image_even_when_it_grew() {
    let dir = temp_dir();
    let png = png(8, 6);
    let whole = length_of(&png);
    let whole_reads = Arc::new(Mutex::new(Vec::new()));
    let path = dir.path().join("growing.png");
    let reads = Arc::clone(&whole_reads);
    let (env, _) = read_env(
        &dir,
        Some(Arc::new(move |offset, length| {
            // A writer appends during the first read of the whole file; the second read sees it all.
            if offset != 0.0 || length < whole {
                return;
            }
            let mut reads = reads.lock().unwrap_or_else(PoisonError::into_inner);
            reads.push(length);
            if reads.len() == 1 {
                append(&path, &[0; 16]);
            }
        })),
    );
    let result = read(
        &dir,
        "growing.png",
        &png,
        ReadOptions {
            env: Some(Arc::new(env)),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(
        *whole_reads.lock().unwrap_or_else(PoisonError::into_inner),
        [whole, whole + 16.0]
    );
    let mut after = png.clone();
    after.extend([0; 16]);
    assert_eq!(only_image(&result).data, to_base64(&after));
}

#[tokio::test]
async fn fails_when_it_changes_during_the_second_read_too() {
    let dir = temp_dir();
    let png = png(8, 6);
    let whole = length_of(&png);
    let path = dir.path().join("busy.png");
    let (env, _) = read_env(
        &dir,
        Some(Arc::new(move |offset, length| {
            if offset == 0.0 && length >= whole {
                append(&path, &[0]);
            }
        })),
    );
    let error = read(
        &dir,
        "busy.png",
        &png,
        ReadOptions {
            env: Some(Arc::new(env)),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap_err();
    assert!(
        error.contains("busy.png changed while it was read"),
        "{error}"
    );
}

// read of images, with an image processor (scripted here; see the module doc)

#[tokio::test]
async fn passes_an_image_that_needs_no_change_through_untouched() {
    let dir = temp_dir();
    let png = png(8, 6);
    let images = || Some(ScriptedImages::identity() as Arc<dyn ImageProcessor>);
    let result = read(
        &dir,
        "a.png",
        &png,
        ReadOptions {
            images: images(),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(
        result.output,
        Some(image_block(to_base64(&png), "image/png"))
    );
    let gif = read(
        &dir,
        "a.gif",
        &gif(1, 1),
        ReadOptions {
            images: images(),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(only_image(&gif).mime_type, "image/gif");
}

#[tokio::test]
async fn scales_an_image_down_and_says_how_to_map_coordinates_back() {
    let dir = temp_dir();
    let processor = ScriptedImages::new(|_, mime_type, _| {
        Some(PreparedImage {
            data: to_base64(b"scaled"),
            mime_type: mime_type.to_owned(),
            resized: Some(ImageResize {
                from: ImageSize {
                    width: 4000,
                    height: 1000,
                },
                to: ImageSize {
                    width: 2000,
                    height: 500,
                },
            }),
            converted_from: None,
        })
    });
    let result = read(
        &dir,
        "wide.png",
        &png(4000, 1000),
        ReadOptions {
            images: Some(processor),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    let block = only_image(&result);
    assert_eq!(block.data, to_base64(b"scaled"));
    assert_eq!(
        messages(&result),
        [format!(
            "Read image file [{}]. Resized from 4000x1000 to 2000x500. Multiply coordinates by 2.00 to map them to the original.",
            block.mime_type
        )]
    );
}

#[tokio::test]
async fn says_when_an_image_was_re_encoded_in_another_format() {
    let dir = temp_dir();
    let processor = ScriptedImages::new(|_, _, _| {
        Some(PreparedImage {
            data: to_base64(b"jpeg"),
            mime_type: "image/jpeg".to_owned(),
            resized: None,
            converted_from: Some("image/png".to_owned()),
        })
    });
    let result = read(
        &dir,
        "big.png",
        &png(1100, 1100),
        ReadOptions {
            images: Some(processor),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(only_image(&result).mime_type, "image/jpeg");
    assert_eq!(
        messages(&result),
        ["Read image file [image/jpeg]. Converted from image/png to image/jpeg."]
    );
}

#[tokio::test]
async fn converts_a_format_providers_do_not_take_inline_to_png() {
    let dir = temp_dir();
    let result = read(
        &dir,
        "a.bmp",
        &bmp(4, 4),
        ReadOptions {
            images: Some(bmp_to_png()),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(only_image(&result).mime_type, "image/png");
    assert_eq!(
        messages(&result),
        ["Read image file [image/png]. Converted from image/bmp to image/png."]
    );
}

#[tokio::test]
async fn reports_bytes_it_cannot_decode_as_an_error() {
    let dir = temp_dir();
    let broken = png(4, 4)[..40].to_vec();
    let result = read(
        &dir,
        "broken.png",
        &broken,
        ReadOptions {
            images: Some(ScriptedImages::new(|_, _, _| None)),
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_refused(&result);
    assert_eq!(
        messages(&result),
        ["broken.png is an image (image/png) that cannot be prepared for the model"]
    );
}

#[tokio::test]
async fn is_what_create_coding_tools_with_images_gives_read() {
    let dir = temp_dir();
    let extension = create_coding_tools(ReadToolOptions {
        images: Some(bmp_to_png()),
    });
    let tool = extension
        .tools
        .iter()
        .find(|candidate| candidate.name == "read")
        .cloned();
    let result = read(
        &dir,
        "b.bmp",
        &bmp(4, 4),
        ReadOptions {
            tool,
            ..ReadOptions::default()
        },
    )
    .await
    .unwrap();
    assert_eq!(only_image(&result).mime_type, "image/png");
}

// EXIF orientation

#[test]
fn reads_big_and_little_endian_jpeg_exif_after_an_app0_segment_and_1_when_absent_or_out_of_range() {
    let jpeg = jpeg(2, 2);
    assert_eq!(
        exif_orientation(&with_orientation(&jpeg, 6, false, false)),
        6
    );
    assert_eq!(
        exif_orientation(&with_orientation(&jpeg, 8, true, false)),
        8
    );
    assert_eq!(
        exif_orientation(&with_orientation(&jpeg, 5, false, true)),
        5
    );
    assert_eq!(
        exif_orientation(&with_orientation(&jpeg, 9, false, false)),
        1
    );
    assert_eq!(exif_orientation(&jpeg), 1);
    assert_eq!(exif_orientation(&png(2, 2)), 1);
}

#[test]
fn reads_webp_exif_chunks_with_and_without_the_exif_prefix() {
    assert_eq!(exif_orientation(&webp_with_orientation(6, false)), 6);
    assert_eq!(exif_orientation(&webp_with_orientation(3, true)), 3);
}

// imageDimensions

#[test]
fn reads_the_size_each_format_declares_in_its_header() {
    let size = |width, height| Some(ImageSize { width, height });
    assert_eq!(image_dimensions(&png(7, 5), "image/png"), size(7, 5));
    assert_eq!(image_dimensions(&jpeg(7, 5), "image/jpeg"), size(7, 5));
    assert_eq!(
        image_dimensions(&with_orientation(&jpeg(7, 5), 6, false, true), "image/jpeg"),
        size(7, 5)
    );
    assert_eq!(
        image_dimensions(&gif(300, 200), "image/gif"),
        size(300, 200)
    );
    let webp = |kind: &[u8], data: &[u8]| -> Vec<u8> {
        let mut bytes = b"RIFF".to_vec();
        bytes.extend_from_slice(&[0, 0, 0, 0]);
        bytes.extend_from_slice(b"WEBP");
        bytes.extend_from_slice(kind);
        bytes.extend_from_slice(&[0, 0, 0, 0]);
        bytes.extend_from_slice(data);
        bytes.extend_from_slice(&[0; 16]);
        bytes
    };
    // VP8: frame tag, start code, then 14-bit width and height.
    assert_eq!(
        image_dimensions(
            &webp(
                b"VP8 ",
                &[0, 0, 0, 0x9d, 0x01, 0x2a, 0x2c, 0x01, 0xc8, 0x00]
            ),
            "image/webp"
        ),
        size(300, 200)
    );
    // VP8L: signature, then width - 1 and height - 1 in 14 bits each.
    // 299 | (199 << 14).
    let bits: u32 = 0x12b | (0xc7 << 14);
    let mut vp8l = vec![0x2f];
    vp8l.extend_from_slice(&bits.to_le_bytes());
    assert_eq!(
        image_dimensions(&webp(b"VP8L", &vp8l), "image/webp"),
        size(300, 200)
    );
    // VP8X: flags, then width - 1 and height - 1 in 24 bits each.
    assert_eq!(
        image_dimensions(
            &webp(b"VP8X", &[0, 0, 0, 0, 0x2b, 0x01, 0, 0xc7, 0, 0]),
            "image/webp"
        ),
        size(300, 200)
    );
    assert_eq!(image_dimensions(&[0xff, 0xd8, 0xff], "image/jpeg"), None);
}

// toBase64

/// Standard base64 decoding, the reference `to_base64` must invert (TS
/// compares with `Buffer`).
fn from_base64(text: &str) -> Vec<u8> {
    let alphabet = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut bits: u32 = 0;
    let mut count = 0;
    let mut bytes = Vec::new();
    for symbol in text.bytes().filter(|&symbol| symbol != b'=') {
        let value = alphabet
            .iter()
            .position(|&candidate| candidate == symbol)
            .expect("base64 symbol");
        bits = (bits << 6) | u32::try_from(value).expect("sextet");
        count += 6;
        if count >= 8 {
            count -= 8;
            bytes.push((bits >> count).to_le_bytes()[0]);
        }
    }
    bytes
}

#[test]
fn matches_buffer_for_every_remainder_length() {
    for (text, encoded) in [
        ("", ""),
        ("f", "Zg=="),
        ("fo", "Zm8="),
        ("foo", "Zm9v"),
        ("foob", "Zm9vYg=="),
        ("fooba", "Zm9vYmE="),
        ("foobar", "Zm9vYmFy"),
    ] {
        assert_eq!(to_base64(text.as_bytes()), encoded);
    }
    for length in [0usize, 1, 2, 3, 4, 5, 10_000] {
        let bytes: Vec<u8> = (0..length)
            .map(|index| u8::try_from(index * 37 % 256).expect("byte"))
            .collect();
        let encoded = to_base64(&bytes);
        assert_eq!(encoded.len(), length.div_ceil(3) * 4);
        assert_eq!(from_base64(&encoded), bytes);
    }
}
