//! Image helpers for [`ImageProcessor`](crate::tools::ImageProcessor)
//! implementations (`pi-durable/images`).
//!
//! Rust-only: TS's Photon backend (`images/index.ts`, `images/node.ts`,
//! `images/cloudflare.ts`) is not ported; only its byte-level EXIF reader is.

mod exif;

pub use exif::exif_orientation;
