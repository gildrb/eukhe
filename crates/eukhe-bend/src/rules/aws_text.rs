//! The names and texts the Bedrock client reads (`bend/aws_text.bend`,
//! entry `bend/ffi_aws_text.bend`; `laws/aws_text.bend`): the partition
//! of a region, the request-id header, a base64 blob, the region of a
//! standard Bedrock endpoint host and of a Bedrock ARN, and a FIPS
//! pseudo-region's real region. Each is an explicit rule stated in plain
//! words in the laws.

use crate::wire::{Reader, Writer, STR_MAX};
use crate::{call, expect_core, Entry, Error};

/// The AWS partitions, in the order the rule tries them (the SDK's
/// `partitions.json`).
pub const PARTITIONS: [&str; 8] = [
    "aws",
    "aws-cn",
    "aws-eusc",
    "aws-iso",
    "aws-iso-b",
    "aws-iso-e",
    "aws-iso-f",
    "aws-us-gov",
];

/// What the base64 rule says of a text.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Base64 {
    /// A base64 text.
    Valid,
    /// Its length in UTF-16 code units is no multiple of 4.
    BadPadding,
    /// A char outside the alphabet, or `=` other than a final run of at
    /// most two.
    Invalid,
}

/// The index in [`PARTITIONS`] of the partition whose region shape
/// `region` has (`<prefix>-<word>-<number>`); `None` for no partition.
#[must_use]
pub fn partition(region: &str) -> Option<usize> {
    let mut request = Writer::new();
    request.tag(0).str(wire_text(region));
    expect_core(Entry::AwsText, index_answer(&mut request, 8))
}

/// The index of the first of `names` that is a request-id header name
/// (`x-<word chars or ->-request-id`, the last `-` optional).
#[must_use]
pub fn request_id_header(names: &[&str]) -> Option<usize> {
    let mut request = Writer::new();
    request.tag(1).count(names.len());
    for name in names {
        request.str(wire_text(name));
    }
    let below = u32::try_from(names.len()).unwrap_or(u32::MAX);
    expect_core(Entry::AwsText, index_answer(&mut request, below))
}

/// The base64 rule over `text` (sent in chunks of at most [`STR_MAX`]
/// chars; the rule reads them as one text).
#[must_use]
pub fn base64(text: &str) -> Base64 {
    let mut request = Writer::new();
    let chunks = chunks(text);
    request.tag(2).count(chunks.len());
    for chunk in chunks {
        request.str(chunk);
    }
    expect_core(Entry::AwsText, base64_answer(&mut request))
}

/// The region of a standard Bedrock runtime endpoint host
/// (`bedrock-runtime[-fips].<region>.amazonaws.com[.cn]`).
#[must_use]
pub fn endpoint_region(host: &str) -> Option<String> {
    let mut request = Writer::new();
    request.tag(3).str(wire_text(host));
    expect_core(Entry::AwsText, maybe_answer(&mut request))
}

/// The region of a Bedrock ARN (`arn:aws[-<x>]:bedrock:<region>:…`).
#[must_use]
pub fn arn_region(id: &str) -> Option<String> {
    let mut request = Writer::new();
    request.tag(4).str(wire_text(id));
    expect_core(Entry::AwsText, maybe_answer(&mut request))
}

/// `region` without its first FIPS part: the first place where
/// `fips-dkr-`, `fips-prod-` or `fips-` (the longest at that place) or
/// `-fips` stands is cut out (the SDK's `getRealRegion` replace).
#[must_use]
pub fn without_fips(region: &str) -> String {
    let mut request = Writer::new();
    request.tag(5).str(wire_text(region));
    expect_core(Entry::AwsText, str_answer(&mut request))
}

/// A `Maybe` index below `below`.
fn index_answer(request: &mut Writer, below: u32) -> Result<Option<usize>, Error> {
    let reply = call(Entry::AwsText, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let index = if reader.maybe()? {
        Some(reader.tag_of(below, "an index")? as usize)
    } else {
        None
    };
    reader.end()?;
    Ok(index)
}

fn base64_answer(request: &mut Writer) -> Result<Base64, Error> {
    let reply = call(Entry::AwsText, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let verdict = match reader.tag_of(3, "a base64 verdict")? {
        0 => Base64::Valid,
        1 => Base64::BadPadding,
        _ => Base64::Invalid,
    };
    reader.end()?;
    Ok(verdict)
}

fn maybe_answer(request: &mut Writer) -> Result<Option<String>, Error> {
    let reply = call(Entry::AwsText, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let found = if reader.maybe()? {
        Some(reader.str()?.to_owned())
    } else {
        None
    };
    reader.end()?;
    Ok(found)
}

fn str_answer(request: &mut Writer) -> Result<String, Error> {
    let reply = call(Entry::AwsText, &request.finish()?)?;
    let mut reader = Reader::reply(&reply)?;
    let text = reader.str()?.to_owned();
    reader.end()?;
    Ok(text)
}

/// `text` cut into runs of at most [`STR_MAX`] chars, in order.
fn chunks(text: &str) -> Vec<&str> {
    let mut chunks = Vec::new();
    let mut rest = text;
    while let Some((end, _)) = rest.char_indices().nth(STR_MAX) {
        chunks.push(&rest[..end]);
        rest = &rest[end..];
    }
    if !rest.is_empty() {
        chunks.push(rest);
    }
    chunks
}

/// A text as the wire carries it: its first [`STR_MAX`] chars.
fn wire_text(text: &str) -> &str {
    text.char_indices()
        .nth(STR_MAX)
        .map_or(text, |(end, _)| &text[..end])
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_core_reads_regions_and_headers() {
        assert_eq!(
            [
                partition("us-east-1"),
                partition("us-gov-west-1"),
                partition("eusc-de-east-1"),
                partition("us-isob-east-1"),
                partition("us-east"),
                partition("moon-base-1"),
            ],
            [Some(0), Some(7), Some(2), Some(4), None, None]
        );
        assert_eq!(
            request_id_header(&["x-request-id", "x-amzn-requestid", "x-amz-request-id"]),
            Some(1)
        );
        assert_eq!(request_id_header(&["content-type"]), None);
    }

    #[test]
    fn the_core_reads_base64_and_endpoints() {
        assert_eq!(
            [
                base64("QUJD"),
                base64("QQ=="),
                base64("QUJ"),
                base64("Q=Q="),
                base64("")
            ],
            [
                Base64::Valid,
                Base64::Valid,
                Base64::BadPadding,
                Base64::Invalid,
                Base64::Valid
            ]
        );
        assert_eq!(
            endpoint_region("bedrock-runtime-fips.us-east-1.amazonaws.com").as_deref(),
            Some("us-east-1")
        );
        assert_eq!(endpoint_region("bedrock.us-east-1.amazonaws.com"), None);
        assert_eq!(
            arn_region("arn:aws-cn:bedrock:cn-north-1:123:model/x").as_deref(),
            Some("cn-north-1")
        );
        assert_eq!(arn_region("arn:aws:bedrock:us-east-1"), None);
        assert_eq!(
            [
                without_fips("fips-dkr-us-east-1"),
                without_fips("us-east-1-fips"),
                without_fips("fips-us-fips"),
                without_fips("us-west-2"),
            ],
            ["us-east-1", "us-east-1", "us-fips", "us-west-2"]
        );
    }
}
