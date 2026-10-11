//! Header record helpers.

use reqwest::header::HeaderMap;

use eukhe_types::pi_ai::{IndexMap, ProviderHeaders};

/// Fetch's isomorphic decode of a header value: each byte is one code point.
fn isomorphic_decode(bytes: &[u8]) -> String {
    bytes.iter().map(|&byte| char::from(byte)).collect()
}

/// TS `headersToRecord(headers)`: the `Headers.entries()` view of a response's
/// headers. Names are lowercase and sorted; repeated values join with `", "`,
/// except `set-cookie`, whose entries stay separate (so the last one wins).
#[must_use]
pub fn headers_to_record(headers: &HeaderMap) -> IndexMap<String, String> {
    let mut names: Vec<&str> = headers
        .keys()
        .map(reqwest::header::HeaderName::as_str)
        .collect();
    names.sort_unstable();
    let mut record = IndexMap::with_capacity(names.len());
    for name in names {
        let mut values = headers
            .get_all(name)
            .iter()
            .map(|value| isomorphic_decode(value.as_bytes()));
        let value = if name == "set-cookie" {
            values.next_back().unwrap_or_default()
        } else {
            values.collect::<Vec<_>>().join(", ")
        };
        record.insert(name.to_owned(), value);
    }
    record
}

/// TS `providerHeadersToRecord(...headerSources)`: merge header sources in
/// order, case-insensitively; a later source overrides an earlier one (keeping
/// its own spelling and moving to the end), and a `None` value removes the
/// header. `None` when nothing remains.
#[must_use]
pub fn provider_headers_to_record(
    sources: &[Option<&ProviderHeaders>],
) -> Option<IndexMap<String, String>> {
    let mut merged: IndexMap<String, (String, String)> = IndexMap::new();
    for source in sources.iter().flatten() {
        for (name, value) in *source {
            let normalized = name.to_lowercase();
            merged.shift_remove(&normalized);
            if let Some(value) = value {
                merged.insert(normalized, (name.clone(), value.clone()));
            }
        }
    }
    (!merged.is_empty()).then(|| merged.into_values().collect())
}

#[cfg(test)]
mod tests {
    use reqwest::header::HeaderValue;

    use super::*;

    #[test]
    fn records_headers_like_fetch_entries() {
        let mut headers = HeaderMap::new();
        headers.append("x-b", HeaderValue::from_static("1"));
        headers.append("x-a", HeaderValue::from_static("2"));
        headers.append("x-b", HeaderValue::from_static("3"));
        headers.append("set-cookie", HeaderValue::from_static("a=1"));
        headers.append("set-cookie", HeaderValue::from_static("b=2"));
        let record = headers_to_record(&headers);
        let entries: Vec<(&str, &str)> = record
            .iter()
            .map(|(k, v)| (k.as_str(), v.as_str()))
            .collect();
        assert_eq!(
            entries,
            [("set-cookie", "b=2"), ("x-a", "2"), ("x-b", "1, 3")]
        );
    }

    #[test]
    fn merges_provider_headers_case_insensitively() {
        let defaults: ProviderHeaders = [
            ("User-Agent".to_owned(), Some("pi".to_owned())),
            ("X-Default".to_owned(), Some("1".to_owned())),
        ]
        .into_iter()
        .collect();
        let overrides: ProviderHeaders = [
            ("user-agent".to_owned(), Some("custom".to_owned())),
            ("x-default".to_owned(), None),
        ]
        .into_iter()
        .collect();
        let merged =
            provider_headers_to_record(&[Some(&defaults), None, Some(&overrides)]).unwrap();
        assert_eq!(
            merged.into_iter().collect::<Vec<_>>(),
            [("user-agent".to_owned(), "custom".to_owned())]
        );
        assert_eq!(provider_headers_to_record(&[None]), None);
    }
}
