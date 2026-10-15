//! Port of pi-durable `search.ts`: BM25 tool search for code mode's
//! `searchTools()` and the `tool_search` tool, a copy of the coding agent's
//! tool search ranking.

use std::collections::HashMap;

const STOP_WORDS: [&str; 21] = [
    "a", "an", "and", "are", "as", "at", "be", "by", "for", "from", "in", "is", "it", "of", "on",
    "or", "that", "the", "this", "to", "with",
];

/// A document to rank: its `name` is returned, its `text` is searched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SearchDocument {
    /// What [`rank_documents`] returns for a match.
    pub name: String,
    /// The searched text.
    pub text: String,
}

/// Naive singular form, so `issues` matches `issue` and `searches` matches
/// `search`. Terms are ASCII, so byte lengths are JS lengths.
fn stem(term: &str) -> String {
    if term.len() > 4 && term.ends_with("ies") {
        return format!("{}y", &term[..term.len() - 3]);
    }
    if term.len() > 4
        && ["ches", "shes", "sses", "xes", "zes"]
            .iter()
            .any(|end| term.ends_with(end))
    {
        return term[..term.len() - 2].to_owned();
    }
    if term.len() > 3 && term.ends_with('s') && !term.ends_with("ss") {
        return term[..term.len() - 1].to_owned();
    }
    term.to_owned()
}

/// JS `text.replace(/([a-z0-9])([A-Z])/g, "$1 $2")`.
fn split_lower_upper(chars: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(chars.len());
    let mut index = 0;
    while index < chars.len() {
        let c = chars[index];
        if (c.is_ascii_lowercase() || c.is_ascii_digit())
            && chars.get(index + 1).is_some_and(char::is_ascii_uppercase)
        {
            out.extend([c, ' ', chars[index + 1]]);
            index += 2;
        } else {
            out.push(c);
            index += 1;
        }
    }
    out
}

/// JS `text.replace(/([A-Z]+)([A-Z][a-z])/g, "$1 $2")`: a run of two or more
/// capitals followed by a lowercase letter splits before its last capital.
fn split_acronym(chars: &[char]) -> Vec<char> {
    let mut out = Vec::with_capacity(chars.len());
    let mut index = 0;
    while index < chars.len() {
        if !chars[index].is_ascii_uppercase() {
            out.push(chars[index]);
            index += 1;
            continue;
        }
        let mut end = index;
        while chars.get(end).is_some_and(char::is_ascii_uppercase) {
            end += 1;
        }
        if end - index >= 2 && chars.get(end).is_some_and(char::is_ascii_lowercase) {
            out.extend_from_slice(&chars[index..end - 1]);
            out.extend([' ', chars[end - 1], chars[end]]);
            index = end + 1;
        } else {
            // No later start inside the run can match either.
            out.extend_from_slice(&chars[index..end]);
            index = end;
        }
    }
    out
}

/// Lowercase terms, split at camelCase boundaries and non-alphanumerics,
/// without stop words.
#[must_use]
pub fn tokenize(text: &str) -> Vec<String> {
    let chars: Vec<char> = text.chars().collect();
    let split: String = split_acronym(&split_lower_upper(&chars))
        .into_iter()
        .collect();
    split
        .to_lowercase()
        .split(|c: char| !(c.is_ascii_lowercase() || c.is_ascii_digit()))
        .filter(|term| !term.is_empty() && !STOP_WORDS.contains(term))
        .map(stem)
        .collect()
}

/// A count as a JS number.
#[expect(
    clippy::cast_precision_loss,
    reason = "term and document counts stay far below 2^52, where `f64` is exact"
)]
fn as_f64(count: usize) -> f64 {
    count as f64
}

/// Okapi BM25 (k1 1.2, b 0.75): the names of the best matches, best first;
/// ties keep document order.
#[must_use]
pub fn rank_documents(query: &str, documents: &[SearchDocument], limit: usize) -> Vec<String> {
    const K1: f64 = 1.2;
    const B: f64 = 0.75;
    let mut query_terms: Vec<String> = Vec::new();
    for term in tokenize(query) {
        if !query_terms.contains(&term) {
            query_terms.push(term);
        }
    }
    if query_terms.is_empty() || documents.is_empty() || limit == 0 {
        return Vec::new();
    }
    let term_counts: Vec<HashMap<String, usize>> = documents
        .iter()
        .map(|document| {
            let mut counts = HashMap::new();
            for term in tokenize(&document.text) {
                *counts.entry(term).or_insert(0) += 1;
            }
            counts
        })
        .collect();
    let lengths: Vec<f64> = term_counts
        .iter()
        .map(|counts| as_f64(counts.values().sum::<usize>()))
        .collect();
    let total: f64 = lengths.iter().sum();
    let mut average_length = total / as_f64(documents.len());
    if average_length == 0.0 {
        average_length = 1.0;
    }
    let document_count = as_f64(documents.len());
    let idf: Vec<f64> = query_terms
        .iter()
        .map(|term| {
            let frequency = as_f64(
                term_counts
                    .iter()
                    .filter(|counts| counts.contains_key(term))
                    .count(),
            );
            (1.0 + (document_count - frequency + 0.5) / (frequency + 0.5)).ln()
        })
        .collect();
    let mut matches: Vec<(&str, f64)> = Vec::new();
    for (index, document) in documents.iter().enumerate() {
        let mut score = 0.0;
        for (term, term_idf) in query_terms.iter().zip(&idf) {
            let Some(&count) = term_counts[index].get(term) else {
                continue;
            };
            let count = as_f64(count);
            let norm = K1 * (1.0 - B + (B * lengths[index]) / average_length);
            score += term_idf * ((count * (K1 + 1.0)) / (count + norm));
        }
        if score > 0.0 {
            matches.push((document.name.as_str(), score));
        }
    }
    matches.sort_by(|left, right| right.1.total_cmp(&left.1));
    matches
        .into_iter()
        .take(limit)
        .map(|(name, _)| name.to_owned())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn doc(name: &str, text: &str) -> SearchDocument {
        SearchDocument {
            name: name.to_owned(),
            text: text.to_owned(),
        }
    }

    #[test]
    fn tokenize_splits_camel_case_and_acronyms() {
        assert_eq!(
            tokenize("getHTTPResponseCode"),
            vec!["get", "http", "response", "code"]
        );
        assert_eq!(tokenize("mcp__docs__search"), vec!["mcp", "doc", "search"]);
        assert_eq!(tokenize("parseJSON2XML"), vec!["parse", "json2", "xml"]);
    }

    #[test]
    fn tokenize_drops_stop_words_and_stems() {
        assert_eq!(
            tokenize("Search the issues and matches, queries, boxes, class"),
            vec!["search", "issue", "match", "query", "box", "class"]
        );
        assert_eq!(tokenize("is it a"), Vec::<String>::new());
    }

    #[test]
    fn rank_orders_by_score() {
        let documents = vec![
            doc("write", "write file"),
            doc("read", "read file contents"),
            doc("search", "search issues"),
        ];
        assert_eq!(
            rank_documents("read the file", &documents, 10),
            vec!["read", "write"]
        );
        assert_eq!(rank_documents("read the file", &documents, 1), vec!["read"]);
    }

    #[test]
    fn rank_ties_keep_document_order() {
        let documents = vec![doc("b", "list issues"), doc("a", "list issues")];
        assert_eq!(rank_documents("issue", &documents, 5), vec!["b", "a"]);
    }

    #[test]
    fn rank_empty_cases() {
        let documents = vec![doc("a", "list issues")];
        assert_eq!(rank_documents("the", &documents, 5), Vec::<String>::new());
        assert_eq!(rank_documents("issue", &[], 5), Vec::<String>::new());
        assert_eq!(rank_documents("issue", &documents, 0), Vec::<String>::new());
        assert_eq!(
            rank_documents("nothing", &documents, 5),
            Vec::<String>::new()
        );
    }
}
