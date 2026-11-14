//! The text a model row shows (the `/model` picker, `/scoped-models`): the
//! model's name, with its id when another model of the same provider
//! carries the same name, cut to its column so that the listed rows still
//! differ on screen.

use std::collections::HashMap;

use eukhe_types::ai::Model;
use unicode_segmentation::UnicodeSegmentation;

use crate::glyphs::ELLIPSIS;
use crate::width::{grapheme_width, str_width, truncate_middle, truncate_to_width};

/// The label of each model, indexed like `models`: its name, or
/// `<name> (<id>)` when another model of the same provider has that name
/// (the trailing provider column cannot tell them apart).
pub(crate) fn row_labels(models: &[Model]) -> Vec<String> {
    let mut counts: HashMap<(&str, &str), usize> = HashMap::new();
    for model in models {
        *counts
            .entry((model.provider.as_str(), model.name.as_str()))
            .or_default() += 1;
    }
    models
        .iter()
        .map(|model| {
            let shared = counts
                .get(&(model.provider.as_str(), model.name.as_str()))
                .is_some_and(|count| *count > 1);
            if shared && model.name != model.id {
                format!("{} ({})", model.name, model.id)
            } else {
                model.name.clone()
            }
        })
        .collect()
}

/// For each label, how many leading graphemes it shares with the most
/// similar other label of `labels` (0 when none shares a start): the
/// position where it starts to differ from the rows around it.
pub(crate) fn shared_prefixes(labels: &[&str]) -> Vec<usize> {
    let split: Vec<Vec<&str>> = labels
        .iter()
        .map(|label| label.graphemes(true).collect())
        .collect();
    split
        .iter()
        .map(|label| {
            split
                .iter()
                .filter(|other| *other != label)
                .map(|other| label.iter().zip(other).take_while(|(a, b)| a == b).count())
                .max()
                .unwrap_or(0)
        })
        .collect()
}

/// `label` in at most `width` columns: whole when it fits, else cut in the
/// middle; when the middle cut would hide where the label starts to differ
/// from the other rows (`shared` leading graphemes in common), the cut
/// keeps that part instead (`Thinking Machines: Inkling 2 Fast Edition`
/// beside `... 2 Preview Edition`, in 15 columns: `...Fast Edition`).
pub(crate) fn cut_label(label: &str, shared: usize, width: usize) -> String {
    if str_width(label) <= width {
        return label.to_string();
    }
    let middle = truncate_middle(label, width, ELLIPSIS);
    let graphemes: Vec<&str> = label.graphemes(true).collect();
    let ellipsis_width = str_width(ELLIPSIS);
    if shared == 0 || shared >= graphemes.len() || width < 2 * ellipsis_width + 1 {
        return middle;
    }
    let cut: Vec<&str> = middle.graphemes(true).collect();
    let head = cut
        .iter()
        .zip(&graphemes)
        .take_while(|(a, b)| a == b)
        .count();
    let tail = cut
        .iter()
        .rev()
        .zip(graphemes.iter().rev())
        .take_while(|(a, b)| a == b)
        .count();
    if head > shared || graphemes.len() - tail <= shared {
        return middle;
    }
    let rest = graphemes[shared..].concat();
    let room = width - ellipsis_width;
    let rest_width = str_width(&rest);
    if rest_width > room {
        return format!("{ELLIPSIS}{}", truncate_to_width(&rest, room, ELLIPSIS));
    }
    let mut lead = String::new();
    let mut used = 0;
    for grapheme in &graphemes[..shared] {
        let grapheme_columns = grapheme_width(grapheme);
        if used + grapheme_columns > room - rest_width {
            break;
        }
        lead.push_str(grapheme);
        used += grapheme_columns;
    }
    format!("{lead}{ELLIPSIS}{rest}")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn model(provider: &str, id: &str, name: &str) -> Model {
        serde_json::from_value(serde_json::json!({
            "id": id, "name": name, "api": "openai-completions", "provider": provider,
            "baseUrl": "https://x.test", "reasoning": false, "input": ["text"],
            "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0 },
            "contextWindow": 1000, "maxTokens": 100
        }))
        .expect("model")
    }

    /// Two labels that differ only in the middle keep the differing part
    /// when cut; a label the middle cut already tells apart keeps the
    /// middle cut.
    #[test]
    fn cuts_keep_where_the_rows_differ() {
        let labels = [
            "Thinking Machines: Inkling 2 Preview Edition",
            "Thinking Machines: Inkling 2 Fast Edition",
            "Claude Haiku 5.5",
        ];
        let shared = shared_prefixes(&labels);
        assert_eq!(shared, vec![29, 29, 0]);
        let cuts: Vec<String> = labels
            .iter()
            .zip(&shared)
            .map(|(label, shared)| cut_label(label, *shared, 15))
            .collect();
        assert_eq!(
            cuts,
            vec!["...Preview E...", "...Fast Edition", "Claude...ku 5.5"]
        );
        // Room for a lead: the label's start fills it.
        assert_eq!(cut_label(labels[1], 29, 20), "Think...Fast Edition");
        // The middle cut already shows the difference.
        assert_eq!(
            cut_label("Model Alpha Two", 1, 12),
            truncate_middle("Model Alpha Two", 12, ELLIPSIS)
        );
    }

    /// Two models of one provider with the same name show their ids; the
    /// same name under another provider stays bare (the provider column
    /// tells them apart).
    #[test]
    fn shared_names_within_a_provider_carry_the_id() {
        let models = [
            model("openai-codex", "gpt-6-sol", "GPT-6 Sol"),
            model("openai-codex", "gpt-6-sol-wm", "GPT-6 Sol"),
            model("openai", "gpt-6-sol", "GPT-6 Sol"),
            model("anthropic", "claude-haiku-5-5", "Claude Haiku 5.5"),
        ];
        assert_eq!(
            row_labels(&models),
            vec![
                "GPT-6 Sol (gpt-6-sol)",
                "GPT-6 Sol (gpt-6-sol-wm)",
                "GPT-6 Sol",
                "Claude Haiku 5.5",
            ]
        );
    }
}
