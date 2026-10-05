//! The browse page (`OptChat` spec §10): the whole memory as one HTML
//! file. It shows the current view, ROOT (every message), and each level of
//! the tree, every entry with its range, time span and size. It reads the
//! files without taking ownership; the view is the live owner's when one
//! answers, else the fold a new owner would compute.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::Path;

use super::chat::Chat;
use super::labeled;
use super::store::{LoadMode, Store};
use super::view::{line_text, NodeTexts, Part};

/// What the written page holds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BrowseSummary {
    pub messages: u64,
    pub nodes: u64,
    pub view_lines: u64,
    /// Whether the view came from a live owner.
    pub live_view: bool,
}

/// Write the memory in `dir` as one HTML page at `out`.
///
/// # Errors
///
/// Returns an error when the chat files cannot be read or the page cannot
/// be written.
pub async fn write_browse_page(dir: &Path, out: &Path) -> anyhow::Result<BrowseSummary> {
    let live = super::service::live_parts(dir).await;
    let (store, loaded) = Store::open(dir, LoadMode::ReadOnly)?;
    let mut problems = loaded.problems.clone();
    let chat = Chat::from_loaded(loaded, &mut problems);
    let parts: Vec<Part> = match &live {
        Some(parts) => parts.iter().map(|(l, i)| Part { l: *l, i: *i }).collect(),
        None => chat.view().parts().to_vec(),
    };
    let date_of = |id: u64| chat.message(id).map_or("", |meta| meta.date.as_str());
    let span = |part: Part| {
        let first = date_of(part.start());
        let last = date_of(
            part.end()
                .saturating_sub(1)
                .min(chat.total().saturating_sub(1)),
        );
        if first == last {
            first.to_string()
        } else {
            format!("{first} → {last}")
        }
    };

    let mut html = String::new();
    html.push_str(concat!(
        "<!doctype html><html><head><meta charset=\"utf-8\"><title>Chat memory</title><style>",
        "body{font:14px/1.45 ui-monospace,monospace;margin:24px;max-width:1100px}",
        "h1,h2{font-family:system-ui,sans-serif}table{border-collapse:collapse;width:100%}",
        "td,th{border-bottom:1px solid #ccc;padding:4px 8px;vertical-align:top;text-align:left}",
        "pre{white-space:pre-wrap;margin:0}details summary{cursor:pointer}.m{color:#666;white-space:nowrap}",
        "</style></head><body>"
    ));
    let _ = write!(
        html,
        "<h1>Chat memory</h1><p>{} messages · {} summaries · view: {} lines ({}) · {}</p>",
        chat.total(),
        chat.nodes().len(),
        parts.len(),
        if live.is_some() {
            "live"
        } else {
            "folded from disk"
        },
        escape(&dir.display().to_string())
    );
    if !problems.is_empty() {
        html.push_str("<h2>Problems</h2><ul>");
        for problem in &problems {
            let _ = write!(html, "<li>{}</li>", escape(problem));
        }
        html.push_str("</ul>");
    }

    html.push_str(
        "<h2>View</h2><table><tr><th>line</th><th>time span</th><th>bytes</th><th>text</th></tr>",
    );
    for part in &parts {
        let text = line_text(*part, chat.nodes());
        let _ = write!(
            html,
            "<tr><td class=m>{}+{}</td><td class=m>{}</td><td class=m>{}</td><td><pre>{}</pre></td></tr>",
            part.start(),
            part.count(),
            escape(&span(*part)),
            text.len(),
            escape(text)
        );
    }
    html.push_str("</table>");

    html.push_str(
        "<h2>ROOT</h2><table><tr><th>id</th><th>date</th><th>bytes</th><th>message</th></tr>",
    );
    for id in 0..chat.total() {
        let Some(meta) = chat.message(id) else {
            continue;
        };
        let record = store.read_message(meta)?;
        let whole = labeled(record.kind, &record.text);
        let first_line = whole.lines().next().unwrap_or("");
        let _ = write!(
            html,
            "<tr><td class=m>{id}</td><td class=m>{}</td><td class=m>{}</td><td><details><summary>{}</summary><pre>{}</pre></details></td></tr>",
            escape(&meta.date),
            meta.size,
            escape(&first_line.chars().take(160).collect::<String>()),
            escape(&whole)
        );
    }
    html.push_str("</table>");

    let mut levels: BTreeMap<u32, Vec<Part>> = BTreeMap::new();
    for (part, _) in chat.nodes().iter() {
        levels.entry(part.l).or_default().push(part);
    }
    for (level, mut level_parts) in levels {
        level_parts.sort_by_key(|part| part.i);
        let _ = write!(
            html,
            "<h2>Level {level} ({} messages per line)</h2><table><tr><th>line</th><th>time span</th><th>bytes</th><th>text</th></tr>",
            1u64 << level
        );
        for part in level_parts {
            let text = chat.nodes().node_text(part).unwrap_or("");
            let _ = write!(
                html,
                "<tr><td class=m>{}+{}</td><td class=m>{}</td><td class=m>{}</td><td><pre>{}</pre></td></tr>",
                part.start(),
                part.count(),
                escape(&span(part)),
                text.len(),
                escape(text)
            );
        }
        html.push_str("</table>");
    }
    html.push_str("</body></html>\n");
    if let Some(parent) = out.parent() {
        if !parent.as_os_str().is_empty() {
            std::fs::create_dir_all(parent)?;
        }
    }
    std::fs::write(out, html)?;
    Ok(BrowseSummary {
        messages: chat.total(),
        nodes: chat.nodes().len() as u64,
        view_lines: parts.len() as u64,
        live_view: live.is_some(),
    })
}

/// The chat as a reader sees it, without taking ownership.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReadView {
    /// The agent's rendering of the view.
    pub text: String,
    pub messages: u64,
    pub summaries: u64,
    pub view_lines: u64,
    pub view_bytes: u64,
    /// Messages whose view line is not summarized yet.
    pub unsummarized: u64,
    /// Whether a live owner answered (its view), or the view is the fold a
    /// new owner would compute from the files.
    pub live: bool,
}

/// Read the chat in `dir`: the live owner's view when one answers, else
/// the fold of the files. Never claims ownership.
///
/// # Errors
///
/// Returns an error when the chat files cannot be read.
pub async fn read_view(dir: &Path) -> anyhow::Result<ReadView> {
    let live = super::service::live_parts(dir).await;
    let (_store, loaded) = Store::open(dir, LoadMode::ReadOnly)?;
    let mut problems = loaded.problems.clone();
    let chat = Chat::from_loaded(loaded, &mut problems);
    let parts: Vec<Part> = match &live {
        Some(parts) => parts.iter().map(|(l, i)| Part { l: *l, i: *i }).collect(),
        None => chat.view().parts().to_vec(),
    };
    let mut text = String::from("<chat>\n");
    let mut view_bytes = 0;
    let mut first_unbuilt = chat.total();
    for part in &parts {
        let summary = line_text(*part, chat.nodes());
        if chat.nodes().node_text(*part).is_none() {
            first_unbuilt = first_unbuilt.min(part.start());
        }
        view_bytes += summary.len();
        let _ = writeln!(
            text,
            "{}+{}|{}",
            part.start(),
            part.count(),
            super::view::flatten(summary)
        );
    }
    text.push_str("</chat>");
    Ok(ReadView {
        text,
        messages: chat.total(),
        summaries: chat.nodes().len() as u64,
        view_lines: parts.len() as u64,
        view_bytes: view_bytes as u64,
        unsummarized: chat.total() - first_unbuilt,
        live: live.is_some(),
    })
}

/// HTML text escaping.
fn escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for character in text.chars() {
        match character {
            '&' => out.push_str("&amp;"),
            '<' => out.push_str("&lt;"),
            '>' => out.push_str("&gt;"),
            '"' => out.push_str("&quot;"),
            '\'' => out.push_str("&#39;"),
            other => out.push(other),
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory::compactor::tests::Scripted;
    use crate::memory::{Kind, Memory};

    /// A reader gets the live owner's view when one answers, else the fold
    /// of the files; the page holds the view, ROOT and each tree level.
    #[tokio::test]
    async fn readers_see_the_live_view_or_the_fold() {
        let dir = tempfile::tempdir().unwrap();
        let pages = tempfile::tempdir().unwrap();
        let memory = Memory::open(dir.path(), Scripted::with(Vec::new()))
            .await
            .unwrap();
        memory.append(Kind::User, "hello <you>").await.unwrap();
        memory.append(Kind::Talk, "hi").await.unwrap();
        let rendered = memory.settled_render().await.unwrap();
        let live = read_view(dir.path()).await.unwrap();
        assert_eq!(
            live,
            ReadView {
                text: rendered.text,
                messages: 2,
                summaries: 3,
                view_lines: 2,
                view_bytes: ("user: hello <you>".len() + "talk: hi".len()) as u64,
                unsummarized: 0,
                live: true,
            }
        );
        drop(memory);
        let folded = read_view(dir.path()).await.unwrap();
        assert_eq!(
            folded,
            ReadView {
                live: false,
                ..live
            }
        );
        let out = pages.path().join("memory.html");
        let summary = write_browse_page(dir.path(), &out).await.unwrap();
        assert_eq!(
            summary,
            BrowseSummary {
                messages: 2,
                nodes: 3,
                view_lines: 2,
                live_view: false,
            }
        );
        let html = std::fs::read_to_string(&out).unwrap();
        for expected in [
            "<h2>View</h2>",
            "<h2>ROOT</h2>",
            "<h2>Level 0 (1 messages per line)</h2>",
            "<h2>Level 1 (2 messages per line)</h2>",
            "<td class=m>0+2</td>",
            "<pre>user: hello &lt;you&gt;\ntalk: hi</pre>",
        ] {
            assert!(html.contains(expected), "{expected} in {html}");
        }
    }
}
