//! The scrubber against real code and data. Three sets:
//!
//! - [`UNTOUCHED`]: code and data no detector may change (CSS
//!   pseudo-elements, `::` paths, versions, hashes, UUIDs, colors,
//!   timestamps, long literals, base64, ids, ports, imports, dotted
//!   names, `@` that is no email). A detector that changes one of them
//!   corrupts what the model reads and, through an edit, the file.
//! - [`PERSONAL`]: personal values, each scrubbed to a reversible token
//!   and restored byte for byte.
//! - [`secrets`]: credentials, scrubbed one way.
//!
//! The secrets are fakes made for this file (random characters in each
//! vendor's shape; IBANs and card numbers of the published examples or
//! checksum-valid made-up ones). Each one is written split at its vendor
//! prefix and joined at run time, so no secret scanner reads this source
//! as a leaked credential.

use super::*;

/// Code and data that pass the scrubber unchanged, one snippet each.
pub(super) const UNTOUCHED: &[&str] = &[
    // CSS
    "a::before { content: \"\\2192\"; }",
    ".btn::after { content: ''; display: block; }",
    "p::first-line, li::marker { color: #ffcc00; }",
    "input::placeholder { color: #abc; }",
    "a::b",
    "::selection { background: #dead00; }",
    ".e2e::before, .a1::after, .c0::backdrop { inset: 0; }",
    ":root { --accent: #1e90ff; --muted: #FFF; }",
    "@media (min-width: 768px) { .grid { gap: 12px; } }",
    "background: url(\"data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR42mNkYPhfDwAChwGA60e6kgAAAABJRU5ErkJggg==\");",
    "color: rgba(0, 0, 0, 0.5); transition: all 0.3s;",
    ".sk-folding-cube-animation-delay { animation-delay: 0.3s; }",
    // Rust, C++, PHP, Ruby
    "use std::fmt::Display;",
    "impl std::fmt::Debug for Foo {}",
    "Foo::bar(baz)",
    "let v: Vec<u8> = Vec::with_capacity(1024);",
    "std::vector<int>::size_type n = 0;",
    "dead::beef",
    "cafe::babe::face()",
    "a::b::c",
    "<T as Iterator>::Item",
    "let x = 0xdeadbeef; let y = 0xFFFF_FFFF;",
    "ab12::cd34::ef56",
    "fd::dup2(a, b)",
    "$this->x = self::$cache; Foo::class;",
    "Foo::Bar::Baz.new",
    "std::cout << \"ab::cd\" << std::endl;",
    "u32::MAX + i64::from(1)",
    "crate::a1::b2::c3",
    // Python
    "evens = xs[::2]; odds = xs[1::2]; rev = xs[::-1]",
    "grid[0:10, 1:3]",
    "@dataclass\nclass Point:",
    "@app.route(\"/users/<int:id>\")",
    "result = a @ b.T",
    // Versions
    "version = \"1.2.3.4\"",
    "\"version\": \"4.17.21\"",
    "v0.10.62",
    "__version__ = '2.0.0.1'",
    "<version>1.0.0.0</version>",
    "Version: 10.0.0.1",
    "numpy==1.26.4 django>=4.2.1.0 click~=8.1.7.2",
    "User-Agent: Mozilla/5.0 Chrome/120.0.0.0 Safari/537.36",
    "tag v1.2.3.4-rc1, release 2.4.1.3-beta",
    "[assembly: AssemblyVersion(\"1.2.3.4\")]",
    "go 1.21.0",
    // Git
    "commit 3f2a9c1d8e7b6a5f4e3d2c1b0a9f8e7d6c5b4a39",
    "Merge: 1a2b3c4 5d6e7f8",
    "git checkout a1b2c3d && git cherry-pick 4e5f6a7",
    // UUIDs
    "id: \"550e8400-e29b-41d4-a716-446655440000\"",
    "019a0000-0000-7000-8000-000000000001",
    // Colors
    "fill=\"#ffcc00\" stroke=\"#FFF\"",
    // Times
    "2026-11-01T12:34:56.789Z",
    "[2026-11-01 12:34:56,789] INFO started",
    "created_at: 1730419200000",
    "elapsed 00:01:23.456",
    "2026-11-01T12:00:00+0000 and +05:30",
    "Date.UTC(2024, 0, 1)",
    "12:34:56",
    // Long literals
    "const MAX: u64 = 18446744073709551615;",
    "Number.MAX_SAFE_INTEGER === 9007199254740991",
    "let n = 1234567890123;",
    "1_000_000_000_000",
    "3.141592653589793",
    "x = 1.4526018159083012",
    // Base64, base32, digests
    "assert_eq!(encode(b\"foobar\"), \"Zm9vYmFy\");",
    "\"SGVsbG8sIFdvcmxkIQ==\"",
    "QG27EKNQC5TKFMCG",
    "md5: CB32B1C9311E88B86491FCE424F6961B",
    "sha256:9f86d081884c7d659a2feaa0c55ad015a3bf4f1b2b0b822cd15d6c15b0f00a08",
    // JSON and ids
    "{\"id\": 1234567890123456789, \"user_id\": \"u_8f3a2b\", \"order\": \"ORD-2024-000123\"}",
    "{\"zip\": \"94103-1234\", \"ext\": \"x123\"}",
    "{\"count\": 12, \"next\": \"/api/items?page=2&per_page=100\"}",
    // Numbers that look like phones
    "const PORT = 8080; const TIMEOUT_MS = 30000;",
    "x = a +1.5e10;",
    "count += 12345678;",
    "printf(\"%+d\\n\", 12345678);",
    "offset = -1234567890;",
    "range(1000000, 9999999)",
    "ISBN 978-0-13-468599-1",
    "bump 20241101-120000-0001",
    // Imports and paths
    "import { foo } from \"../lib/utils/index.js\";",
    "use crate::privacy::Scrubber;",
    "#include <boost/asio.hpp>",
    "from django.db import models",
    "/usr/local/lib/python3.12/site-packages/numpy/__init__.py",
    "C:\\Program Files\\Git\\bin\\git.exe",
    // Dotted names and URLs
    "foo.bar.baz",
    "window.location.href = \"/login\";",
    "self.config.api.base_url",
    "package com.example.app;",
    "os.path.join(root, \"a.txt\")",
    "fetch(\"https://api.example.com/v1/users\")",
    // `@` that is no email
    "<img src=\"icon@2x.png\" srcset=\"logo@3x.webp 3x\">",
    "\"@types/node\": \"^20.11.5\"",
    "git clone git@github.com:org/repo.git",
    "user@host:~$ ls",
    "\"repository\": \"git@gitlab.com:group/project.git\"",
    // `Bearer` that is no credential
    "Use Bearer authentication for every request.",
    "headers[\"Authorization\"] = f\"Bearer {token}\"",
    "Authorization: Bearer ${process.env.TOKEN}",
    "\"Bearer \" + accessToken",
    "Bearer authentication_scheme_description_text",
    // Addresses that identify no one
    "listen 0.0.0.0:8080; proxy_pass http://127.0.0.1:3000;",
    "netmask 255.255.255.0",
    "bind [::1]:9000",
    "connect 0:0:0:0:0:0:0:1 now",
    "bind 0:0:0:0:0:0:0:0 now",
    "connect 0:0:0::1 now",
    "connect ::ffff:127.0.0.1 now",
    "ab:cd:ef:01:23:45",
    // Hashline reads
    "[foo.css#1A2B]\n12:a::before {",
    // Uppercase identifiers
    "const SHA256_DIGEST_LENGTH = 32; ES256 HS512",
    // Published test card numbers
    "stripe test card 4242 4242 4242 4242, exp 12/34",
    "4111111111111111",
];

/// Personal values in context: the text, and the value in it that must
/// become a reversible token.
pub(super) const PERSONAL: &[(&str, &str)] = &[
    (
        "\"author\": \"A. Writer <writer@example.org>\"",
        "writer@example.org",
    ),
    ("ssh deploy@203.0.113.7", "203.0.113.7"),
    ("server 10.0.0.7 refused", "10.0.0.7"),
    (
        "upstream [2001:db8::8a2e:370:7334]:443",
        "2001:db8::8a2e:370:7334",
    ),
    ("call +49 172 4510 5432 today", "+49 172 4510 5432"),
    ("ssn 078-05-1120 on file", "078-05-1120"),
    ("ping 192.168.1.20", "192.168.1.20"),
    ("office 415-555-0132", "415-555-0132"),
    ("mapped ::ffff:192.0.2.128 here", "::ffff:192.0.2.128"),
];

/// Credentials in context: the text, and the secret in it that must
/// never reach the provider.
pub(super) fn secrets() -> Vec<(String, String)> {
    // (text before, the secret's prefix, the rest of the secret, text after)
    const PARTS: &[(&str, &str, &str, &str)] = &[
        (
            "OPENAI_API_KEY=",
            "sk-",
            "proj-odJFCrnl2edlBDdz1C5Jau2RJtBRnlWmTSHf6pWkLUyifDLk",
            "",
        ),
        (
            "key: ",
            "sk-",
            "ant-api03-DmWJ6UuVTAIjvFu7WICPhDeOZIiBOB-Y6sHrFH2Z",
            "",
        ),
        ("token ", "ghp", "_xoiGFfWd3hjOkYRBMeyyMDHqJ38aRUhR4IWr", ""),
        (
            "GITHUB_TOKEN=",
            "github",
            "_pat_XPvhsBkDa9U4UqGWlG6g3O_t1OGMmjxWkI9X7H6aMuFbh7x41Ztpdp4K8ffUF0eWIXiiQE8JkqH3MB9n7I",
            "",
        ),
        ("aws_access_key_id = ", "AKIA", "MTZX272HPOEVB9OO", ""),
        (
            "\"apiKey\": \"",
            "AIza",
            "ajhDieQjEJ_Bq8F80ymm3T207gmhZRnFyy5",
            "\"",
        ),
        ("CI_TOKEN=", "glpat", "-iBlrDp37eCZ32JgdPI1a", ""),
        (
            "SLACK_BOT_TOKEN=",
            "xoxb",
            "-132677360260-yq7YYDsBS9UYJQTFjmsn9dLV",
            "",
        ),
        (
            "//registry.npmjs.org/:_authToken=",
            "npm",
            "_IdVuddLEG62Hkd9Gf2leMeR3pzh84KpLMcNf",
            "",
        ),
        (
            "DO_TOKEN=",
            "dop",
            "_v1_da86a78c49ea20e32684b27b95e909348334896a68f812d810a485ed03241b4d",
            "",
        ),
        (
            "X-Shopify-Access-Token: ",
            "shpat",
            "_419b1b673bd4755d05ad7853c1f76eb9",
            "",
        ),
        (
            "Authorization: Bearer ",
            "DCdyZQJiJSZQ",
            "doHwHen3SO3oXyGf3azU3iQOpM-N",
            "",
        ),
        (
            concat!("-----BEGIN OPENSSH PRIVATE", " KEY-----\n"),
            "b3BlbnNzaC1rZXkt",
            "djEAAAAABG5vbmUAAAAEbm9uZQ",
            concat!("\n-----END OPENSSH PRIVATE", " KEY-----"),
        ),
        ("pay with ", "4526 0181 ", "5908 3012", " today"),
        ("card=", "51661318", "60913906", ";"),
        ("amex ", "3799 603082 ", "46287", ""),
        ("IBAN ", "DE89 3704 0044 ", "0532 0130 00", ""),
        ("iban: ", "GB82WEST", "12345698765432", "."),
    ];
    PARTS
        .iter()
        .map(|(before, prefix, rest, after)| {
            (
                format!("{before}{prefix}{rest}{after}"),
                format!("{prefix}{rest}"),
            )
        })
        .collect()
}

/// No detector changes code or data: the corpus passes byte for byte.
#[test]
fn code_and_data_pass_unchanged() {
    let scrubber = Scrubber::new(&["Ada Lovelace".to_owned()], TokenMap::default());
    let changed: Vec<(&str, String)> = UNTOUCHED
        .iter()
        .filter_map(|text| {
            let out = scrubber.scrub_str(text);
            (out != *text).then_some((*text, out))
        })
        .collect();
    assert_eq!(changed, Vec::<(&str, String)>::new());
}

/// Every personal value leaves as a token and comes back as itself.
#[test]
fn personal_values_become_tokens_that_come_back() {
    let scrubber = Scrubber::new(&[], TokenMap::default());
    for (text, value) in PERSONAL {
        let out = scrubber.scrub_str(text);
        assert!(!out.contains(value), "{value} survived: {out}");
        assert_eq!(scrubber.tokens().restore(&out), *text);
    }
}

/// Restoring the scrubbed corpus gives the corpus back.
#[test]
fn the_corpus_round_trips() {
    let scrubber = Scrubber::new(&["Ada Lovelace".to_owned()], TokenMap::default());
    for text in UNTOUCHED
        .iter()
        .copied()
        .chain(PERSONAL.iter().map(|(text, _)| *text))
    {
        assert_eq!(scrubber.tokens().restore(&scrubber.scrub_str(text)), text);
    }
}

/// The addresses of `spans` (start, end) that the scan reaches: none
/// inside another.
fn reached(text: &str, spans: impl Iterator<Item = (usize, usize)>) -> Vec<&str> {
    let mut done = 0;
    let mut found = Vec::new();
    for (at, end) in spans {
        if at >= done {
            done = end;
            found.push(&text[at..end]);
        }
    }
    found
}

/// The addresses the core answers at every position of `text` where an
/// address could start after a boundary (no word char before it), asked
/// directly, one candidate per position: no gate.
fn core_addresses(text: &str) -> Vec<&str> {
    let mut starts = Vec::new();
    let mut candidates = Vec::new();
    let mut after_word = false;
    for (at, c) in text.char_indices() {
        if !after_word {
            starts.push(at);
            candidates.push(detect::candidate(text, at));
        }
        after_word = detect::is_word(c);
    }
    let ends = eukhe_bend::rules::privacy::ip_ends(&candidates);
    reached(
        text,
        starts.into_iter().zip(ends).filter_map(|(at, chars)| {
            chars.map(|chars| (at, at + detect::chars_to_bytes(&text[at..], chars)))
        }),
    )
}

/// The addresses the scrubber's one call per text finds (`Ips::of`).
fn scrubber_addresses(text: &str) -> Vec<&str> {
    let ips = detect::Ips::of(text);
    reached(
        text,
        text.char_indices()
            .filter_map(|(at, _)| ips.at(at).map(|end| (at, end))),
    )
}

/// Bridge (the core's IP grammar, laws/privacy/ip.bend): every position
/// of every snippet, asked of the core directly, holds no address in code
/// and data, and exactly the personal values that are IP addresses
/// (`std::net::IpAddr` reads them); the scrubber's gated call finds the
/// same addresses.
#[test]
fn the_core_finds_exactly_the_personal_addresses() {
    let secrets = secrets();
    let texts: Vec<(&str, Vec<&str>)> = UNTOUCHED
        .iter()
        .map(|text| (*text, Vec::new()))
        .chain(PERSONAL.iter().map(|(text, value)| {
            let ips = if value.parse::<std::net::IpAddr>().is_ok() {
                vec![*value]
            } else {
                Vec::new()
            };
            (*text, ips)
        }))
        .chain(secrets.iter().map(|(text, _)| (text.as_str(), Vec::new())))
        .collect();
    let seen: Vec<(&str, Vec<&str>, Vec<&str>)> = texts
        .iter()
        .map(|(text, _)| (*text, core_addresses(text), scrubber_addresses(text)))
        .collect();
    let expected: Vec<(&str, Vec<&str>, Vec<&str>)> = texts
        .iter()
        .map(|(text, ips)| (*text, ips.clone(), ips.clone()))
        .collect();
    assert_eq!(seen, expected);
}

/// Regression (a remote session corrupted a stylesheet): the model read
/// `a::before` as `aIP_4d040core` and wrote that back. Now the model reads
/// the stylesheet as it is (a personal value in it as a token), and the
/// file it writes back from what it read is the file, byte for byte.
#[test]
fn a_stylesheet_read_and_written_back_through_the_scrub_is_unchanged() {
    let file = "/* staging origin 203.0.113.7 */\n.card::before { content: \"\"; }\n.card::after,\nli::marker { color: #ffcc00; }\n";
    let scrubber = Scrubber::new(&[], TokenMap::default());
    let read = scrubber.scrub_str(file);
    assert_eq!(
        read,
        "/* staging origin IP_1 */\n.card::before { content: \"\"; }\n.card::after,\nli::marker { color: #ffcc00; }\n"
    );
    let message: AssistantMessage = serde_json::from_value(serde_json::json!({
        "role": "assistant",
        "content": [
            { "type": "toolCall", "id": "t1", "name": "write",
              "arguments": { "path": "style.css", "content": read } },
        ],
        "api": "anthropic", "provider": "anthropic", "model": "m", "timestamp": 0,
        "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                   "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
        "stopReason": "toolUse",
    }))
    .expect("the wire shape");
    let written = scrubber.tokens().restore_message(message);
    let AssistantContentBlock::ToolCall(call) = &written.content[0] else {
        panic!("a tool call: {written:?}");
    };
    assert_eq!(
        call.arguments
            .get("content")
            .and_then(|content| content.as_str()),
        Some(file)
    );
}
