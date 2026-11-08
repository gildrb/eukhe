use super::corpus_tests::secrets;
use super::*;

fn scrubber() -> Scrubber {
    Scrubber::new(&["Ada Lovelace".to_owned()])
}

#[test]
fn loopback_endpoints_are_local_and_others_are_not() {
    assert!(is_local("http://127.0.0.1:18020/v1"));
    assert!(is_local("http://localhost:8080"));
    assert!(is_local("http://[::1]:9000"));
    assert!(!is_local("https://api.anthropic.com"));
    assert!(!is_local("https://openrouter.ai/api/v1"));
}

#[test]
fn emails_get_a_stable_token() {
    let email = scrubber().scrub_str("write to dev@example.net about the invoice");
    assert_eq!(email, "write to EMAIL_1 about the invoice");
    // The same input twice: the same token.
    assert_eq!(
        scrubber().scrub_str("dev@example.net"),
        scrubber().scrub_str("dev@example.net")
    );
    // A different input: a different token.
    assert_ne!(
        scrubber().scrub_str("dev@example.net"),
        scrubber().scrub_str("ops@example.net")
    );
}

#[test]
fn terms_scrub_names_and_only_at_boundaries() {
    let out = scrubber().scrub_str("ask Ada Lovelace, not Adalbert; ADA LOVELACE too");
    assert_eq!(out, "ask PERSON_1, not Adalbert; PERSON_2 too");
    // A term inside a longer word does not match.
    let inside = Scrubber::new(&["Ada".to_owned()]).scrub_str("Adalbert stays");
    assert_eq!(inside, "Adalbert stays");
}

#[test]
fn every_value_takes_the_token_of_its_class() {
    let out = Scrubber::new(&[]).scrub_str(
        "mail dev@example.net, call +49 172 4510 5432, ssn 078-05-1120, host 10.0.0.7 or 2001:db8::1",
    );
    assert_eq!(
        out,
        "mail EMAIL_1, call PHONE_1, ssn ID_1, host IP_1 or IP_2"
    );
}

#[test]
fn credentials_become_one_way_tokens() {
    let secrets = secrets();
    for (text, secret) in &secrets {
        let out = scrubber().scrub_str(text);
        assert!(!out.contains(secret), "{secret} survived: {out}");
        assert!(
            ["KEY_", "CARD_", "IBAN_"]
                .iter()
                .any(|class| out.contains(class)),
            "{out}"
        );
        assert!(!restore(&out).contains(secret), "{secret} came back");
    }
    // A bearer credential keeps its scheme visible.
    let bearer = scrubber().scrub_str(&secrets[11].0);
    assert!(bearer.starts_with("Authorization: Bearer KEY_"), "{bearer}");
}

#[test]
fn ips_are_scrubbed_paths_and_domains_pass() {
    let out = scrubber().scrub_str(
        "the log at /home/lovelace/Repos/eukhe/target and /var/log/syslog says 10.0.0.7 refused https://api.anthropic.com/v1",
    );
    assert_eq!(
        out,
        "the log at /home/lovelace/Repos/eukhe/target and /var/log/syslog says IP_1 refused https://api.anthropic.com/v1"
    );
    // Your own domain is a term, not a shape.
    let own = Scrubber::new(&["example.dev".to_owned()]);
    assert_eq!(
        own.scrub_str("deploy example.dev now"),
        "deploy PERSON_1 now"
    );
}

#[test]
fn phone_numbers_are_scrubbed_but_dates_survive() {
    let out = scrubber().scrub_str("call +49 172 4510 5432 or 212-451-0543 on 2026-10-27");
    assert_eq!(out, "call PHONE_1 or PHONE_2 on 2026-10-27");
}

/// Restoring a scrubbed text gives the text back, byte for byte, for
/// every reversible class, including a literal that reads as a token:
/// it gets a token of its own, so no token maps back to two values.
#[test]
fn restore_inverts_the_scrub() {
    let scrubber = scrubber();
    // `IP_1` now names 10.0.0.7.
    assert_eq!(scrubber.scrub_str("10.0.0.7"), "IP_1");
    let text = "Ada Lovelace (dev@example.net, +49 172 4510 5432) set IP_1 = \"10.0.0.7\"; ID_9 and PERSON_1x stay";
    let model_view = scrubber.scrub_str(text);
    assert_eq!(
        model_view,
        "PERSON_1 (EMAIL_1, PHONE_1) set IP_2 = \"IP_1\"; ID_1 and PERSON_1x stay"
    );
    assert_eq!(restore(&model_view), text);
}

/// Restoring random mixes of values, literals that read as tokens and
/// code gives each mix back.
#[test]
fn restore_inverts_the_scrub_on_random_text() {
    const PARTS: &[&str] = &[
        "IP_1",
        "PERSON_2",
        "EMAIL_",
        "ID_07",
        "_",
        "::",
        "a",
        "1",
        ".",
        "0.",
        "10.0.0.7",
        "+49 172 4510 5432",
        " ",
        "\n",
        "@",
        "dev@example.net",
        "x.com",
        "2001:db8::1",
        "-",
        "Ada Lovelace",
        "é",
        "→",
        "a::before",
        "IP_",
        "9",
        "PHONE_3",
        "078-05-1120",
        "\"",
    ];
    let scrubber = scrubber();
    let mut state: u64 = 0x5eed;
    for _ in 0..2000 {
        let mut text = String::new();
        for _ in 0..12 {
            // A 64-bit LCG (Knuth's MMIX constants): deterministic picks.
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let pick = usize::try_from(state >> 33).unwrap_or(0) % PARTS.len();
            text.push_str(PARTS[pick]);
        }
        assert_eq!(restore(&scrubber.scrub_str(&text)), text, "{text:?}");
    }
}

/// The model's answer comes back with its tokens restored: text,
/// thinking and every string of its tool calls' arguments.
#[test]
fn the_answer_is_restored_whole() {
    let scrubbed = scrubber().scrub_str("write to Ada Lovelace at dev@example.net from 10.0.0.7");
    let message: AssistantMessage = serde_json::from_value(serde_json::json!({
        "role": "assistant",
        "content": [
            { "type": "thinking", "thinking": scrubbed },
            { "type": "text", "text": scrubbed },
            { "type": "toolCall", "id": "t1", "name": "bash",
              "arguments": { "script": scrubbed, "env": [{ "to": "EMAIL_1" }] } },
        ],
        "api": "anthropic", "provider": "anthropic", "model": "m", "timestamp": 0,
        "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                   "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
        "stopReason": "toolUse",
    }))
    .expect("the wire shape");
    let restored = serde_json::to_value(restore_message(message)).expect("serializes");
    let original = "write to Ada Lovelace at dev@example.net from 10.0.0.7";
    assert_eq!(
        restored["content"],
        serde_json::json!([
            { "type": "thinking", "thinking": original },
            { "type": "text", "text": original },
            { "type": "toolCall", "id": "t1", "name": "bash",
              "arguments": { "script": original, "env": [{ "to": "dev@example.net" }] } },
        ])
    );
}

#[test]
fn messages_of_every_role_are_scrubbed() {
    let (secret_text, secret) = secrets().swap_remove(2);
    let messages: Vec<Message> = serde_json::from_value(serde_json::json!([
        { "role": "system", "content": "workspace /home/dev/work", "timestamp": 0 },
        { "role": "user", "content": secret_text, "timestamp": 0 },
        { "role": "assistant", "content": [
            { "type": "toolCall", "id": "t1", "name": "bash",
              "arguments": { "script": "cat /home/dev/.ssh/id_ed25519", "hosts": ["10.0.0.7"] } },
        ],
          "api": "anthropic", "provider": "anthropic", "model": "m", "timestamp": 0,
          "usage": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "totalTokens": 0,
                     "cost": { "input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0, "total": 0 } },
          "stopReason": "stop" },
        { "role": "toolResult", "toolCallId": "t1", "toolName": "bash", "isError": false,
          "content": [ { "type": "text", "text": " mailed ops@example.org the file" } ],
          "timestamp": 0 },
    ]))
    .expect("the wire shapes");
    let scrubbed = format!("{:?}", scrubber().scrub_messages(messages));
    assert!(!scrubbed.contains(&secret));
    assert!(!scrubbed.contains("ops@example.org"));
    assert!(!scrubbed.contains("10.0.0.7"));
    assert!(scrubbed.contains("KEY_"));
    assert!(scrubbed.contains("EMAIL_1"));
    assert!(scrubbed.contains("IP_1"));
    // A path in a tool call argument passes as it is.
    assert!(scrubbed.contains("/home/dev/.ssh/id_ed25519"));
}

/// A corpus of identifying text; scrubbing must leave none of the
/// originals (for names, in any case).
#[test]
fn no_original_survives_anywhere() {
    let secrets = secrets();
    let text = format!(
        "Ada Lovelace, ada lovelace, ADA LOVELACE; dev@example.net, dev+tag@example.net; {}, {}; +49 172 4510 5432; 10.0.0.7, 2001:db8::1; {}",
        secrets[0].1, secrets[2].1, secrets[13].1
    );
    let out = scrubber().scrub_str(&text);
    let lowered = out.to_ascii_lowercase();
    for original in [
        "ada lovelace",
        "dev@example.net",
        "dev+tag@example.net",
        &secrets[0].1.to_ascii_lowercase(),
        &secrets[2].1.to_ascii_lowercase(),
        "172 4510 5432",
        "10.0.0.7",
        "2001:db8::1",
        "4526",
    ] {
        assert!(
            !lowered.contains(original),
            "{original} survived scrubbing: {out}"
        );
    }
}

/// What a scrubbed request still tells a provider: the token classes,
/// and everything a pattern cannot see.
#[test]
fn what_still_leaks_is_visible() {
    let scrubber = Scrubber::new(&[]);
    let out = scrubber.scrub_str("my sister Mia and my repo porthmeus at C:\\Users\\dev");
    // Not in the term list, no pattern shape: both travel as-is. This
    // test documents the boundary, it does not assert a property.
    assert!(out.contains("Mia"));
    assert!(out.contains("porthmeus"));
}
