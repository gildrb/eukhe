use super::*;

fn labels(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

#[test]
fn the_title_request_is_the_omp_recipe() {
    assert_eq!(
        title_request("  fix the flaky login test \n"),
        ChatRequest {
            messages: vec![
                ChatMessage {
                    role: ChatRole::System,
                    content: TITLE_SYSTEM_PROMPT.to_owned(),
                },
                ChatMessage {
                    role: ChatRole::User,
                    content: "fix the flaky login test".to_owned(),
                },
            ],
            prefill: "<title>".to_owned(),
            stop: vec!["</title>".to_owned()],
            max_tokens: 24,
        }
    );
}

#[test]
fn the_title_request_cuts_a_long_message() {
    let long = "é".repeat(TITLE_INPUT_CHARS + 10);
    let request = title_request(&long);
    assert_eq!(request.messages[1].content, "é".repeat(TITLE_INPUT_CHARS));
}

#[test]
fn titles_normalize() {
    let cases = [
        ("Fix flaky login test", Some("Fix flaky login test")),
        (
            "  \"debug the parser.\"\nsecond line",
            Some("Debug the parser"),
        ),
        (
            "<title>Rust lifetimes explained</title> tail",
            Some("Rust lifetimes explained"),
        ),
        (
            "Title: Deploy pipeline setup",
            Some("Deploy pipeline setup"),
        ),
        (
            "MIGRATE THE DATABASE SCHEMA",
            Some("Migrate the database schema"),
        ),
        ("API key rotation", Some("API key rotation")),
        (
            "one two three four five six seven eight nine ten eleven",
            Some("One two three four five six seven eight nine ten"),
        ),
        ("**Bold markdown title**", Some("Bold markdown title")),
        ("\n\n  ", None),
        ("\"...\"", None),
    ];
    let normalized: Vec<(&str, Option<String>)> = cases
        .iter()
        .map(|(raw, _)| (*raw, normalize_title(raw)))
        .collect();
    let expected: Vec<(&str, Option<String>)> = cases
        .iter()
        .map(|(raw, title)| (*raw, title.map(str::to_owned)))
        .collect();
    assert_eq!(normalized, expected);
}

#[test]
fn the_judge_request_lists_the_labels() {
    assert_eq!(
        judge_request("State:\n{}\nQuestion", &labels(&["Yes", "No"])),
        ChatRequest {
            messages: vec![
                ChatMessage {
                    role: ChatRole::System,
                    content: format!("{JUDGE_SYSTEM_PROMPT} The labels are: Yes, No."),
                },
                ChatMessage {
                    role: ChatRole::User,
                    content: "State:\n{}\nQuestion".to_owned(),
                },
            ],
            prefill: "Answer:".to_owned(),
            stop: vec!["\n".to_owned()],
            max_tokens: JUDGE_MAX_TOKENS,
        }
    );
}

#[test]
fn labels_parse() {
    let set = labels(&["A", "B", "a"]);
    let cases = [
        ("A", Some(0)),
        ("  B. because", Some(1)),
        ("a", Some(2)),
        ("\"B\"", Some(1)),
        ("C", None),
        ("", None),
        ("Answer: A.", Some(0)),
        ("answer", None),
    ];
    let parsed: Vec<(&str, Option<usize>)> = cases
        .iter()
        .map(|(reply, _)| (*reply, parse_label(reply, &set)))
        .collect();
    assert_eq!(parsed, cases.to_vec());
    let yes_no = labels(&["Yes", "No"]);
    assert_eq!(
        (parse_label("yes", &yes_no), parse_label("NO!", &yes_no)),
        (Some(0), Some(1))
    );
}

#[test]
fn the_translate_request_names_the_language() {
    assert_eq!(
        translate_request("fr", "good morning"),
        ChatRequest {
            messages: vec![
                ChatMessage {
                    role: ChatRole::System,
                    content: "You are a translator. Output only the translation.".to_owned(),
                },
                ChatMessage {
                    role: ChatRole::User,
                    content: "Translate this text to French:\ngood morning".to_owned(),
                },
            ],
            prefill: String::new(),
            stop: Vec::new(),
            max_tokens: 88,
        }
    );
    assert_eq!(
        (language_name("Klingon"), translation_text("  bonjour \n")),
        ("Klingon", "bonjour".to_owned())
    );
}

#[test]
fn remote_replies_read_like_worker_replies() {
    let title = title_request("x");
    let translate = translate_request("de", "x");
    assert_eq!(
        (
            remote_reply_text(&title, "<title>Fix the build</title>\nextra"),
            remote_reply_text(&title, "Fix the build"),
            remote_reply_text(&translate, " Guten Morgen "),
        ),
        (
            "Fix the build".to_owned(),
            "Fix the build".to_owned(),
            "Guten Morgen ".to_owned(),
        )
    );
}
