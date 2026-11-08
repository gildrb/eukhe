use super::*;

fn strings(items: &[&str]) -> Vec<String> {
    items.iter().map(|item| (*item).to_owned()).collect()
}

/// The parse result with its usage error rendered as the printed text.
fn rendered<T>(parsed: Result<T, TinyUsage>) -> Result<T, String> {
    parsed.map_err(|usage| usage.to_string())
}

#[test]
fn say_arguments_parse() {
    assert_eq!(
        (
            rendered(parse_say(&strings(&[
                "hello", "there", "--out", "a.wav", "--voice", "bf_emma"
            ]))),
            rendered(parse_say(&strings(&["--voice", "am_puck", "hi"]))),
            rendered(parse_say(&strings(&["--out"]))),
            rendered(parse_say(&strings(&[]))),
        ),
        (
            Ok(SayArgs {
                text: "hello there".to_owned(),
                out: Some(PathBuf::from("a.wav")),
                voice: Some("bf_emma".to_owned()),
            }),
            Ok(SayArgs {
                text: "hi".to_owned(),
                out: None,
                voice: Some("am_puck".to_owned()),
            }),
            Err(format!(
                "Usage: {APP_NAME} say <text...> [--out <file.wav>] [--voice <id>]"
            )),
            Err(format!(
                "Usage: {APP_NAME} say <text...> [--out <file.wav>] [--voice <id>]"
            )),
        )
    );
}

#[test]
fn transcribe_arguments_parse() {
    let usage = format!("Usage: {APP_NAME} transcribe <file.wav> [--language <code>]");
    assert_eq!(
        (
            rendered(parse_transcribe(&strings(&[
                "clip.wav",
                "--language",
                "pt"
            ]))),
            rendered(parse_transcribe(&strings(&["clip.wav"]))),
            rendered(parse_transcribe(&strings(&["a.wav", "b.wav"]))),
            rendered(parse_transcribe(&strings(&["--language", "en"]))),
        ),
        (
            Ok(TranscribeArgs {
                file: PathBuf::from("clip.wav"),
                language: "pt".to_owned(),
            }),
            Ok(TranscribeArgs {
                file: PathBuf::from("clip.wav"),
                language: String::new(),
            }),
            Err(usage.clone()),
            Err(usage),
        )
    );
}

#[test]
fn the_first_player_on_the_path_plays() {
    let first = tempfile::tempdir().expect("tempdir");
    let second = tempfile::tempdir().expect("tempdir");
    std::fs::write(first.path().join("aplay"), "").expect("aplay");
    std::fs::write(second.path().join("paplay"), "").expect("paplay");
    let path = std::env::join_paths([first.path(), second.path()]).expect("path");
    let empty = std::env::join_paths([first.path().join("none")]).expect("path");
    assert_eq!(
        (
            find_player(Some(&path)),
            find_player(Some(&empty)),
            find_player(None)
        ),
        (Some(second.path().join("paplay")), None, None)
    );
}
