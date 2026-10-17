//! Scripts calling the conversation's tools: the result layout, how nested
//! results reach the script, discovery globals, the store, `models.*`, source
//! options, and the deadline.

use std::sync::{Arc, Mutex};

use eukhe_ai::providers::faux::FauxResponseStep;
use eukhe_chord::json::{from_json, JsonValue};
use serde_json::json;

use super::{options, run_script, sandbox, setup, setup_with, text, Setup};
use crate::codemode::{
    ClassifierDefault, ClassifierResolver, CodemodeCallStatus, CodemodeModels, CodemodeToolDetails,
};
use crate::harness::tests::chat_support::{all_entries, open_chat};
use crate::harness::tests::support::context;
use crate::harness::tool::tests::nested_support::{call_with, lock};
use crate::harness::tool::tests::support::{done, results, submit_and_wait};
use crate::storage::MemoryStorage;
use crate::types::SubmissionStatus;

fn details(message: &eukhe_types::pi_ai::ToolResultMessage) -> CodemodeToolDetails {
    let details = eukhe_chord::json::to_json(message.details.as_ref().expect("details")).unwrap();
    from_json(&details).unwrap()
}

/// `(id, name, args, status, error)` of each row.
fn rows(
    details: &CodemodeToolDetails,
) -> Vec<(u64, String, String, CodemodeCallStatus, Option<String>)> {
    details
        .calls
        .iter()
        .map(|row| {
            (
                row.id,
                row.name.clone(),
                row.args.clone(),
                row.status,
                row.error.clone(),
            )
        })
        .collect()
}

/// The script's returned value: the last line of the result's text.
fn returned(message: &eukhe_types::pi_ai::ToolResultMessage) -> JsonValue {
    let text = text(message);
    JsonValue::parse(text.lines().last().expect("a line"))
        .unwrap_or_else(|_| panic!("the returned JSON in {text}"))
}

#[tokio::test]
async fn calls_tools_as_nested_calls_and_lays_out_text_console_and_value() {
    let setup = setup();
    let message = run_script(
        &setup,
        r#"const a = await tools.echo({ text: "hi" });
console.log("log", 1);
text(a);
return { n: 2 };"#,
    )
    .await;
    assert!(!message.is_error);
    assert_eq!(
        text(&message),
        "Script completed\nWall time <t> seconds\nOutput:\n==> text 1/2 <==\necho hi\n==> text 2/2 <==\n{\"n\":2}\n<console_output>\nlog 1\n</console_output>"
    );
    assert_eq!(
        rows(&details(&message)),
        vec![(
            1,
            "echo".to_owned(),
            r#"{"text":"hi"}"#.to_owned(),
            CodemodeCallStatus::Ok,
            None
        )]
    );
    assert_eq!(setup.runs.all(), vec![r#"echo:{"text":"hi"}"#.to_owned()]);
}

#[tokio::test]
async fn a_schema_tool_resolves_with_its_error_value_and_a_failed_text_tool_rejects() {
    let setup = setup();
    let message = run_script(
        &setup,
        r"const ok = await tools.status({ code: 0 });
const bad = await tools.status({ code: 2 });
let failed;
try { await tools.fail({}); } catch (error) { failed = [error.message, error.structuredOutput]; }
return [ok, bad, failed];",
    )
    .await;
    assert_eq!(
        returned(&message),
        JsonValue::parse(r#"[{"code":0},{"code":2},["it broke","it broke"]]"#).unwrap()
    );
    let statuses: Vec<(String, CodemodeCallStatus)> = details(&message)
        .calls
        .iter()
        .map(|row| (row.name.clone(), row.status))
        .collect();
    assert_eq!(
        statuses,
        vec![
            ("status".to_owned(), CodemodeCallStatus::Ok),
            ("status".to_owned(), CodemodeCallStatus::Error),
            ("fail".to_owned(), CodemodeCallStatus::Error),
        ]
    );
    assert_eq!(
        details(&message).calls[2].error.as_deref(),
        Some("it broke")
    );
}

#[tokio::test]
async fn scripts_find_tools_with_the_discovery_globals() {
    let setup = setup();
    let message = run_script(
        &setup,
        r#"return [
  (await describeTool("gh_search_issues")).includes("declare const tools"),
  await describeNamespace("github"),
  (await searchTools("issues")).map((tool) => tool.name),
  (await searchTools("echo", { namespace: "github" })).length,
  await describeTool("nope"),
  ALL_TOOLS.map((tool) => tool.name),
];"#,
    )
    .await;
    assert_eq!(
        returned(&message),
        JsonValue::parse(
            r#"[true,{"name":"github","description":"GitHub issues","instructions":"Prefer search","tools":["gh_search_issues"]},["gh_search_issues"],0,null,["echo","status","fail","gh_search_issues"]]"#
        )
        .unwrap()
    );
}

#[tokio::test]
async fn a_rejected_discovery_call_rejects_in_the_script() {
    let setup = setup();
    let message = run_script(
        &setup,
        r#"try { await searchTools("x", { limit: 0 }); } catch (error) { return error.message; }"#,
    )
    .await;
    // A returned string is output as it is.
    assert_eq!(
        text(&message).lines().last(),
        Some("searchTools() limit must be a positive integer")
    );
}

#[tokio::test]
async fn keeps_stored_values_across_calls_of_a_conversation() {
    let setup = setup();
    setup.chat.faux.set_responses(vec![
        call_with(
            "codemode",
            json!({ "code": r#"store("n", 41); store("gone", 1); return 1;"# }),
            "c1",
        )
        .into(),
        call_with(
            "codemode",
            json!({ "code": r#"store("gone", undefined); return [load("n") + 1, load("gone")];"# }),
            "c2",
        )
        .into(),
        call_with(
            "codemode",
            json!({ "code": r#"return load("gone");"# }),
            "c3",
        )
        .into(),
        done().into(),
    ]);
    let chat = open_chat(Arc::new(MemoryStorage::new()), &setup.chat, None)
        .await
        .unwrap();
    assert_eq!(
        submit_and_wait(&chat.root, "go").await,
        SubmissionStatus::Done
    );
    let entries = all_entries(&chat.root, context()).await.unwrap();
    let values: Vec<String> = results(&entries)
        .iter()
        .map(|message| text(message).lines().last().unwrap_or_default().to_owned())
        .collect();
    assert_eq!(values, vec!["1", "[42,null]", "Output:"]);
    chat.harness.close(context()).await.unwrap();
}

#[tokio::test]
async fn scripts_read_the_model_catalog_when_models_are_included() {
    let setup = setup_with(crate::codemode::CodemodeToolOptions {
        models: CodemodeModels::Included,
        ..options(sandbox())
    });
    let message = run_script(
        &setup,
        r#"const chat = await models.getModelsOfType("chat", "faux");
const one = await models.getModelOfType("chat", "faux", "faux-1");
return [chat.map((model) => model.id), one.provider, typeof models.classify];"#,
    )
    .await;
    assert_eq!(
        returned(&message),
        JsonValue::parse(r#"[["faux-1"],"faux","function"]"#).unwrap()
    );

    let setup = super::setup();
    let message = run_script(&setup, "return typeof models;").await;
    assert_eq!(text(&message).lines().last(), Some("undefined"));
}

#[tokio::test]
async fn a_classification_without_a_model_asks_the_default_classifier() {
    let asked = Arc::new(Mutex::new(Vec::new()));
    let seen = Arc::clone(&asked);
    let resolver: ClassifierResolver = Arc::new(move |_models, session_model| {
        lock(&seen).push(session_model);
        Box::pin(async { Err("no model of the judge role is available".to_owned()) })
    });
    let setup = setup_with(crate::codemode::CodemodeToolOptions {
        models: CodemodeModels::Included,
        classifier: ClassifierDefault::Resolver(resolver),
        ..options(sandbox())
    });
    let message = run_script(
        &setup,
        r#"const context = { state: {}, questions: { q: { type: "bool", instructions: "Is it?", criteria: { true: "yes", false: "no" } } } };
const answers = [];
for (const model of [null, undefined]) {
  try { await models.classify(model, context); answers.push("resolved"); } catch (error) { answers.push(error.message); }
}
return answers;"#,
    )
    .await;
    assert_eq!(
        (returned(&message), lock(&asked).clone()),
        (
            JsonValue::parse(
                r#"["no model of the judge role is available","no model of the judge role is available"]"#
            )
            .unwrap(),
            vec!["faux/faux-1".to_owned(), "faux/faux-1".to_owned()]
        )
    );
}

#[tokio::test]
async fn invalid_source_options_end_the_call_with_an_error() {
    let setup = setup();
    let message = run_script(&setup, "// @options: {\"bogus\": 1}\nreturn 1;").await;
    assert!(message.is_error);
    assert!(
        text(&message)
            .contains("@options only supports `max_output_tokens` and `timeout_ms`; got `bogus`"),
        "{}",
        text(&message)
    );
    assert_eq!(setup.runs.all(), Vec::<String>::new());
}

#[tokio::test]
async fn cuts_output_to_its_token_budget_and_reports_a_failed_spill() {
    let setup = setup();
    let message = run_script(
        &setup,
        "// @options: {\"max_output_tokens\": 5}\ntext(\"a\".repeat(50) + \"b\".repeat(50));",
    )
    .await;
    assert_eq!(
        text(&message),
        "Script completed\nWall time <t> seconds\nOutput:\nWarning: truncated output (original token count: 25)\nTotal output lines: 1\n\naaaaaaaaaa…20 tokens truncated…bbbbbbbbbb\n\n[Could not save the full output: no execution environment]"
    );
}

#[tokio::test]
async fn a_failed_script_reports_its_error_and_the_calls_it_made() {
    let setup = setup();
    let message = run_script(
        &setup,
        "await tools.echo({ text: \"x\" });\nthrow new Error(\"nope\");",
    )
    .await;
    assert!(message.is_error);
    let text = text(&message);
    assert!(
        text.starts_with(
            "Script failed\nWall time <t> seconds\nOutput:\nScript error:\nError: nope\n"
        ),
        "{text}"
    );
    assert!(
        text.ends_with("\n\nTool calls made before the failure (they are not undone): echo (ok)"),
        "{text}"
    );
}

#[tokio::test]
async fn the_scripts_deadline_ends_a_busy_script() {
    let setup = setup();
    let message = run_script(&setup, "// @options: {\"timeout_ms\": 50}\nwhile (true) {}").await;
    assert!(message.is_error);
    // The run's deadline is what remains of the script's own when the VM
    // starts.
    let text = text(&message);
    assert!(
        text.starts_with("Script failed\nWall time <t> seconds\nOutput:\nScript error:\nScript timed out: Execution timed out after "),
        "{text}"
    );
    assert!(text.ends_with(" ms\n\nNo tool calls were made."), "{text}");
}

#[tokio::test]
async fn the_codemode_section_lists_the_callable_tools_by_namespace() {
    let Setup { chat, .. } = setup();
    let requests: Arc<Mutex<Vec<String>>> = Arc::default();
    let sink = Arc::clone(&requests);
    chat.faux
        .set_responses(vec![FauxResponseStep::factory(move |request, _, _, _| {
            lock(&sink).push(serde_json::to_string(request.messages()).unwrap_or_default());
            Ok(done())
        })]);
    let open = open_chat(Arc::new(MemoryStorage::new()), &chat, None)
        .await
        .unwrap();
    assert_eq!(
        submit_and_wait(&open.root, "go").await,
        SubmissionStatus::Done
    );
    open.harness.close(context()).await.unwrap();
    let request = lock(&requests).pop().expect("a request");
    for expected in [
        "Tools scripts can call (`await tools.<name>(args)`):",
        "## github\\nGitHub issues",
        "### `echo`",
        "### `gh_search_issues`",
    ] {
        assert!(request.contains(expected), "{expected} in {request}");
    }
    // The code mode tool itself is not callable from scripts.
    assert!(!request.contains("### `codemode`"), "{request}");
}
