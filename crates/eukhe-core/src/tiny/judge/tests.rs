use eukhe_ai::models::{create_models, CreateModelsOptions};
use eukhe_tiny::{find, FallbackChain};

use super::*;

/// The conversation's chat model: on `acme`, which lists it as no
/// classifier.
const SESSION: &str = "acme/chat-1";

/// `acme`'s classifier model.
fn sorter() -> ClassifierModel {
    ClassifierModel {
        id: "sorter".to_owned(),
        name: "Sorter".to_owned(),
        api: "acme-classify".to_owned(),
        provider: "acme".to_owned(),
        base_url: String::new(),
        input: vec![Modality::Text],
        input_limits: None,
        cost: ModelCost::default(),
        headers: None,
        context_window: 4_096,
    }
}

/// A model collection with the `local` provider and `acme`, a keyless
/// provider with one classifier model.
fn models(agent_dir: &Path) -> Models {
    let models = create_models(CreateModelsOptions::default());
    add_local_provider(&models, agent_dir);
    let classify: eukhe_ai::api::ClassifyFn = Arc::new(|model, _context, _options| {
        let model = model.clone();
        Box::pin(async move {
            ClassifierResult {
                api: model.api,
                provider: model.provider,
                model: model.id,
                answers: IndexMap::new(),
                usage: None,
                stop_reason: ClassifierStopReason::Error,
                error_message: Some("these tests pick models only".to_owned()),
                timestamp: 0,
            }
        })
    });
    let acme = create_provider(CreateProviderOptions {
        id: "acme".to_owned(),
        name: Some("Acme".to_owned()),
        auth: ProviderAuth {
            api_key: Some(Arc::new(LocalAuth)),
            oauth: None,
        },
        models: Arc::from([AnyModel::Classifier(sorter())]),
        classifiers: Some(IndexMap::from_iter([(
            "acme-classify".to_owned(),
            ProviderClassifier { classify },
        )])),
        ..CreateProviderOptions::default()
    })
    .expect("acme provider");
    models.set_provider(acme);
    models
}

fn settings(primary: &str, fallback: FallbackChain) -> RoleSettings {
    RoleSettings {
        primary: primary.to_owned(),
        fallback,
    }
}

fn local(id: &str) -> ClassifierModel {
    classifier_model(find(id).expect("catalog model"))
}

#[tokio::test]
async fn a_classification_without_a_model_takes_the_first_available_judge_model() {
    let agent_dir = tempfile::tempdir().expect("agent dir");
    let models = models(agent_dir.path());
    let only_350m = |model: &CatalogModel| model.id == "lfm2.5-350m";
    let unset = settings("", FallbackChain::Unset);
    let acme_first = settings("acme/sorter", FallbackChain::Unset);
    let missing_first = settings(
        "acme/nope",
        FallbackChain::Explicit(vec![
            "local/lfm2.5-230m".to_owned(),
            "local/lfm2.5-350m".to_owned(),
            "acme/sorter".to_owned(),
        ]),
    );
    assert_eq!(
        (
            judge_classifier(&models, &unset, SESSION, only_350m).await,
            judge_classifier(&models, &acme_first, SESSION, only_350m).await,
            judge_classifier(&models, &missing_first, SESSION, only_350m).await,
            judge_classifier(&models, &missing_first, SESSION, |_| false).await,
        ),
        (
            Ok(local("lfm2.5-350m")),
            Ok(sorter()),
            Ok(local("lfm2.5-350m")),
            Ok(sorter()),
        )
    );
}

#[tokio::test]
async fn a_classification_without_an_available_judge_model_is_unavailable() {
    let agent_dir = tempfile::tempdir().expect("agent dir");
    let models = models(agent_dir.path());
    let result = judge_classifier(
        &models,
        &settings("", FallbackChain::Unset),
        SESSION,
        |_| false,
    )
    .await;
    assert_eq!(
        (result.clone(), result.map_err(|error| error.to_string())),
        (
            Err(JudgeClassifierError::Unavailable(RoleUnavailable {
                role: Role::Judge,
                chain: vec![
                    Candidate::Local("lfm2.5-230m".to_owned()),
                    Candidate::Local("lfm2.5-350m".to_owned()),
                    Candidate::Remote(SESSION.to_owned()),
                ],
            })),
            Err(
                "no model of the judge role is available (chain: local/lfm2.5-230m, \
                 local/lfm2.5-350m, acme/chat-1); install one with \
                 `eukhe tiny-models download lfm2.5-230m`"
                    .to_owned()
            ),
        )
    );
}
