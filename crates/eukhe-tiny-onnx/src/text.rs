//! Text generation: a decoder LLM exported to ONNX with its KV (and, for
//! LFM2, conv) cache as graph inputs and outputs, greedy decoding.

use std::borrow::Cow;
use std::path::{Path, PathBuf};

use eukhe_tiny::{
    Audio, ChatReply, ChatRequest, ChatRole, ChatTemplate, Engine, SpeakRequest, StopReason,
    TranscribeRequest, Transcript, WorkerFailure,
};
use ort::session::{Session, SessionInputValue};
use ort::value::{DynValue, Tensor, TensorElementType, ValueType};

use crate::runtime::Runtime;
use crate::tokenizer::Tokenizer;

/// The model graph, relative to the model directory.
const MODEL_FILE: &str = "onnx/model_q4.onnx";
/// The `ChatML` turn end; it ends the assistant turn like the eos id.
const CHAT_ML_TURN_END: &str = "<|im_end|>";

pub(crate) struct TextEngine {
    dir: PathBuf,
    template: ChatTemplate,
    runtime: Runtime,
    model: Option<Model>,
}

impl TextEngine {
    pub(crate) fn new(dir: PathBuf, template: ChatTemplate, runtime: Runtime) -> TextEngine {
        TextEngine {
            dir,
            template,
            runtime,
            model: None,
        }
    }

    fn model(&mut self) -> Result<&mut Model, WorkerFailure> {
        let model = match self.model.take() {
            Some(model) => model,
            None => Model::load(&self.dir, self.template, &mut self.runtime)?,
        };
        Ok(self.model.insert(model))
    }
}

impl Engine for TextEngine {
    fn load(&mut self) -> Result<(), WorkerFailure> {
        self.model().map(|_| ())
    }

    fn chat(&mut self, request: &ChatRequest) -> Result<ChatReply, WorkerFailure> {
        let prompt = render(self.template, request);
        self.model()?.generate(&prompt, request)
    }

    fn transcribe(&mut self, _request: &TranscribeRequest) -> Result<Transcript, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "transcribe".to_owned(),
        })
    }

    fn speak(&mut self, _request: &SpeakRequest) -> Result<Audio, WorkerFailure> {
        Err(WorkerFailure::Unsupported {
            op: "speak".to_owned(),
        })
    }
}

/// The prompt of a chat request: the chat template with the generation
/// prompt and the prefill (the model card's `chat_template.jinja`, minus
/// tools and thinking).
fn render(template: ChatTemplate, request: &ChatRequest) -> String {
    match template {
        ChatTemplate::ChatMl => {
            let mut prompt = String::from("<|startoftext|>");
            for (index, message) in request.messages.iter().enumerate() {
                let role = match message.role {
                    // The template drops an empty leading system prompt.
                    ChatRole::System if index == 0 && message.content.is_empty() => continue,
                    ChatRole::System => "system",
                    ChatRole::User => "user",
                    ChatRole::Assistant => "assistant",
                };
                prompt.push_str("<|im_start|>");
                prompt.push_str(role);
                prompt.push('\n');
                prompt.push_str(&message.content);
                prompt.push_str(CHAT_ML_TURN_END);
                prompt.push('\n');
            }
            prompt.push_str("<|im_start|>assistant\n");
            prompt.push_str(&request.prefill);
            prompt
        }
    }
}

/// An integer input's element type.
#[derive(Debug, Clone, Copy)]
enum IntKind {
    I64,
    I32,
}

/// What one graph input is fed with.
#[derive(Debug)]
enum Feed {
    /// The new tokens, `[1, new]`.
    InputIds(IntKind),
    /// Ones over the past and new tokens, `[1, past + new]`.
    AttentionMask(IntKind),
    /// The positions of the new tokens, `[1, new]`.
    PositionIds(IntKind),
    /// The number of cached tokens (scalar or `[1]`).
    PastLength { kind: IntKind, rank: usize },
    /// A cache entry: zeros of this shape first, then the paired
    /// `present…` output of the previous step.
    State(Vec<i64>),
}

/// What becomes of one graph output.
#[derive(Debug, Clone, Copy)]
enum Sink {
    Logits,
    /// The next value of the state input at this index of the state list.
    State(usize),
    Unused,
}

/// How a decoder graph is fed and read, from its input and output names.
struct Graph {
    /// The graph inputs in session order.
    inputs: Vec<(String, Feed)>,
    /// The graph outputs by name.
    outputs: Vec<(String, Sink)>,
}

impl Graph {
    fn of(session: &Session) -> Result<Graph, WorkerFailure> {
        let load = |message: String| WorkerFailure::Load { message };
        let int_kind = |name: &str, dtype: &ValueType| match dtype.tensor_type() {
            Some(TensorElementType::Int64) => Ok(IntKind::I64),
            Some(TensorElementType::Int32) => Ok(IntKind::I32),
            Some(other) => Err(load(format!(
                "{MODEL_FILE}: input `{name}` is {other}, not an integer"
            ))),
            None => Err(load(format!(
                "{MODEL_FILE}: input `{name}` is {dtype}, not a tensor"
            ))),
        };
        let mut inputs = Vec::with_capacity(session.inputs().len());
        let mut presents = Vec::new();
        for input in session.inputs() {
            let name = input.name();
            let dtype = input.dtype();
            let feed = match name {
                "input_ids" => Feed::InputIds(int_kind(name, dtype)?),
                "attention_mask" => Feed::AttentionMask(int_kind(name, dtype)?),
                "position_ids" => Feed::PositionIds(int_kind(name, dtype)?),
                "past_sequence_length" => Feed::PastLength {
                    kind: int_kind(name, dtype)?,
                    rank: dtype.tensor_shape().map_or(0, |shape| shape.len()),
                },
                _ => {
                    // `past_key_values.N.key` ↔ `present.N.key`,
                    // `past_conv.N` ↔ `present_conv.N`.
                    let present = match name.strip_prefix("past_key_values.") {
                        Some(rest) => format!("present.{rest}"),
                        None => match name.strip_prefix("past_") {
                            Some(rest) => format!("present_{rest}"),
                            None => {
                                return Err(load(format!(
                                    "{MODEL_FILE}: unsupported input `{name}`"
                                )));
                            }
                        },
                    };
                    let (Some(TensorElementType::Float32), Some(shape)) =
                        (dtype.tensor_type(), dtype.tensor_shape())
                    else {
                        return Err(load(format!(
                            "{MODEL_FILE}: cache input `{name}` is {dtype}, not a float32 tensor"
                        )));
                    };
                    // Batch 1; every other dynamic dimension is the (empty)
                    // past sequence.
                    let initial = shape
                        .iter()
                        .enumerate()
                        .map(|(axis, &dim)| match dim {
                            ..=-1 if axis == 0 => 1,
                            ..=-1 => 0,
                            dim => dim,
                        })
                        .collect();
                    presents.push(present);
                    Feed::State(initial)
                }
            };
            inputs.push((name.to_owned(), feed));
        }
        if !inputs
            .iter()
            .any(|(_, feed)| matches!(feed, Feed::InputIds(_)))
        {
            return Err(load(format!("{MODEL_FILE}: no `input_ids` input")));
        }
        let outputs: Vec<(String, Sink)> = session
            .outputs()
            .iter()
            .map(|output| {
                let name = output.name();
                let sink = if name == "logits" {
                    Sink::Logits
                } else {
                    presents
                        .iter()
                        .position(|present| present == name)
                        .map_or(Sink::Unused, Sink::State)
                };
                (name.to_owned(), sink)
            })
            .collect();
        if !outputs.iter().any(|(_, sink)| matches!(sink, Sink::Logits)) {
            return Err(load(format!("{MODEL_FILE}: no `logits` output")));
        }
        for present in &presents {
            if !outputs.iter().any(|(name, _)| name == present) {
                return Err(load(format!(
                    "{MODEL_FILE}: no `{present}` output for its cache input"
                )));
            }
        }
        Ok(Graph { inputs, outputs })
    }
}

/// A loaded text model.
struct Model {
    session: Session,
    tokenizer: Tokenizer,
    eos: Vec<u32>,
    graph: Graph,
}

impl Model {
    fn load(
        dir: &Path,
        template: ChatTemplate,
        runtime: &mut Runtime,
    ) -> Result<Model, WorkerFailure> {
        let load = |message: String| WorkerFailure::Load { message };
        let tokenizer_path = dir.join("tokenizer.json");
        let tokenizer = Tokenizer::from_file(&tokenizer_path)
            .map_err(|error| load(format!("{}: {error}", tokenizer_path.display())))?;
        let mut eos = Vec::new();
        for file in ["generation_config.json", "config.json"] {
            let path = dir.join(file);
            let text = std::fs::read_to_string(&path)
                .map_err(|error| load(format!("{}: {error}", path.display())))?;
            let config: serde_json::Value = serde_json::from_str(&text)
                .map_err(|error| load(format!("{}: {error}", path.display())))?;
            let ids = match config.get("eos_token_id") {
                Some(serde_json::Value::Array(ids)) => ids.iter().collect(),
                Some(id) => vec![id],
                None => Vec::new(),
            };
            for id in ids {
                let id = id
                    .as_u64()
                    .and_then(|id| u32::try_from(id).ok())
                    .ok_or_else(|| load(format!("{}: bad eos_token_id {id}", path.display())))?;
                if !eos.contains(&id) {
                    eos.push(id);
                }
            }
        }
        match template {
            ChatTemplate::ChatMl => {
                if let Some(id) = tokenizer.token_to_id(CHAT_ML_TURN_END) {
                    if !eos.contains(&id) {
                        eos.push(id);
                    }
                }
            }
        }
        if eos.is_empty() {
            return Err(load(format!("{}: no eos_token_id", dir.display())));
        }
        let session = runtime.session(&dir.join(MODEL_FILE))?;
        let graph = Graph::of(&session)?;
        Ok(Model {
            session,
            tokenizer,
            eos,
            graph,
        })
    }

    /// Greedy decoding of `prompt` (which ends with the request's prefill).
    fn generate(
        &mut self,
        prompt: &str,
        request: &ChatRequest,
    ) -> Result<ChatReply, WorkerFailure> {
        let inference = |message: String| WorkerFailure::Inference { message };
        let mut new: Vec<u32> = self
            .tokenizer
            .encode(prompt)
            .map_err(|error| inference(format!("tokenize: {error}")))?;
        let mut states: Vec<Option<DynValue>> = Vec::new();
        for (name, feed) in &self.graph.inputs {
            if let Feed::State(initial) = feed {
                let zeros = vec![
                    0.0_f32;
                    initial
                        .iter()
                        .map(|&dim| usize::try_from(dim).unwrap_or(0))
                        .product()
                ];
                let tensor = Tensor::from_array((initial.clone(), zeros))
                    .map_err(|error| inference(format!("{name}: {error}")))?;
                states.push(Some(tensor.into_dyn()));
            }
        }
        let stops: Vec<&str> = request
            .stop
            .iter()
            .map(String::as_str)
            .filter(|stop| !stop.is_empty())
            .collect();
        let max_tokens = usize::try_from(request.max_tokens).unwrap_or(usize::MAX);
        let mut past = 0_usize;
        let mut generated: Vec<u32> = Vec::new();
        let mut text = String::new();
        loop {
            if generated.len() >= max_tokens {
                return Ok(ChatReply {
                    text,
                    stop: StopReason::Length,
                });
            }
            let token = self.step(&new, past, &mut states)?;
            past += new.len();
            if self.eos.contains(&token) {
                return Ok(ChatReply {
                    text,
                    stop: StopReason::Eos,
                });
            }
            generated.push(token);
            text = self.tokenizer.decode(&generated);
            if let Some(end) = stops.iter().filter_map(|stop| text.find(stop)).min() {
                text.truncate(end);
                return Ok(ChatReply {
                    text,
                    stop: StopReason::Stop,
                });
            }
            new.clear();
            new.push(token);
        }
    }

    /// One forward pass over `new` tokens after `past` cached ones: the
    /// greedy next token. Takes the cache from `states` and puts the
    /// updated cache back.
    fn step(
        &mut self,
        new: &[u32],
        past: usize,
        states: &mut [Option<DynValue>],
    ) -> Result<u32, WorkerFailure> {
        let inference = |message: String| WorkerFailure::Inference { message };
        let total = past + new.len();
        let mut feeds: Vec<(Cow<'_, str>, SessionInputValue<'_>)> =
            Vec::with_capacity(self.graph.inputs.len());
        let mut cache = states.iter_mut();
        for (name, feed) in &self.graph.inputs {
            let value = match feed {
                Feed::InputIds(kind) => int_tensor(
                    *kind,
                    vec![1, new.len()],
                    new.iter().map(|&id| i64::from(id)),
                ),
                Feed::AttentionMask(kind) => {
                    int_tensor(*kind, vec![1, total], (0..total).map(|_| 1))
                }
                Feed::PositionIds(kind) => int_tensor(
                    *kind,
                    vec![1, new.len()],
                    (past..total).map(|position| i64::try_from(position).unwrap_or(i64::MAX)),
                ),
                Feed::PastLength { kind, rank } => int_tensor(
                    *kind,
                    vec![1; *rank],
                    std::iter::once(i64::try_from(past).unwrap_or(i64::MAX)),
                ),
                Feed::State(_) => cache
                    .next()
                    .and_then(Option::take)
                    .ok_or_else(|| "no cache value".to_owned()),
            }
            .map_err(|error| inference(format!("{name}: {error}")))?;
            feeds.push((Cow::Borrowed(name.as_str()), SessionInputValue::from(value)));
        }
        let outputs = self
            .session
            .run(feeds)
            .map_err(|error| inference(error.to_string()))?;
        let mut token = None;
        for (name, value) in outputs {
            let sink = self
                .graph
                .outputs
                .iter()
                .find_map(|(output, sink)| (output == name).then_some(*sink))
                .unwrap_or(Sink::Unused);
            match sink {
                Sink::Logits => {
                    let (shape, logits) = value
                        .try_extract_tensor::<f32>()
                        .map_err(|error| inference(format!("logits: {error}")))?;
                    let bad_shape = || inference(format!("logits: bad shape {shape}"));
                    let vocab = shape
                        .last()
                        .and_then(|&dim| usize::try_from(dim).ok())
                        .filter(|&vocab| vocab > 0 && logits.len() >= vocab)
                        .ok_or_else(bad_shape)?;
                    let best = logits[logits.len() - vocab..]
                        .iter()
                        .enumerate()
                        .max_by(|(_, a), (_, b)| a.total_cmp(b))
                        .and_then(|(index, _)| u32::try_from(index).ok())
                        .ok_or_else(bad_shape)?;
                    token = Some(best);
                }
                Sink::State(index) => {
                    if let Some(slot) = states.get_mut(index) {
                        *slot = Some(value);
                    }
                }
                Sink::Unused => {}
            }
        }
        if states.iter().any(Option::is_none) {
            return Err(inference("a cache output is missing".to_owned()));
        }
        token.ok_or_else(|| inference("no logits output".to_owned()))
    }
}

/// An integer tensor of `kind` (the values fit: token ids, positions and
/// lengths of a prompt).
fn int_tensor(
    kind: IntKind,
    shape: Vec<usize>,
    values: impl Iterator<Item = i64>,
) -> Result<DynValue, String> {
    match kind {
        IntKind::I64 => {
            Tensor::from_array((shape, values.collect::<Vec<i64>>())).map(Tensor::into_dyn)
        }
        IntKind::I32 => {
            let values = values
                .map(i32::try_from)
                .collect::<Result<Vec<i32>, _>>()
                .map_err(|error| error.to_string())?;
            Tensor::from_array((shape, values)).map(Tensor::into_dyn)
        }
    }
    .map_err(|error| error.to_string())
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;
    use std::time::Instant;

    use eukhe_tiny::{
        ChatMessage, ChatRequest, ChatRole, ChatTemplate, Engine, EngineOptions, StopReason,
    };

    use super::{render, TextEngine};
    use crate::runtime::Runtime;

    fn title_request() -> ChatRequest {
        ChatRequest {
            messages: vec![
                ChatMessage {
                    role: ChatRole::System,
                    content: "Write a short title for the user's request.".to_owned(),
                },
                ChatMessage {
                    role: ChatRole::User,
                    content: "How do I resize a btrfs partition on an encrypted LUKS volume?"
                        .to_owned(),
                },
            ],
            prefill: "<title>".to_owned(),
            stop: vec!["</title>".to_owned()],
            max_tokens: 24,
        }
    }

    #[test]
    fn chat_ml_prompt() {
        assert_eq!(
            render(ChatTemplate::ChatMl, &title_request()),
            "<|startoftext|><|im_start|>system\nWrite a short title for the user's request.<|im_end|>\n\
             <|im_start|>user\nHow do I resize a btrfs partition on an encrypted LUKS volume?<|im_end|>\n\
             <|im_start|>assistant\n<title>"
        );
    }

    /// Needs `EUKHE_TINY_TEST_MODELS` (a directory with `lfm2.5-230m/`)
    /// and `ORT_DYLIB_PATH`; skipped otherwise.
    #[test]
    fn lfm2_writes_a_title() {
        let Some(models) = std::env::var_os("EUKHE_TINY_TEST_MODELS") else {
            println!("SKIPPED: EUKHE_TINY_TEST_MODELS is not set");
            return;
        };
        let dir = PathBuf::from(models).join("lfm2.5-230m");
        if !dir.is_dir() {
            println!("SKIPPED: {} is not a directory", dir.display());
            return;
        }
        let Some(library) = std::env::var_os("ORT_DYLIB_PATH") else {
            println!("SKIPPED: ORT_DYLIB_PATH is not set");
            return;
        };
        let runtime = Runtime::new(&EngineOptions {
            device: "cpu".to_owned(),
            dtype: String::new(),
            runtime_library: PathBuf::from(library),
        })
        .expect("runtime options");
        let mut engine = TextEngine::new(dir, ChatTemplate::ChatMl, runtime);
        let started = Instant::now();
        engine.load().expect("load");
        let loaded = started.elapsed();
        let started = Instant::now();
        let reply = engine.chat(&title_request()).expect("chat");
        let generated = started.elapsed();
        println!(
            "title: {:?} ({:?}); load {loaded:?}, chat {generated:?}",
            reply.text, reply.stop
        );
        match reply.stop {
            StopReason::Stop | StopReason::Eos => {}
            StopReason::Length => panic!("no end within 24 tokens: {reply:?}"),
        }
        assert!(!reply.text.trim().is_empty(), "empty title: {reply:?}");
        assert!(
            !reply.text.contains("</title>"),
            "stop string kept: {reply:?}"
        );
    }
}
