//! Test support of the coding tools: a fake execution api and an
//! environment whose operations a test can intercept (the TS subclasses of
//! `NodeExecutionEnv`).

use std::sync::{Arc, Mutex, PoisonError};

use eukhe_chord::context::{Context, BACKGROUND_CONTEXT};
use eukhe_chord::json::JsonValue;
use eukhe_pi_ai::models::Models;
use eukhe_types::pi_ai::{
    JsonObject as PiJsonObject, JsonValue as PiJsonValue, ModelThinkingLevel, UserContentBlock,
};
use futures::future::BoxFuture;
use futures::FutureExt;

use crate::documents::{AnyDocDefinition, ResolvedAddress};
use crate::env::{
    BinaryReader, CreateDirOptions, DirReader, ExecCommand, ExecutionEnv, ExecutionError,
    FileError, FileInfo, FileSystem, FileWatcher, NativeExecutionEnv, NativeExecutionEnvOptions,
    OnWatchChange, OpenBinaryReaderOptions, ReadTextLinesOptions, RemoveOptions, Shell,
    ShellExecOptions, ShellExecResult, ShellOutputSkip, ShellOutputWindow, TempFileOptions,
    TextLineReader, WatchTarget,
};
use crate::harness::types::{
    Agent, ConversationHandle, ExecuteToolOptions, InvocationTaskOptions, ModelRef,
    NestedToolExecutionResult, RegistrySnapshot, RetainedOutput, ToolCommitChange, ToolDiagnostic,
    ToolExecutionApi, ToolExecutionResult, ToolOutputChunk, ToolRegistration,
};
use crate::session::{DocumentWatch, SessionError, SessionResult};
use crate::tasks::{AnyTask, SettledTask};
use crate::types::{
    AnyTaskRecord, ConversationId, DocumentObserver, DocumentReader, EntryId, JsonObject, TaskId,
};

/// A temporary working directory, removed on drop.
pub(super) fn temp_dir() -> tempfile::TempDir {
    tempfile::Builder::new()
        .prefix("pi-durable-tools-")
        .tempdir()
        .expect("temp dir")
}

pub(super) fn native(cwd: &tempfile::TempDir) -> NativeExecutionEnv {
    NativeExecutionEnv::new(NativeExecutionEnvOptions {
        cwd: cwd.path().to_string_lossy().into_owned(),
        ..NativeExecutionEnvOptions::default()
    })
}

pub(super) type ReadTextHook = Arc<
    dyn for<'a> Fn(
            &'a NativeExecutionEnv,
            &'a str,
            &'a Context,
        ) -> BoxFuture<'a, Result<String, FileError>>
        + Send
        + Sync,
>;
pub(super) type WriteHook = Arc<
    dyn for<'a> Fn(
            &'a NativeExecutionEnv,
            &'a str,
            &'a [u8],
            &'a Context,
        ) -> BoxFuture<'a, Result<(), FileError>>
        + Send
        + Sync,
>;
pub(super) type OpenReaderHook = Arc<
    dyn for<'a> Fn(
            &'a NativeExecutionEnv,
            &'a str,
            OpenBinaryReaderOptions,
            &'a Context,
        ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>>
        + Send
        + Sync,
>;
pub(super) type ExecHook = Arc<
    dyn for<'a> Fn(
            &'a NativeExecutionEnv,
            &'a ExecCommand,
            &'a ShellExecOptions,
            &'a Context,
        ) -> BoxFuture<'a, Result<ShellExecResult, ExecutionError>>
        + Send
        + Sync,
>;

/// A native environment with interceptable operations.
pub(super) struct HookedEnv {
    pub(super) inner: NativeExecutionEnv,
    pub(super) id: Option<String>,
    pub(super) read_text_file: Option<ReadTextHook>,
    pub(super) write_file: Option<WriteHook>,
    pub(super) open_binary_reader: Option<OpenReaderHook>,
    pub(super) exec: Option<ExecHook>,
}

impl HookedEnv {
    pub(super) fn new(inner: NativeExecutionEnv) -> Self {
        Self {
            inner,
            id: None,
            read_text_file: None,
            write_file: None,
            open_binary_reader: None,
            exec: None,
        }
    }
}

impl FileSystem for HookedEnv {
    fn id(&self) -> &str {
        self.id.as_deref().unwrap_or_else(|| self.inner.id())
    }

    fn read_text_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        match &self.read_text_file {
            Some(hook) => hook(&self.inner, path, cx),
            None => self.inner.read_text_file(path, cx),
        }
    }

    fn write_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        match &self.write_file {
            Some(hook) => hook(&self.inner, path, content, cx),
            None => self.inner.write_file(path, content, cx),
        }
    }

    fn open_binary_reader<'a>(
        &'a self,
        path: &'a str,
        options: OpenBinaryReaderOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn BinaryReader>, FileError>> {
        match &self.open_binary_reader {
            Some(hook) => hook(&self.inner, path, options, cx),
            None => self.inner.open_binary_reader(path, options, cx),
        }
    }

    fn cwd(&self) -> &str {
        FileSystem::cwd(&self.inner)
    }

    fn absolute_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        FileSystem::absolute_path(&self.inner, path, cx)
    }

    fn join_path<'a>(
        &'a self,
        parts: &'a [&'a str],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        FileSystem::join_path(&self.inner, parts, cx)
    }

    fn open_text_line_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn TextLineReader>, FileError>> {
        FileSystem::open_text_line_reader(&self.inner, path, cx)
    }

    fn read_text_lines<'a>(
        &'a self,
        path: &'a str,
        options: ReadTextLinesOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<String>, FileError>> {
        FileSystem::read_text_lines(&self.inner, path, options, cx)
    }

    fn read_binary_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<u8>, FileError>> {
        FileSystem::read_binary_file(&self.inner, path, cx)
    }

    fn append_file<'a>(
        &'a self,
        path: &'a str,
        content: &'a [u8],
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::append_file(&self.inner, path, content, cx)
    }

    fn truncate_file<'a>(
        &'a self,
        path: &'a str,
        size: f64,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::truncate_file(&self.inner, path, size, cx)
    }

    fn flush_file<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::flush_file(&self.inner, path, cx)
    }

    fn rename_file<'a>(
        &'a self,
        source_path: &'a str,
        destination_path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::rename_file(&self.inner, source_path, destination_path, cx)
    }

    fn file_info<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<FileInfo, FileError>> {
        FileSystem::file_info(&self.inner, path, cx)
    }

    fn list_dir<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Vec<FileInfo>, FileError>> {
        FileSystem::list_dir(&self.inner, path, cx)
    }

    fn open_dir_reader<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn DirReader>, FileError>> {
        FileSystem::open_dir_reader(&self.inner, path, cx)
    }

    fn watch<'a>(
        &'a self,
        targets: &'a [WatchTarget],
        on_change: OnWatchChange,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<Box<dyn FileWatcher>, FileError>> {
        FileSystem::watch(&self.inner, targets, on_change, cx)
    }

    fn canonical_path<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        FileSystem::canonical_path(&self.inner, path, cx)
    }

    fn exists<'a>(
        &'a self,
        path: &'a str,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<bool, FileError>> {
        FileSystem::exists(&self.inner, path, cx)
    }

    fn create_dir<'a>(
        &'a self,
        path: &'a str,
        options: CreateDirOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::create_dir(&self.inner, path, options, cx)
    }

    fn remove<'a>(
        &'a self,
        path: &'a str,
        options: RemoveOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<(), FileError>> {
        FileSystem::remove(&self.inner, path, options, cx)
    }

    fn create_temp_dir<'a>(
        &'a self,
        prefix: Option<&'a str>,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        FileSystem::create_temp_dir(&self.inner, prefix, cx)
    }

    fn create_temp_file<'a>(
        &'a self,
        options: TempFileOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<String, FileError>> {
        FileSystem::create_temp_file(&self.inner, options, cx)
    }

    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        FileSystem::cleanup(&self.inner, cx)
    }
}

impl Shell for HookedEnv {
    fn exec<'a>(
        &'a self,
        command: &'a ExecCommand,
        options: &'a ShellExecOptions,
        cx: &'a Context,
    ) -> BoxFuture<'a, Result<ShellExecResult, ExecutionError>> {
        match &self.exec {
            Some(hook) => hook(&self.inner, command, options, cx),
            None => self.inner.exec(command, options, cx),
        }
    }

    fn cleanup<'a>(&'a self, cx: &'a Context) -> BoxFuture<'a, ()> {
        Shell::cleanup(&self.inner, cx)
    }
}

/// One `output()` call: the text and what the environment skipped before it.
pub(super) type OutputCall = (String, Option<ShellOutputSkip>);

/// A minimal execution API: the environment, collected output and
/// diagnostics, and nothing durable (TS `fakeApi`).
pub(super) struct FakeApi {
    pub(super) env: Option<Arc<dyn ExecutionEnv>>,
    pub(super) window: Option<ShellOutputWindow>,
    pub(super) output: Mutex<Vec<OutputCall>>,
    pub(super) diagnostics: Mutex<Vec<ToolDiagnostic>>,
    /// The agent's model and the models resolving it; without one, `read`
    /// treats the model as one that sees images.
    pub(super) model: Option<(Models, ModelRef)>,
}

impl FakeApi {
    pub(super) fn new(env: Option<Arc<dyn ExecutionEnv>>) -> Arc<Self> {
        Self::with_model(env, None)
    }

    pub(super) fn with_model(
        env: Option<Arc<dyn ExecutionEnv>>,
        model: Option<(Models, ModelRef)>,
    ) -> Arc<Self> {
        Arc::new(Self {
            env,
            window: None,
            output: Mutex::new(Vec::new()),
            diagnostics: Mutex::new(Vec::new()),
            model,
        })
    }

    pub(super) fn text(&self) -> String {
        self.output
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .map(|(text, _)| text.as_str())
            .collect()
    }

    pub(super) fn reported(&self) -> Vec<ToolDiagnostic> {
        self.diagnostics
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone()
    }
}

fn absent<T: Send + 'static>(what: &str) -> BoxFuture<'static, SessionResult<T>> {
    let error = SessionError::error(format!("The fake api has no {what}"));
    futures::future::ready(Err(error)).boxed()
}

impl DocumentReader for FakeApi {
    fn snapshot_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        absent("documents")
    }

    fn snapshot_as_of_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _at: EntryId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<JsonObject>>>> {
        absent("documents")
    }
}

impl DocumentObserver for FakeApi {
    fn watch_doc_definition(
        &self,
        _definition: Arc<dyn AnyDocDefinition>,
        _resolved: ResolvedAddress,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<DocumentWatch>>> {
        absent("documents")
    }
}

impl ToolExecutionApi for FakeApi {
    fn task_id(&self) -> TaskId {
        TaskId::from_number(1)
    }

    fn conversation_id(&self) -> ConversationId {
        ConversationId::from_number(1)
    }

    #[expect(
        clippy::unnecessary_literal_bound,
        reason = "the trait ties the ID to the api"
    )]
    fn call_id(&self) -> &str {
        "call"
    }

    fn registry(&self) -> RegistrySnapshot {
        panic!("the fake api has no registry")
    }

    fn models(&self) -> Models {
        match &self.model {
            Some((models, _)) => models.clone(),
            None => panic!("the fake api has no models"),
        }
    }

    fn agent(&self, _cx: &Context) -> BoxFuture<'static, SessionResult<Arc<Agent>>> {
        // No model: `read` treats it as one that sees images.
        let agent = Agent {
            model: self.model.as_ref().map(|(_, model)| model.clone()),
            thinking_level: ModelThinkingLevel::Off,
            extensions: Vec::new(),
            tools: Vec::new(),
            callable: Vec::new(),
            sections: Vec::new(),
            instructions: None,
            cwd: None,
        };
        futures::future::ready(Ok(Arc::new(agent))).boxed()
    }

    fn env(&self) -> Option<Arc<dyn ExecutionEnv>> {
        self.env.clone()
    }

    fn output(
        &self,
        chunk: ToolOutputChunk<'_>,
        skipped: Option<ShellOutputSkip>,
    ) -> SessionResult<()> {
        let text = match chunk {
            ToolOutputChunk::Text(text) => text.to_owned(),
            ToolOutputChunk::Bytes(bytes) => String::from_utf8_lossy(bytes).into_owned(),
        };
        self.output
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push((text, skipped));
        Ok(())
    }

    fn output_window(&self) -> Option<ShellOutputWindow> {
        self.window
    }

    fn retained_output(&self) -> SessionResult<RetainedOutput> {
        let text = self
            .output
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .iter()
            .map(|(text, _)| text.as_str())
            .collect();
        Ok(RetainedOutput {
            text,
            truncated: false,
        })
    }

    fn diagnostic(&self, diagnostic: ToolDiagnostic) -> SessionResult<()> {
        self.diagnostics
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .push(diagnostic);
        Ok(())
    }

    fn details(&self, _value: JsonValue, _cx: &Context) -> BoxFuture<'static, SessionResult<()>> {
        futures::future::ready(Ok(())).boxed()
    }

    fn commit_erased(
        &self,
        _change: ToolCommitChange,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<()>> {
        absent("commit")
    }

    fn memo(
        &self,
        _name: &str,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<JsonValue>>> {
        absent("memo")
    }

    fn memo_or_store(
        &self,
        _name: &str,
        _candidate: JsonValue,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<JsonValue>> {
        absent("memo")
    }

    fn create_task_erased(
        &self,
        _task: AnyTask,
        _input: JsonValue,
        _options: InvocationTaskOptions,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<TaskId>> {
        absent("tasks")
    }

    fn get_task(
        &self,
        _id: TaskId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<AnyTaskRecord>>> {
        absent("tasks")
    }

    fn wait_for_task(
        &self,
        _id: TaskId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<SettledTask>> {
        absent("tasks")
    }

    fn conversation(
        &self,
        _id: ConversationId,
        _cx: &Context,
    ) -> BoxFuture<'static, SessionResult<Option<Arc<dyn ConversationHandle>>>> {
        absent("conversations")
    }

    fn execute_tool(
        &self,
        _name: &str,
        _args: PiJsonObject,
        _cx: &Context,
        _options: ExecuteToolOptions,
    ) -> BoxFuture<'static, SessionResult<NestedToolExecutionResult>> {
        absent("nested tools")
    }
}

/// Execute `tool` with `args` through `api`.
pub(super) async fn execute(
    tool: &ToolRegistration,
    args: PiJsonValue,
    api: &Arc<FakeApi>,
    cx: &Context,
) -> SessionResult<ToolExecutionResult> {
    let api: Arc<dyn ToolExecutionApi> = Arc::clone(api) as Arc<dyn ToolExecutionApi>;
    (tool.execute)(args, api, cx.clone()).await
}

/// Execute with a fresh fake api over `env` in the background context.
pub(super) async fn run(
    tool: &ToolRegistration,
    args: PiJsonValue,
    env: Arc<dyn ExecutionEnv>,
) -> (SessionResult<ToolExecutionResult>, Arc<FakeApi>) {
    let api = FakeApi::new(Some(env));
    let result = execute(tool, args, &api, &BACKGROUND_CONTEXT).await;
    (result, api)
}

pub(super) fn text_output(result: &ToolExecutionResult) -> String {
    result
        .output
        .iter()
        .flatten()
        .filter_map(|part| match part {
            UserContentBlock::Text(text) => Some(text.text.as_str()),
            UserContentBlock::Image(_) => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

pub(super) fn diagnostic_text(result: &ToolExecutionResult) -> String {
    result
        .diagnostics
        .iter()
        .flatten()
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>()
        .join("\n")
}

/// Read a file of `env` as text.
pub(super) async fn read_file(env: &dyn ExecutionEnv, path: &str) -> String {
    env.read_text_file(path, &BACKGROUND_CONTEXT)
        .await
        .expect("read file")
}

/// Write a file of `env`.
pub(super) async fn write_file(env: &dyn ExecutionEnv, path: &str, content: impl AsRef<[u8]>) {
    env.write_file(path, content.as_ref(), &BACKGROUND_CONTEXT)
        .await
        .expect("write file");
}
