# Local models

On-device models for titles, judgments, translation, speech, dictation. Never downloaded automatically.

```sh
eukhe tiny-models                       # list models and state
eukhe tiny-models download lfm2.5-230m  # download one, or all
eukhe translate de hello                # translate to German
eukhe say "hello" [--out a.wav]         # speak, or write a WAV
eukhe transcribe a.wav                  # WAV to text
```

- Text: `lfm2.5-230m`, `lfm2.5-350m`. Speech to text: `whisper-base`, `whisper-small`. Text to speech: `kokoro`.
- Stored in `~/.eukhe/models/tiny/`; download checks size and sha256 per file.
- ONNX Runtime 1.24+. Nix sets `ORT_DYLIB_PATH` to nixpkgs' library; yours wins.

## Roles

A role uses the first available of its model, then its fallbacks (local: installed; provider: the session's model). None: the task fails.

|Role|Task|Default order|
|---|---|---|
|`tiny`|Session titles|`local/lfm2.5-230m`, `local/lfm2.5-350m`, the session's model|
|`judge`|Typed judgments|As `tiny`|
|`translate`|Translation|As `tiny`|
|`speech`|Text to speech|`local/kokoro`|
|`dictation`|Speech to text|`local/whisper-base`, `local/whisper-small`|

|Key|Default|Effect|
|---|---|---|
|`modelRoles.<role>`|none|Role model: `local/<id>` or `provider/model`. `/model` hub roles `titles`, `judge`, `translate`, `speech`, `dictation` set it globally ([settings.md](settings.md#model-roles)); clearing there falls back to the default order|
|`retry.fallbackChains.<role>`|default order|Models after `modelRoles.<role>`; `[]` = only `modelRoles.<role>`|
|`tts.localVoice`|`af_heart`|`eukhe say` voice; `--voice` overrides|
|`stt.enabled`|`false`|Dictation into the editor via `dictation`|
|`providers.tinyRuntimeLibrary`|none|ONNX Runtime library path; none = `ORT_DYLIB_PATH` (global only)|

## Dictation

```sh
set stt.enabled true                 # config.cfg
bind <key> "action app.stt.pushToTalk" # binds.cfg: hold to talk; or action app.stt.toggle; neither bound by default
```

Recorder: first on `PATH` of `pw-record`, `parec`, `arecord` (macOS: `sox`, then `ffmpeg`).
