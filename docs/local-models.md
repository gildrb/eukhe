# Local models

eukhe can run small models on your computer for titles, judgments,
translation, speech and dictation. eukhe does not download them
automatically:

```sh
eukhe tiny-models                       # list models and their state
eukhe tiny-models download lfm2.5-230m  # download one model, or all
eukhe translate de hello                # translate text to German
eukhe say "hello" [--out a.wav]         # speak text, or write a WAV file
eukhe transcribe a.wav                  # write the text of a WAV file
```

The models are `lfm2.5-230m` and `lfm2.5-350m` (text), `whisper-base` and
`whisper-small` (speech to text), and `kokoro` (text to speech). They go in
`~/.eukhe/models/tiny/`. The download checks the size and the sha256 of each
file. The models need ONNX Runtime 1.24 or newer. The Nix package sets
`ORT_DYLIB_PATH` to the nixpkgs library; your own `ORT_DYLIB_PATH` wins.

Each task has a role. A role uses its model, then its fallback list. It uses
the first model that is available: a local model must be installed, and a
provider model must be the session's model. If no model is available, the
task fails.

|Role|Task|Default order|
|---|---|---|
|`tiny`|Session titles|`local/lfm2.5-230m`, `local/lfm2.5-350m`, the session's model|
|`judge`|Typed judgments|Same as `tiny`|
|`translate`|Translation|Same as `tiny`|
|`speech`|Text to speech|`local/kokoro`|
|`dictation`|Speech to text|`local/whisper-base`, `local/whisper-small`|

|Key|Default|Effect|
|---|---|---|
|`modelRoles.<role>`|none|The model of the role: `local/<id>` or `provider/model`|
|`retry.fallbackChains.<role>`|default order|List of models after `modelRoles.<role>`; `[]` uses only `modelRoles.<role>`|
|`tts.localVoice`|`af_heart`|Voice of `eukhe say`; `--voice` overrides it|
|`stt.enabled`|`false`|Dictation into the editor with the `dictation` role|
|`providers.tinyRuntimeLibrary`|none|Path of the ONNX Runtime library; none uses `ORT_DYLIB_PATH` (global only)|

For dictation, set `stt.enabled true`, then bind `action app.stt.pushToTalk`
(hold the key) or `action app.stt.toggle` in `binds.cfg`. Both are not bound
by default. Recording uses the first of `pw-record`, `parec` and `arecord`
on `PATH` (macOS: `sox`, then `ffmpeg`).
