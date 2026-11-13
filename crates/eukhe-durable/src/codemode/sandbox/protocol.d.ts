// The contract between the VM glue (host.ts, prelude.ts) and the Rust host (vm.rs). vm.rs calls
// the functions below through rquickjs and decodes the bridge text in `decode_bridge`; a change
// here changes vm.rs in the same commit. Rust `Option::None` arrives as `undefined`.

/** A tool the script may call (`VmData::tools_json`). */
type DeclaredTool = { name: string; jsName: string; description: string };

/** A host global the script may call (`VmData::globals_json`); `spread`: every argument is passed. */
type DeclaredGlobal = { name: string; spread: boolean };

/** An output item (`CodemodeOutputItem`): `text()`, `console.*`, or `image()`. */
type OutputKind = "text" | "console" | "image";

/**
 * The prelude's messages to the host, posted as the JSON text `[kind, a, b, c]` (`undefined`
 * becomes `null`) and decoded by `decode_bridge`.
 */
type Bridge = {
  /** A call of a tool or a host global: its id, name, and arguments' JSON (`undefined`: none). */
  (kind: "call" | "global", id: number, name: string, args: string | undefined): void;
  /** An output item: text, or image data and its MIME type. */
  (kind: "output", item: OutputKind, data: string, mimeType?: string): void;
  /**
   * The script ended: completed with its value's JSON (`undefined`: none) and the store writes'
   * JSON, or failed with the error's JSON (`{ name?, message, stack? }`).
   */
  (kind: "done", ok: boolean, payload: string | undefined, writes?: string): void;
};

/** A thrown value, read as an error when it is one. */
type Thrown = { readonly name?: unknown; readonly message?: unknown; readonly stack?: unknown } | null | undefined;

/** What host.ts evaluates to, called with the run's start time (ms) and seed. */
type HostApi = {
  /** The clock while the next result is processed; it never goes back. */
  setNow(ms: number): void;
  /** The prelude's bridge over `post`, which receives each message's JSON text. */
  bridge(post: (text: string) => void): Bridge;
  /** A compile error as `{ name, message, stack }` JSON. */
  describe(error: Thrown): string;
};

/** The script as compiled: `(async (tools, console) => { <code> })`. */
type Script = (tools: object, console: object) => Promise<unknown>;

/**
 * What prelude.ts evaluates to, called with the bridge and the JSON texts of the tools, the
 * globals, and the store (`{ key: <JSON text of the value> }`).
 */
type PreludeApi = {
  /** Settles call `id`: resolves with the value of `payload` JSON, or rejects with an error. */
  settle(id: number, ok: boolean, payload: string | undefined, propertiesJson: string | undefined): void;
  /** Runs the compiled script; its end is reported as `done`. */
  run(fn: Script): void;
  /** Ends a script that waits on nothing that can resume it; whether it did. */
  stalled(): boolean;
};
