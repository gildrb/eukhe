// The Settings sections. Controls render from the daemon's values
// (`session.state`, cvars) and re-read them after every change, so a
// reload shows the same thing.

import * as stylex from "@stylexjs/stylex";
import { ArrowLeft, ChevronRight } from "lucide-preact";
import type { ComponentChildren } from "preact";
import { useEffect, useMemo, useState } from "react";
import {
  compactChat,
  listModels,
  modelKey,
  notificationsSupported,
  reloadState,
  setAndReload,
  setModel,
  setPref,
  setThinking,
  setTier,
} from "../lib/actions.ts";
import { dateSpan, fmt } from "../lib/format.ts";
import { request, run } from "../lib/link.ts";
import { useStore, type Frame } from "../lib/store.ts";
import { messageSpeed, modelName } from "../lib/turn.ts";
import type { Model } from "../lib/types.ts";
import { colors, media, radius, size, space, stroke, type, weight } from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import {
  Button,
  CheckRow,
  Labelled,
  MenuSelect,
  Segmented,
  Status,
  TextButton,
  TextField,
} from "./controls.tsx";
import { CopyButton } from "./CopyButton.tsx";
import { serviceTiers, thinkingLevels } from "./ModelMenu.tsx";

const MODES = [
  { value: "one-at-a-time", label: "One at a time" },
  { value: "all", label: "All at once" },
];
const OFF_ON = [
  { value: "off", label: "Off" },
  { value: "on", label: "On" },
];

/** A cvar value as one line. */
const valueText = (value: unknown) => (typeof value === "string" ? value : JSON.stringify(value));
/** `MEMORY_VIEW_CEILING` (eukhe-types/src/daemon/memory.rs): the view's ceiling in bytes. */
const VIEW_CEILING = 128_000;
const EVENTS_SHOWN = 200;

type Result = { text: string; error: boolean } | null;

/** Run `action`; report "Not changed. …" on failure. */
function useAction(): [Result, (action: () => Promise<unknown>, done?: string) => void] {
  const [result, setResult] = useState<Result>(null);
  const perform = (action: () => Promise<unknown>, done = "") => {
    setResult(null);
    action().then(
      () => setResult(done ? { text: done, error: false } : null),
      (error: Error) => setResult({ text: `Not changed. ${error.message}`, error: true }),
    );
  };
  return [result, perform];
}

function Stack({ children }: { children: ComponentChildren }) {
  return <div {...stylex.props(styles.stack)}>{children}</div>;
}

function NoChat() {
  return <p {...stylex.props(ui.tertiary)}>Open a chat to see this.</p>;
}

/** A figures grid: label (tertiary) above value, two columns. */
function Figures({ pairs }: { pairs: [string, string | null | undefined, boolean?][] }) {
  return (
    <dl {...stylex.props(styles.figures)}>
      {pairs.map(([label, value, mono]) => (
        <div key={label} {...stylex.props(styles.figure)}>
          <dt {...stylex.props(ui.small, ui.tertiary)}>{label}</dt>
          <dd
            translate={mono ? false : undefined}
            {...stylex.props(
              mono && value ? ui.mono : ui.figures,
              styles.figureValue,
              mono && styles.monoValue,
            )}
          >
            {value || "–"}
          </dd>
        </div>
      ))}
    </dl>
  );
}

// ---------------------------------------------------------------- general --

export function General() {
  const prefs = useStore((state) => state.prefs);
  const [result, setResult] = useState<Result>(null);
  return (
    <Stack>
      <Labelled label="Theme">
        <Segmented
          label="Theme"
          options={[
            { value: "system", label: "System" },
            { value: "light", label: "Light" },
            { value: "dark", label: "Dark" },
          ]}
          value={prefs.theme}
          onChange={(value) =>
            void setPref("theme", value === "light" || value === "dark" ? value : "system")
          }
        />
      </Labelled>
      <Labelled
        label="Enter key on touch"
        note="On a phone or tablet, Enter either starts a new line or sends. ⌘ or Ctrl with Enter always sends."
      >
        <Segmented
          label="Enter key on touch"
          options={[
            { value: "newline", label: "New line" },
            { value: "send", label: "Send" },
          ]}
          value={prefs.enterSendsOnTouch ? "send" : "newline"}
          onChange={(value) => void setPref("enterSendsOnTouch", value === "send")}
        />
      </Labelled>
      {notificationsSupported() ? (
        <Labelled
          label="Notifications"
          note="While this tab is in the background, eukhe tells you when a reply finishes, fails or needs your approval."
        >
          <Segmented
            label="Notifications"
            options={OFF_ON}
            value={prefs.notify ? "on" : "off"}
            onChange={(value) =>
              void setPref("notify", value === "on").then((ok) =>
                setResult(
                  ok ? null : { text: "The browser did not allow notifications.", error: true },
                ),
              )
            }
          />
        </Labelled>
      ) : (
        <Labelled
          label="Notifications"
          note="This browser cannot show notifications for this page. They need HTTPS, for example through tailscale serve."
        >
          {null}
        </Labelled>
      )}
      {result ? <Status text={result.text} error={result.error} /> : null}
    </Stack>
  );
}

// ------------------------------------------------------------------ model --

function ModelList() {
  const session = useStore((state) => state.session);
  const [models, setModels] = useState<Model[] | null>(null);
  const [catalog, setCatalog] = useState(false);
  const [result, perform] = useAction();
  useEffect(() => {
    listModels(catalog).then(setModels, () => setModels([]));
  }, [catalog]);
  const current = modelKey(session?.state.model);
  return (
    <Labelled label="Model">
      <div role="radiogroup" aria-label="Model" {...stylex.props(styles.rows)}>
        {(models ?? []).map((model) => {
          const key = modelKey(model);
          return (
            <button
              key={key}
              type="button"
              role="radio"
              aria-checked={key === current}
              onClick={() =>
                key === current
                  ? undefined
                  : perform(() => setModel(model), `Now using ${model.name || model.id}.`)
              }
              {...stylex.props(ui.reset, ui.focusRing, styles.row, key === current && styles.rowOn)}
            >
              <span {...stylex.props(ui.ellipsis, styles.grow)}>{model.name || model.id}</span>
              <span translate={false} {...stylex.props(ui.small, ui.tertiary)}>
                {model.provider}
              </span>
            </button>
          );
        })}
        {models && !models.length ? (
          <p {...stylex.props(ui.tertiary)}>No models are available.</p>
        ) : null}
      </div>
      {catalog ? null : <TextButton onClick={() => setCatalog(true)}>All models</TextButton>}
      {result ? <Status text={result.text} error={result.error} /> : null}
    </Labelled>
  );
}

function ScopedModels() {
  const session = useStore((state) => state.session);
  const [models, setModels] = useState<Model[]>([]);
  const [result, perform] = useAction();
  useEffect(() => {
    listModels().then(setModels, () => setModels([]));
  }, []);
  const entries = session?.state.scopedModels ?? [];
  const scoped = new Set(entries.map((entry) => modelKey(entry.model)));
  return (
    <Labelled label="Scoped models" note="The models eukhe cycles through. None means all of them.">
      <div role="group" aria-label="Scoped models" {...stylex.props(styles.checks)}>
        {models.map((model) => {
          const key = modelKey(model);
          const on = scoped.has(key);
          return (
            <CheckRow
              key={key}
              checked={on}
              label={model.name || model.id}
              trail={model.provider}
              onChange={() => {
                const next = on
                  ? entries.filter((entry) => modelKey(entry.model) !== key)
                  : [...entries, { model: { provider: model.provider, id: model.id } }];
                perform(() => setAndReload({ type: "set_scoped_models", scopedModels: next }));
              }}
            />
          );
        })}
      </div>
      {result ? <Status text={result.text} error={result.error} /> : null}
    </Labelled>
  );
}

export function ModelSection() {
  const session = useStore((state) => state.session);
  const [result, perform] = useAction();
  if (!session) return <NoChat />;
  const state = session.state;
  // The daemon's own names, verbatim (as the CLI shows them).
  const levels = thinkingLevels(state).map((level) => ({ value: level, label: level }));
  const tiers = serviceTiers(state).map((tier) => ({ value: tier, label: tier }));
  return (
    <Stack>
      <ModelList />
      {levels.length > 1 ? (
        <Labelled label="Reasoning">
          {levels.length <= 5 ? (
            <Segmented
              label="Reasoning"
              options={levels}
              value={state.thinkingLevel}
              onChange={(level) => perform(() => setThinking(level))}
            />
          ) : (
            <MenuSelect
              label="Reasoning"
              options={levels}
              value={state.thinkingLevel}
              onChange={(level) => perform(() => setThinking(level))}
            />
          )}
        </Labelled>
      ) : null}
      {tiers.length > 1 ? (
        <Labelled label="Service tier">
          <MenuSelect
            label="Service tier"
            options={tiers}
            value={state.serviceTier ?? session.serviceTier ?? undefined}
            onChange={(tier) => perform(() => setTier(tier))}
          />
        </Labelled>
      ) : null}
      {result ? <Status text={result.text} error={result.error} /> : null}
      <ScopedModels />
    </Stack>
  );
}

// --------------------------------------------------------------- behavior --

type Cvars = { values?: { id: string; value: unknown }[] } | null;

export function Behavior() {
  const session = useStore((state) => state.session);
  const linkOpen = useStore((state) => state.link.status === "open");
  const [retry, setRetry] = useState<boolean | undefined>(undefined);
  const [instructions, setInstructions] = useState("");
  const [compacting, setCompacting] = useState<Result>(null);
  const [result, perform] = useAction();
  const sessionId = session?.id;

  const readRetry = () =>
    run<Cvars>({ type: "cvar", line: "" }).then((data) => {
      const found = data?.values?.find((entry) => entry.id === "retry.enabled");
      setRetry(found ? found.value === true : undefined);
    });
  useEffect(() => {
    if (sessionId && linkOpen) void readRetry().catch(() => {});
  }, [sessionId, linkOpen]);

  if (!session) return <NoChat />;
  const state = session.state;
  return (
    <Stack>
      <Labelled
        label="Steering messages"
        note="Messages you steer with while eukhe works: deliver them one at a time, or all at once."
      >
        <Segmented
          label="Steering messages"
          options={MODES}
          value={state.steeringMode}
          onChange={(mode) => perform(() => setAndReload({ type: "set_steering_mode", mode }))}
        />
      </Labelled>
      <Labelled label="Follow-up messages" note="Messages you queue for after the reply.">
        <Segmented
          label="Follow-up messages"
          options={MODES}
          value={state.followUpMode}
          onChange={(mode) => perform(() => setAndReload({ type: "set_follow_up_mode", mode }))}
        />
      </Labelled>
      <Labelled
        label="Compact automatically"
        note="Summarize earlier messages when the context gets full."
      >
        <Segmented
          label="Compact automatically"
          options={OFF_ON}
          value={state.autoCompactionEnabled ? "on" : "off"}
          onChange={(value) =>
            perform(() => setAndReload({ type: "set_auto_compaction", enabled: value === "on" }))
          }
        />
      </Labelled>
      <Labelled label="Retry failed requests">
        {retry === undefined ? (
          <p {...stylex.props(ui.tertiary)}>Reading</p>
        ) : (
          <Segmented
            label="Retry failed requests"
            options={OFF_ON}
            value={retry ? "on" : "off"}
            onChange={(value) =>
              perform(async () => {
                await run({ type: "set_auto_retry", enabled: value === "on" });
                await readRetry();
              })
            }
          />
        )}
      </Labelled>
      {result ? <Status text={result.text} error={result.error} /> : null}
      <Labelled
        label="Compact now"
        note="Summarize the earlier messages now, optionally with instructions."
      >
        <form
          {...stylex.props(styles.inline)}
          onSubmit={(event) => {
            event.preventDefault();
            setCompacting({ text: "Compacting", error: false });
            compactChat(instructions).then(
              (text) => {
                setCompacting({ text, error: false });
                setInstructions("");
              },
              (error: Error) =>
                setCompacting({ text: `Not compacted. ${error.message}`, error: true }),
            );
          }}
        >
          <TextField
            aria-label="Compaction instructions"
            placeholder="Optional instructions"
            value={instructions}
            onInput={(event) => setInstructions(event.currentTarget.value)}
          />
          <Button type="submit">Compact</Button>
        </form>
        {compacting ? <Status text={compacting.text} error={compacting.error} /> : null}
      </Labelled>
    </Stack>
  );
}

// ----------------------------------------------------------------- memory --

type MemoryNode = {
  id: number;
  count: number;
  firstDate?: string;
  lastDate?: string;
  summary?: string | null;
};
type MemoryData = {
  tree?: {
    status?: {
      messages: number;
      lines: number;
      viewBytes: number;
      unsummarized?: number;
      running?: number;
      model?: string;
      lastError?: string;
    };
    level:
      | { kind: "message"; message: { id: number; date: string; text: string } }
      | { kind: "lines"; nodes: MemoryNode[] };
  };
} | null;

export function MemorySection() {
  const session = useStore((state) => state.session);
  const stamp = useStore((state) => state.session?.memory.stamp ?? 0);
  const [path, setPath] = useState<MemoryNode[]>([]);
  const [data, setData] = useState<MemoryData | undefined>(undefined);
  const [error, setError] = useState<string | null>(null);
  const sessionId = session?.id;
  const node = path.at(-1);

  useEffect(() => setPath([]), [sessionId]);
  useEffect(() => {
    if (!sessionId) return undefined;
    let live = true;
    setError(null);
    request<MemoryData>("memory", node ? { node: { id: node.id, count: node.count } } : {}).then(
      (reply) => live && setData(reply),
      (failure: Error) => live && setError(failure.message),
    );
    return () => {
      live = false;
    };
  }, [sessionId, node, stamp]);

  if (!session) return <NoChat />;
  if (error) return <Status text={`Memory did not load. ${error}`} error />;
  if (data === undefined) return <p {...stylex.props(ui.tertiary)}>Reading</p>;
  if (!data?.tree) return <p {...stylex.props(ui.tertiary)}>This chat keeps no memory yet.</p>;
  const { status, level } = data.tree;
  return (
    <Stack>
      {status ? (
        <Figures
          pairs={[
            ["Messages", fmt.num(status.messages)],
            ["Lines", fmt.num(status.lines)],
            ["View", `${fmt.bytes(status.viewBytes)} of ${fmt.bytes(VIEW_CEILING)}`],
            ["Not summarized", fmt.num(status.unsummarized ?? 0)],
            ["Compacting", fmt.num(status.running ?? 0)],
            ["Compactor", status.model || "Default"],
          ]}
        />
      ) : null}
      {status?.lastError ? (
        <Status text={`The compactor failed. ${status.lastError}`} error />
      ) : null}
      {node ? (
        <div {...stylex.props(styles.crumbs)}>
          <button
            type="button"
            onClick={() => setPath(path.slice(0, -1))}
            {...stylex.props(ui.reset, ui.focusRing, styles.back)}
          >
            <ArrowLeft aria-hidden="true" {...stylex.props(ui.iconSmall)} />
            Back
          </button>
          <span {...stylex.props(ui.small, ui.tertiary, ui.figures)}>
            Lines {node.id} to {node.id + node.count - 1}
          </span>
        </div>
      ) : null}
      {level.kind === "message" ? (
        <article {...stylex.props(styles.message)}>
          <p {...stylex.props(ui.small, ui.tertiary, ui.figures)}>
            Message {fmt.num(level.message.id)}, {dateSpan(level.message.date, level.message.date)}
          </p>
          <p {...stylex.props(styles.pre)}>{level.message.text}</p>
          <div>
            <CopyButton text={level.message.text} />
          </div>
        </article>
      ) : level.nodes.length ? (
        <ul {...stylex.props(styles.drill)}>
          {level.nodes.map((child) => (
            <li key={`${child.id}:${child.count}`}>
              <button
                type="button"
                onClick={() => setPath([...path, child])}
                {...stylex.props(ui.reset, ui.focusRing, styles.drillRow)}
              >
                <span {...stylex.props(styles.drillHead)}>
                  <span {...stylex.props(ui.small, ui.figures, ui.strong)}>
                    {child.count === 1
                      ? `Line ${child.id}`
                      : `Lines ${child.id} to ${child.id + child.count - 1}`}
                  </span>
                  <span {...stylex.props(ui.small, ui.tertiary, ui.figures)}>
                    {dateSpan(child.firstDate, child.lastDate)}
                  </span>
                </span>
                <span {...stylex.props(ui.secondary, styles.clamp)}>
                  {child.summary === null || child.summary === undefined
                    ? "Not summarized yet."
                    : child.summary}
                </span>
                <ChevronRight
                  aria-hidden="true"
                  {...stylex.props(ui.icon, ui.tertiary, styles.drillArrow)}
                />
              </button>
            </li>
          ))}
        </ul>
      ) : (
        <p {...stylex.props(ui.tertiary)}>Nothing under this line.</p>
      )}
    </Stack>
  );
}

// ------------------------------------------------------------------ usage --

type Stats = {
  cost: number;
  totalMessages: number;
  tokens: { input: number; output: number; cacheRead: number; cacheWrite: number };
  contextUsage?: { tokens: number; contextWindow: number; percent?: number };
} | null;

export function Usage() {
  const session = useStore((state) => state.session);
  const running = useStore((state) => Boolean(state.session?.turn.running));
  const [stats, setStats] = useState<Stats | undefined>(undefined);
  const [error, setError] = useState<string | null>(null);
  const sessionId = session?.id;
  useEffect(() => {
    if (!sessionId || running) return;
    run<Stats>({ type: "get_session_stats" }).then(setStats, (failure: Error) =>
      setError(failure.message),
    );
  }, [sessionId, running]);
  const calls = useMemo(
    () =>
      session
        ? session.messages
            .filter((message) => message.role === "assistant" && message.usage)
            .toReversed()
        : [],
    [session?.messages],
  );
  if (!session) return <NoChat />;
  if (error) return <Status text={`Usage did not load. ${error}`} error />;
  if (!stats) return <p {...stylex.props(ui.tertiary)}>Reading</p>;
  const context = stats.contextUsage ?? session.state.contextUsage;
  const fraction = context?.contextWindow
    ? Math.min(
        1,
        Math.max(
          0,
          typeof context.percent === "number"
            ? context.percent / 100
            : context.tokens / context.contextWindow,
        ),
      )
    : null;
  return (
    <Stack>
      <Figures
        pairs={[
          ["Cost", fmt.cost(stats.cost)],
          ["Messages", fmt.num(stats.totalMessages)],
          ["Input", fmt.tokens(stats.tokens.input)],
          ["Output", fmt.tokens(stats.tokens.output)],
          ["Cache read", fmt.tokens(stats.tokens.cacheRead)],
          ["Cache write", fmt.tokens(stats.tokens.cacheWrite)],
        ]}
      />
      {context && fraction !== null ? (
        <div {...stylex.props(styles.barBlock)}>
          <p {...stylex.props(ui.small, ui.secondary, ui.figures)}>
            Context {fmt.tokens(context.tokens, false)} of {fmt.tokens(context.contextWindow)},{" "}
            {fmt.percent(fraction)} used
          </p>
          <div
            role="meter"
            aria-label="Context used"
            aria-valuemin={0}
            aria-valuemax={100}
            aria-valuenow={Math.round(fraction * 100)}
            {...stylex.props(styles.bar)}
          >
            <span {...stylex.props(styles.barFill)} style={{ transform: `scaleX(${fraction})` }} />
          </div>
        </div>
      ) : null}
      {calls.length ? (
        <div {...stylex.props(styles.tableFrame)}>
          <table {...stylex.props(styles.table)}>
            <caption {...stylex.props(ui.srOnly)}>Model calls, newest first</caption>
            <thead>
              <tr>
                {["Time", "Model", "In", "Out", "First token", "Speed"].map((label) => (
                  <th key={label} scope="col" {...stylex.props(styles.cell, styles.th)}>
                    {label}
                  </th>
                ))}
              </tr>
            </thead>
            <tbody>
              {calls.slice(0, 200).map((message, index) => {
                const speed = messageSpeed(message);
                return (
                  <tr key={index}>
                    <td {...stylex.props(styles.cell, ui.figures)}>
                      {fmt.time(message.timestamp)}
                    </td>
                    <td translate={false} {...stylex.props(styles.cell)}>
                      {message.responseModel || message.model || "–"}
                    </td>
                    <td {...stylex.props(styles.cell, ui.figures)}>
                      {fmt.tokens(message.usage?.input ?? Number.NaN, false)}
                    </td>
                    <td {...stylex.props(styles.cell, ui.figures)}>
                      {fmt.tokens(message.usage?.output ?? Number.NaN, false)}
                    </td>
                    <td {...stylex.props(styles.cell, ui.figures)}>
                      {typeof speed?.ttftMs === "number" ? fmt.duration(speed.ttftMs) : "–"}
                    </td>
                    <td {...stylex.props(styles.cell, ui.figures)}>
                      {speed?.rate ? fmt.rate(speed.rate) : "–"}
                    </td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>
      ) : (
        <p {...stylex.props(ui.tertiary)}>No model calls yet.</p>
      )}
    </Stack>
  );
}

// --------------------------------------------------------------- advanced --

/** A string or number from a frame, as text; anything else as nothing. */
function wireText(value: unknown): string {
  return typeof value === "string" || typeof value === "number" ? String(value) : "";
}

function frameSummary(frame: Frame): string {
  const data = frame.data;
  const event = data.event as Record<string, unknown> | undefined;
  if (frame.type === "event" && event) {
    if (typeof event.toolName === "string") return event.toolName;
    const stream = event.assistantMessageEvent as { type?: string } | undefined;
    if (stream?.type) return stream.type;
    const message = event.message as { role?: string } | undefined;
    return message?.role ?? "";
  }
  if (frame.type === "reply" || frame.type === "failure") {
    return `request ${wireText(data.id)}${data.error ? ` ${wireText(data.error)}` : ""}`;
  }
  if (frame.dir === "out") {
    return data.op === "run" ? ((data.command as { type?: string } | undefined)?.type ?? "") : "";
  }
  return wireText(data.reason) || wireText(data.error);
}

export function Advanced() {
  const session = useStore((state) => state.session);
  const linkOpen = useStore((state) => state.link.status === "open");
  const framesSeq = useStore((state) => state.framesSeq);
  const frames = useStore((state) => state.frames);
  const [line, setLine] = useState("");
  const [scope, setScope] = useState("session");
  const [values, setValues] = useState<{ id: string; value: unknown }[] | null>(null);
  const [filter, setFilter] = useState("");
  const [result, setResult] = useState<Result>(null);
  const [openFrames, setOpenFrames] = useState<Set<number>>(() => new Set());
  const sessionId = session?.id;

  const adopt = (data: Cvars) => {
    if (data?.values) setValues(data.values.toSorted((a, b) => a.id.localeCompare(b.id)));
  };
  useEffect(() => {
    if (sessionId && linkOpen)
      run<Cvars>({ type: "cvar", line: "" }).then(adopt, (error: Error) =>
        setResult({ text: `Values did not load. ${error.message}`, error: true }),
      );
  }, [sessionId, linkOpen]);

  const shownValues = (values ?? []).filter((entry) => {
    const query = filter.trim().toLowerCase();
    return (
      !query ||
      entry.id.toLowerCase().includes(query) ||
      valueText(entry.value).toLowerCase().includes(query)
    );
  });
  const shownFrames = useMemo(() => frames.slice(-EVENTS_SHOWN).toReversed(), [framesSeq, frames]);

  return (
    <Stack>
      <Labelled
        label="Console"
        note="Write with set <name> <value> or toggle <name>. Tap a value below to start a set line."
      >
        <form
          {...stylex.props(styles.inline)}
          onSubmit={(event) => {
            event.preventDefault();
            const text = line.trim();
            if (!text) return;
            setResult({ text: "Running", error: false });
            run<Cvars>({ type: "cvar", line: text, global: scope === "global" }).then(
              (data) => {
                adopt(data);
                setResult({
                  text:
                    scope === "global"
                      ? "Applied and written to the global config."
                      : "Applied to this chat.",
                  error: false,
                });
                setLine("");
                void reloadState().catch(() => {});
              },
              (error: Error) => setResult({ text: error.message, error: true }),
            );
          }}
        >
          <TextField
            mono
            id="console-line"
            aria-label="Console line"
            placeholder="set retry.enabled false"
            autoCapitalize="off"
            autoCorrect="off"
            spellcheck={false}
            value={line}
            onInput={(event) => setLine(event.currentTarget.value)}
          />
          <Button kind="primary" type="submit">
            Run
          </Button>
        </form>
        <Segmented
          label="Applies to"
          options={[
            { value: "session", label: "This chat" },
            { value: "global", label: "Global" },
          ]}
          value={scope}
          onChange={setScope}
        />
        {result ? <Status text={result.text} error={result.error} /> : null}
        <Button
          onClick={() => {
            run({ type: "cvar_save" }).then(
              () =>
                setResult({ text: "Saved this chat’s values to its agent config.", error: false }),
              (error: Error) => setResult({ text: error.message, error: true }),
            );
          }}
        >
          Save to agent
        </Button>
      </Labelled>
      <Labelled label="Values">
        <TextField
          type="search"
          aria-label="Filter values"
          placeholder="Filter values"
          value={filter}
          onInput={(event) => setFilter(event.currentTarget.value)}
        />
        <ul {...stylex.props(styles.valueList)}>
          {values === null ? <li {...stylex.props(ui.tertiary)}>Reading</li> : null}
          {values !== null && !shownValues.length ? (
            <li {...stylex.props(ui.tertiary)}>No values match.</li>
          ) : null}
          {shownValues.map((entry) => (
            <li key={entry.id}>
              <button
                type="button"
                onClick={() => {
                  setLine(`set ${entry.id} ${valueText(entry.value)}`);
                  document.getElementById("console-line")?.focus();
                }}
                {...stylex.props(ui.reset, ui.focusRing, styles.valueRow)}
              >
                <span translate={false} {...stylex.props(ui.mono, ui.ellipsis, styles.valueId)}>
                  {entry.id}
                </span>
                <span translate={false} {...stylex.props(ui.mono, ui.ellipsis, styles.valueText)}>
                  {valueText(entry.value)}
                </span>
              </button>
            </li>
          ))}
        </ul>
      </Labelled>
      <Labelled
        label="Events"
        note="Every frame between this page and eukhe, newest first. Tap one to see it whole."
      >
        <ul {...stylex.props(styles.valueList)}>
          {shownFrames.map((frame) => {
            const event = frame.data.event as { type?: string } | undefined;
            const kind =
              frame.type === "event" && event?.type
                ? event.type
                : `${frame.dir === "out" ? "sent " : ""}${frame.type}`;
            const open = openFrames.has(frame.seq);
            return (
              <li key={frame.seq}>
                <button
                  type="button"
                  aria-expanded={open}
                  onClick={() => {
                    const next = new Set(openFrames);
                    if (open) next.delete(frame.seq);
                    else next.add(frame.seq);
                    setOpenFrames(next);
                  }}
                  {...stylex.props(ui.reset, ui.focusRing, styles.eventRow)}
                >
                  <span {...stylex.props(ui.small, ui.figures, ui.tertiary)}>
                    {fmt.time(frame.at)}
                  </span>
                  <span translate={false} {...stylex.props(ui.mono, ui.ellipsis, styles.valueId)}>
                    {kind}
                  </span>
                  <span translate={false} {...stylex.props(ui.mono, ui.ellipsis, styles.valueText)}>
                    {frameSummary(frame)}
                  </span>
                </button>
                {open ? (
                  <pre tabIndex={0} translate={false} {...stylex.props(ui.mono, styles.json)}>
                    {JSON.stringify(frame.data, null, 2).slice(0, 20_000)}
                  </pre>
                ) : null}
              </li>
            );
          })}
        </ul>
      </Labelled>
    </Stack>
  );
}

// ------------------------------------------------------------------ about --

export function About() {
  const link = useStore((state) => state.link);
  const session = useStore((state) => state.session);
  const words: Record<string, string> = {
    open: "Connected",
    connecting: "Connecting",
    offline: "Offline",
    unavailable: "eukhe is not running",
  };
  return (
    <Figures
      pairs={[
        ["Build", link.hello?.build ?? "Unknown", true],
        ["Link to eukhe", words[link.status] ?? link.status],
        ["Protocol", link.hello ? String(link.hello.protocol) : "1"],
        ["Chat", session?.id, true],
        ["Folder", session?.state.cwd, true],
        ["Model", session ? modelName(session.state.model) : null],
      ]}
    />
  );
}

const styles = stylex.create({
  stack: { display: "flex", flexDirection: "column", rowGap: space.x8, paddingTop: space.x2 },
  figures: {
    display: "grid",
    gridTemplateColumns: "repeat(2, minmax(0, 1fr))",
    gap: `${space.x5} ${space.x6}`,
    margin: 0,
  },
  figure: { display: "flex", flexDirection: "column", rowGap: space.x1, minWidth: 0 },
  figureValue: { margin: 0, overflowWrap: "anywhere" },
  monoValue: { fontSize: type.small },
  rows: { display: "flex", flexDirection: "column", alignSelf: "stretch" },
  row: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x3,
    minHeight: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x3,
    borderRadius: radius.control,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  rowOn: { backgroundColor: colors.hover, fontWeight: weight.medium },
  grow: { flexGrow: 1 },
  checks: { display: "flex", flexDirection: "column", alignSelf: "stretch" },
  inline: { display: "flex", columnGap: space.x2, alignSelf: "stretch" },
  crumbs: { display: "flex", alignItems: "center", columnGap: space.x4 },
  back: {
    display: "inline-flex",
    alignItems: "center",
    columnGap: space.x1,
    minHeight: { default: size.control, [media.touch]: size.touch },
    color: colors.secondary,
    fontSize: type.small,
  },
  message: { display: "flex", flexDirection: "column", rowGap: space.x2 },
  pre: { whiteSpace: "pre-wrap", overflowWrap: "anywhere" },
  drill: { listStyle: "none", margin: 0, padding: 0 },
  drillRow: {
    display: "grid",
    gridTemplateColumns: "minmax(0, 1fr) auto",
    gridTemplateRows: "auto auto",
    columnGap: space.x3,
    rowGap: space.x1,
    width: "100%",
    paddingBlock: space.x3,
    paddingInline: space.x2,
    borderTopWidth: stroke.hairline,
    borderTopStyle: "solid",
    borderTopColor: colors.hairline,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  drillHead: { display: "flex", columnGap: space.x4, gridColumn: 1 },
  clamp: {
    gridColumn: 1,
    display: "-webkit-box",
    WebkitLineClamp: 2,
    WebkitBoxOrient: "vertical",
    overflow: "hidden",
    fontSize: type.small,
    lineHeight: type.smallLine,
  },
  drillArrow: { gridColumn: 2, gridRow: "1 / span 2", alignSelf: "center" },
  barBlock: { display: "flex", flexDirection: "column", rowGap: space.x2 },
  bar: {
    position: "relative",
    height: stroke.bar,
    backgroundColor: colors.hairline,
    overflow: "hidden",
  },
  barFill: {
    position: "absolute",
    inset: 0,
    backgroundColor: colors.primary,
    transformOrigin: "left center",
  },
  tableFrame: { overflowX: "auto" },
  table: {
    borderCollapse: "collapse",
    width: "100%",
    fontSize: type.small,
    lineHeight: type.smallLine,
  },
  cell: {
    paddingBlock: space.x2,
    paddingInlineEnd: space.x4,
    borderBottomWidth: stroke.hairline,
    borderBottomStyle: "solid",
    borderBottomColor: colors.hairline,
    textAlign: "start",
    whiteSpace: "nowrap",
  },
  th: { fontWeight: weight.medium, color: colors.tertiary },
  valueList: {
    listStyle: "none",
    margin: 0,
    padding: 0,
    alignSelf: "stretch",
    maxHeight: size.pane,
    overflowY: "auto",
  },
  valueRow: {
    display: "grid",
    gridTemplateColumns: "minmax(0, 1fr) minmax(0, 1fr)",
    columnGap: space.x4,
    alignItems: "center",
    width: "100%",
    minHeight: { default: size.item, [media.touch]: size.touch },
    paddingInline: space.x2,
    borderRadius: radius.control,
    fontSize: type.small,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  valueId: { fontSize: type.small, color: colors.primary },
  valueText: { fontSize: type.small, color: colors.tertiary },
  eventRow: {
    display: "grid",
    gridTemplateColumns: "auto minmax(0, 1fr) minmax(0, 1fr)",
    columnGap: space.x3,
    alignItems: "center",
    width: "100%",
    minHeight: { default: size.item, [media.touch]: size.touch },
    paddingInline: space.x2,
    borderRadius: radius.control,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  json: {
    margin: 0,
    marginBlock: space.x2,
    padding: space.x3,
    maxHeight: size.pane,
    overflow: "auto",
    borderRadius: radius.control,
    backgroundColor: colors.surface,
    fontSize: type.tiny,
    lineHeight: type.smallLine,
  },
});
