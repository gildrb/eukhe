// The conversation: turns (the user's bubble, then the assistant's
// thinking, tools and text in order, then a meta row), the streaming
// message, the one activity line, the approval card, pending and queued
// messages, and "Latest" when scrolled up. It sticks to the bottom only
// while the reader is there.

import * as Collapsible from "@radix-ui/react-collapsible";
import * as stylex from "@stylexjs/stylex";
import { ArrowDown, ChevronDown } from "lucide-preact";
import type { ComponentChildren } from "preact";
import { memo, useEffect, useLayoutEffect, useRef, useState } from "react";
import { dropPending, retryLast, send, unqueue } from "../lib/actions.ts";
import { fmt } from "../lib/format.ts";
import { request, run } from "../lib/link.ts";
import { answerApproval, bind } from "../lib/session.ts";
import { store, useStore } from "../lib/store.ts";
import {
  basename,
  contentText,
  derivePhase,
  effectWords,
  messageSpeed,
  toolTarget,
  withoutSignalRules,
  type Approval,
  type Note,
  type Pending,
  type Session,
  type Tool,
} from "../lib/turn.ts";
import type { ContentBlock, Message } from "../lib/types.ts";
import {
  colors,
  layer,
  media,
  motion,
  opacity,
  radius,
  shadows,
  size,
  space,
  stroke,
  type,
  weight,
} from "../tokens.stylex.ts";
import { ui } from "../ui.ts";
import { fillComposer } from "./Composer.tsx";
import { Button, TextButton } from "./controls.tsx";
import { CopyButton } from "./CopyButton.tsx";
import { Prose } from "./Markdown.tsx";

const STICK_PX = 48;
const TAIL_LINES = 3;

/** Thinking time per streamed block, measured live (history has none). */
const thinkingMs = new Map<string, number>();

const blockKey = (message: Message, index: number) => `${String(message.timestamp)}:${index}`;

function outputText(output: unknown): string {
  if (!output) return "";
  if (typeof output === "string") return output;
  if (typeof output === "object" && output !== null && "content" in output)
    return contentText(output.content);
  return contentText(output);
}

function argsText(args: unknown): string {
  if (args === null || args === undefined) return "";
  if (typeof args === "string") return args;
  if (typeof args === "object") {
    const values = Object.values(args);
    if (values.length === 1 && typeof values[0] === "string") return values[0];
  }
  return JSON.stringify(args, null, 2);
}

type ToolResult = Message & { role: "toolResult" };

function resolveTool(
  call: { id: string; name: string; arguments: unknown },
  session: Session,
  results: Map<string, Message>,
): Tool {
  const live = session.tools[call.id];
  const result = results.get(call.id) as ToolResult | undefined;
  const tool: Tool = {
    id: call.id,
    name: call.name,
    args: call.arguments,
    status: "waiting",
    partial: null,
    result: null,
    isError: false,
    startedAt: 0,
    endedAt: 0,
  };
  if (live)
    Object.assign(tool, live, { args: live.args ?? call.arguments, name: live.name || call.name });
  if (result) {
    tool.status = result.isError ? "failed" : "done";
    tool.result = { content: result.content };
    if (typeof result.durationMs === "number") tool.durationMs = result.durationMs;
  }
  if (tool.status === "waiting" && !session.turn.running) tool.status = "stopped";
  return tool;
}

function toolState(tool: Tool, now: number): string {
  switch (tool.status) {
    case "running":
      return fmt.clock(now - tool.startedAt);
    case "failed":
      return "Failed";
    case "stopped":
      return "Stopped";
    case "waiting":
      return "Waiting";
    default:
      if (tool.durationMs !== undefined) return fmt.duration(tool.durationMs);
      return tool.startedAt && tool.endedAt >= tool.startedAt
        ? fmt.duration(tool.endedAt - tool.startedAt)
        : "";
  }
}

// ------------------------------------------------------------- pieces --

function Disclosure({
  label,
  extra,
  children,
  defaultOpen = false,
}: {
  label: ComponentChildren;
  extra?: string;
  children: ComponentChildren;
  defaultOpen?: boolean;
}) {
  const [open, setOpen] = useState(defaultOpen);
  return (
    <Collapsible.Root open={open} onOpenChange={setOpen}>
      <Collapsible.Trigger asChild>
        <button type="button" {...stylex.props(ui.reset, ui.focusRing, styles.disclosure)}>
          <span>{label}</span>
          {extra ? <span {...stylex.props(styles.extra)}>{extra}</span> : null}
          <ChevronDown
            aria-hidden="true"
            {...stylex.props(ui.iconSmall, styles.chevron, open && styles.chevronOpen)}
          />
        </button>
      </Collapsible.Trigger>
      <Collapsible.Content>{children}</Collapsible.Content>
    </Collapsible.Root>
  );
}

function Thinking({ text, label }: { text: string; label: string }) {
  return (
    <Disclosure label={label}>
      <div {...stylex.props(styles.thinking)}>{text}</div>
    </Disclosure>
  );
}

function MonoBlock({ title, text }: { title: string; text: string }) {
  return (
    <div {...stylex.props(styles.mono)}>
      <div {...stylex.props(styles.monoHead)}>
        <span>{title}</span>
        <CopyButton text={text} />
      </div>
      <pre tabIndex={0} translate={false} {...stylex.props(ui.mono, styles.monoText)}>
        {text}
      </pre>
    </div>
  );
}

function ToolRow({ tool, now }: { tool: Tool; now: number }) {
  const [open, setOpen] = useState(false);
  const output = tool.result
    ? outputText(tool.result)
    : tool.partial
      ? outputText(tool.partial)
      : "";
  const tail =
    !open && tool.status === "running" && output
      ? output.replace(/\s+$/, "").split("\n").slice(-TAIL_LINES).join("\n")
      : "";
  return (
    <Collapsible.Root open={open} onOpenChange={setOpen} {...stylex.props(styles.tool)}>
      <Collapsible.Trigger asChild>
        <button type="button" {...stylex.props(ui.reset, ui.focusRing, styles.toolRow)}>
          <span translate={false} {...stylex.props(ui.mono, styles.toolName)}>
            {tool.name}
          </span>
          <span translate={false} {...stylex.props(ui.mono, ui.ellipsis, styles.toolTarget)}>
            {toolTarget(tool.args)}
          </span>
          <span
            {...stylex.props(
              ui.figures,
              styles.toolState,
              tool.status === "failed" && styles.failed,
            )}
          >
            {toolState(tool, now)}
          </span>
        </button>
      </Collapsible.Trigger>
      {tail ? (
        <pre aria-hidden="true" translate={false} {...stylex.props(ui.mono, styles.tail)}>
          {tail}
        </pre>
      ) : null}
      <Collapsible.Content {...stylex.props(styles.toolDetails)}>
        <MonoBlock title="Arguments" text={argsText(tool.args)} />
        <MonoBlock
          title="Output"
          text={output || (tool.status === "running" ? "" : "No output.")}
        />
      </Collapsible.Content>
    </Collapsible.Root>
  );
}

function ToolList({ tools, settled, now }: { tools: Tool[]; settled: boolean; now: number }) {
  const rows = (
    <div {...stylex.props(styles.toolList)}>
      {tools.map((tool) => (
        <ToolRow key={tool.id} tool={tool} now={now} />
      ))}
    </div>
  );
  if (!settled) return rows;
  const failed = tools.filter((tool) => tool.status === "failed").length;
  return (
    <Disclosure
      label={`Used ${fmt.num(tools.length)} ${tools.length === 1 ? "tool" : "tools"}`}
      extra={failed ? `${fmt.num(failed)} failed` : ""}
    >
      {rows}
    </Disclosure>
  );
}

function Bubble({
  text,
  images = [],
  origin,
  pending = false,
  label,
  children,
}: {
  text: string;
  images?: { src: string }[];
  origin?: string;
  pending?: boolean;
  label?: string;
  children?: ComponentChildren;
}) {
  return (
    <div {...stylex.props(styles.bubbleRow)}>
      <div {...stylex.props(styles.bubble, pending && styles.pendingBubble)}>
        {origin ? <span {...stylex.props(ui.small, ui.tertiary)}>{origin}</span> : null}
        {images.length ? (
          <div {...stylex.props(styles.bubbleImages)}>
            {images.map((image, index) => (
              <img
                key={index}
                src={image.src}
                alt="Attached image"
                loading="lazy"
                decoding="async"
                {...stylex.props(styles.bubbleImage)}
              />
            ))}
          </div>
        ) : null}
        {text ? <p {...stylex.props(styles.bubbleText)}>{text}</p> : null}
      </div>
      {label || children ? (
        <div {...stylex.props(ui.small, styles.bubbleMeta)}>
          {label ? <span>{label}</span> : null}
          {children}
        </div>
      ) : null}
    </div>
  );
}

// -------------------------------------------------------------- turns --

type TurnGroup = { start: number; messages: Message[] };

function groupTurns(messages: Message[]): TurnGroup[] {
  const turns: TurnGroup[] = [];
  let turn: TurnGroup | null = null;
  messages.forEach((message, index) => {
    const starts =
      message.role === "user" ||
      message.role === "bashExecution" ||
      (message.role === "custom" && message.customType === "signal" && message.display !== false);
    if (starts || !turn) {
      turn = { start: index, messages: [] };
      turns.push(turn);
    }
    turn.messages.push(message);
  });
  return turns;
}

type Item =
  | { kind: "text"; text: string }
  | { kind: "thinking"; text: string; key: string }
  | { kind: "tool"; tool: Tool };

function assistantItems(message: Message, session: Session, results: Map<string, Message>): Item[] {
  const blocks: ContentBlock[] = Array.isArray(message.content)
    ? message.content
    : [{ type: "text", text: message.content ?? "" }];
  const items: Item[] = [];
  blocks.forEach((block, index) => {
    if (block.type === "text" && block.text.trim()) items.push({ kind: "text", text: block.text });
    else if (block.type === "thinking" && block.thinking.trim()) {
      items.push({ kind: "thinking", text: block.thinking, key: blockKey(message, index) });
    } else if (block.type === "toolCall")
      items.push({ kind: "tool", tool: resolveTool(block, session, results) });
  });
  return items;
}

function Items({ items, settled, now }: { items: Item[]; settled: boolean; now: number }) {
  const out: ComponentChildren[] = [];
  let tools: Tool[] = [];
  const flush = () => {
    if (!tools.length) return;
    const allSettled =
      settled && tools.every((tool) => tool.status !== "running" && tool.status !== "waiting");
    out.push(
      <ToolList key={`tools:${tools[0]?.id}`} tools={tools} settled={allSettled} now={now} />,
    );
    tools = [];
  };
  items.forEach((item, index) => {
    if (item.kind === "tool") {
      tools.push(item.tool);
      return;
    }
    flush();
    if (item.kind === "text") out.push(<Prose key={`text:${index}`} text={item.text} />);
    else {
      const known = thinkingMs.get(item.key);
      out.push(
        <Thinking
          key={item.key}
          text={item.text}
          label={known ? `Thought for ${fmt.duration(known)}` : "Thoughts"}
        />,
      );
    }
  });
  flush();
  return <>{out}</>;
}

/** The streaming assistant message: text renders as it comes, thinking times itself. */
function Live({
  message,
  now,
  session,
  results,
}: {
  message: Message;
  now: number;
  session: Session;
  results: Map<string, Message>;
}) {
  const started = useRef(new Map<string, number>());
  const blocks = Array.isArray(message.content) ? message.content : [];
  return (
    <>
      {blocks.map((block, index) => {
        const key = blockKey(message, index);
        if (!started.current.has(key)) started.current.set(key, now);
        const last = index === blocks.length - 1;
        if (block.type === "text") return <Prose key={key} text={block.text} streaming={last} />;
        if (block.type === "thinking") {
          if (!last && !thinkingMs.has(key))
            thinkingMs.set(key, now - (started.current.get(key) ?? now));
          const known = thinkingMs.get(key);
          return (
            <Thinking
              key={key}
              text={block.thinking}
              label={last || !known ? "Thinking" : `Thought for ${fmt.duration(known)}`}
            />
          );
        }
        if (block.type === "toolCall" && block.id) {
          return (
            <div key={key} {...stylex.props(styles.toolList)}>
              <ToolRow tool={resolveTool(block, session, results)} now={now} />
            </div>
          );
        }
        return null;
      })}
    </>
  );
}

function MetaRow({
  messages,
  isLast,
  failed,
}: {
  messages: Message[];
  isLast: boolean;
  failed: boolean;
}) {
  const last = messages.findLast((message) => message.role === "assistant");
  if (!last) return null;
  const text = messages
    .filter((message) => message.role === "assistant")
    .map((message) => contentText(message.content))
    .filter(Boolean)
    .join("\n\n");
  const speed = messageSpeed(last);
  return (
    <div {...stylex.props(ui.small, styles.meta)}>
      {text ? <CopyButton text={text} /> : null}
      {isLast && failed ? <TextButton onClick={retryLast}>Retry</TextButton> : null}
      <span {...stylex.props(styles.metaEnd)}>
        {speed?.rate ? <span {...stylex.props(ui.figures)}>{fmt.rate(speed.rate)}</span> : null}
        {last.timestamp ? (
          <span {...stylex.props(ui.figures)}>{fmt.time(last.timestamp)}</span>
        ) : null}
      </span>
    </div>
  );
}

function ErrorLine({ text, retry }: { text: string; retry: boolean }) {
  return (
    <div role="alert" {...stylex.props(styles.error)}>
      <p>Something went wrong. {text}</p>
      {retry ? (
        <TextButton strong onClick={retryLast}>
          Retry
        </TextButton>
      ) : null}
    </div>
  );
}

type TurnProps = {
  turn: TurnGroup;
  isLast: boolean;
  session: Session;
  results: Map<string, Message>;
  notes: Note[];
  now: number;
  /** Changes whenever the turn must render again. */
  signature: string;
};

const TurnView = memo(
  function TurnView({ turn, isLast, session, results, notes, now }: TurnProps) {
    const running = isLast && session.turn.running;
    const head: ComponentChildren[] = [];
    const answer: ComponentChildren[] = [];
    let items: Item[] = [];
    let lastAssistant: Message | null = null;
    const flush = () => {
      if (items.length)
        answer.push(
          <Items key={`items:${answer.length}`} items={items} settled={!running} now={now} />,
        );
      items = [];
    };
    for (const message of turn.messages) {
      switch (message.role) {
        case "user": {
          const text = withoutSignalRules(contentText(message.content));
          const images = Array.isArray(message.content)
            ? message.content
                .filter(
                  (block): block is ContentBlock & { type: "image" } =>
                    block.type === "image" && Boolean(block.data),
                )
                .map((block) => ({ src: `data:${block.mimeType};base64,${block.data}` }))
            : [];
          if (text.trim() || images.length)
            head.push(<Bubble key={`user:${head.length}`} text={text} images={images} />);
          break;
        }
        case "custom": {
          const text = contentText(message.content);
          if (message.display === false || !text.trim()) break;
          flush();
          if (message.customType === "signal") {
            head.push(<Bubble key={`signal:${head.length}`} text={text} origin="From Signal" />);
          } else {
            const words =
              (message.customType ?? "note").split(".").pop()?.replace(/[_-]+/g, " ").trim() ||
              "Note";
            answer.push(
              <Disclosure
                key={`custom:${answer.length}`}
                label={words.charAt(0).toUpperCase() + words.slice(1)}
              >
                <div {...stylex.props(styles.nested)}>
                  <Prose text={text} />
                </div>
              </Disclosure>,
            );
          }
          break;
        }
        case "assistant":
          items.push(...assistantItems(message, session, results));
          lastAssistant = message;
          break;
        case "bashExecution": {
          flush();
          const failed = typeof message.exitCode === "number" && message.exitCode !== 0;
          const tool: Tool = {
            id: `bash:${String(message.timestamp)}`,
            name: "shell",
            args: { command: message.command },
            status: message.cancelled ? "stopped" : failed ? "failed" : "done",
            partial: null,
            result: { content: [{ type: "text", text: message.output ?? "" }] },
            isError: failed,
            startedAt: 0,
            endedAt: 0,
          };
          answer.push(<ToolList key={tool.id} tools={[tool]} settled={false} now={now} />);
          break;
        }
        case "compactionSummary":
        case "branchSummary":
          flush();
          answer.push(
            <Disclosure
              key={`summary:${answer.length}`}
              label={
                message.role === "compactionSummary"
                  ? "Earlier messages compacted"
                  : "Branch summary"
              }
            >
              <div {...stylex.props(styles.thinking)}>{message.summary ?? ""}</div>
            </Disclosure>,
          );
          break;
        default:
          break;
      }
    }
    flush();
    if (isLast && session.live) {
      answer.push(
        <Live key="live" message={session.live} now={now} session={session} results={results} />,
      );
    }
    let failed = false;
    const finished = lastAssistant;
    if (finished && !running) {
      if (finished.stopReason === "error") {
        failed = true;
        answer.push(
          <ErrorLine
            key="error"
            text={finished.errorMessage || "The model request failed."}
            retry={isLast}
          />,
        );
      } else if (finished.stopReason === "aborted") {
        answer.push(
          <p key="stopped" {...stylex.props(ui.small, ui.tertiary)}>
            Stopped
          </p>,
        );
      }
    }
    if (isLast && !running && session.turn.error && !failed) {
      failed = true;
      answer.push(<ErrorLine key="turn-error" text={session.turn.error} retry />);
    }
    for (const [index, item] of notes.entries()) {
      answer.push(
        <p
          key={`note:${index}`}
          {...stylex.props(ui.small, item.kind === "error" ? styles.failed : ui.tertiary)}
        >
          {item.text}
        </p>,
      );
    }
    if (!running)
      answer.push(<MetaRow key="meta" messages={turn.messages} isLast={isLast} failed={failed} />);
    return (
      <article {...stylex.props(styles.turn)}>
        {head}
        {answer.length ? <div {...stylex.props(styles.answer)}>{answer}</div> : null}
      </article>
    );
  },
  (before, after) => before.signature === after.signature && before.isLast === after.isLast,
);

function turnSignature(
  turn: TurnGroup,
  session: Session,
  isLast: boolean,
  notes: Note[],
  results: Map<string, Message>,
  tick: number,
): string {
  if (!isLast) return `${turn.messages.length}|${notes.length}|${results.size}`;
  return [
    turn.messages.length,
    notes.length,
    results.size,
    session.turn.running,
    session.turn.error ?? "",
    session.live
      ? `${session.live.timestamp}:${contentText(session.live.content).length}:${JSON.stringify(session.live.content).length}`
      : "",
    Object.values(session.tools)
      .map((tool) => `${tool.id}:${tool.status}:${tool.updatedAt ?? 0}`)
      .join(","),
    session.turn.running ? tick : 0,
  ].join("|");
}

// ----------------------------------------------------------- the tail --

function ApprovalCard({ item }: { item: Approval }) {
  const busy = item.status === "answering";
  const card = useRef<HTMLDivElement>(null);
  if (item.status === "elsewhere") {
    return <p {...stylex.props(ui.small, ui.tertiary)}>Answered in another window</p>;
  }
  return (
    <div
      ref={card}
      role="group"
      tabIndex={-1}
      aria-label="Approve this command?"
      aria-keyshortcuts="A D"
      onKeyDown={(event) => {
        if (busy || (event.target instanceof HTMLButtonElement && event.key === "Enter")) return;
        const key = event.key.toLowerCase();
        if (key === "a") void answerApproval(item.requestId, "approve");
        else if (key === "d") void answerApproval(item.requestId, "deny");
      }}
      {...stylex.props(ui.focusRing, styles.approval)}
    >
      <p {...stylex.props(ui.strong)}>Approve this command?</p>
      <pre translate={false} {...stylex.props(ui.mono, styles.approvalCommand)}>
        {item.command}
      </pre>
      <p {...stylex.props(ui.small, styles.approvalEffect)}>{effectWords(item.effect)}</p>
      <div {...stylex.props(styles.approvalButtons)}>
        <button
          type="button"
          disabled={busy}
          onClick={() => void answerApproval(item.requestId, "deny")}
          {...stylex.props(ui.reset, styles.approvalButton)}
        >
          Deny
        </button>
        <button
          type="button"
          disabled={busy}
          onClick={() => void answerApproval(item.requestId, "approve")}
          {...stylex.props(ui.reset, styles.approvalButton, styles.approve)}
        >
          Approve
        </button>
      </div>
    </div>
  );
}

function notice(text: string) {
  store.set({ notice: text });
}

function editQueued(lane: "steering" | "followUp", index: number, text: string) {
  unqueue(lane, index, text).then(
    (taken) => fillComposer(taken),
    (error: Error) => notice(`Not editable. ${error.message}`),
  );
}

function removeQueued(lane: "steering" | "followUp", index: number, text: string) {
  unqueue(lane, index, text).catch((error: Error) => notice(`Not removed. ${error.message}`));
}

function PendingList({ session }: { session: Session }) {
  const queue = session.queue;
  return (
    <>
      {session.pending.map((item: Pending) =>
        item.status === "failed" ? (
          <Bubble key={item.admissionId} text={item.text} pending label="Not sent">
            <TextButton
              strong
              onClick={() =>
                void send({
                  ...item,
                  queued: session.turn.running,
                  mode: session.turn.running ? item.mode : "followUp",
                })
              }
            >
              Retry
            </TextButton>
            <TextButton
              onClick={() => {
                dropPending(item);
                fillComposer(item.text, item.images);
              }}
            >
              Edit
            </TextButton>
          </Bubble>
        ) : (
          <Bubble
            key={item.admissionId}
            text={item.text}
            pending
            label={item.status === "held" ? "Sends when eukhe is back" : "Sending"}
          />
        ),
      )}
      {queue.steering.map((item, index) => (
        <Bubble
          key={`steer:${index}:${item.text}`}
          text={item.text}
          pending
          label="Steering, sends at the next step"
        >
          <TextButton onClick={() => editQueued("steering", index, item.text)}>Edit</TextButton>
          <TextButton onClick={() => removeQueued("steering", index, item.text)}>Remove</TextButton>
        </Bubble>
      ))}
      {queue.followUps.map((item, index) => (
        <Bubble
          key={`queue:${index}:${item.text}`}
          text={item.text}
          pending
          label="Queued, sends after this reply"
        >
          <TextButton onClick={() => editQueued("followUp", index, item.text)}>Edit</TextButton>
          <TextButton onClick={() => removeQueued("followUp", index, item.text)}>Remove</TextButton>
        </Bubble>
      ))}
    </>
  );
}

function Center({
  title,
  body,
  action,
}: {
  title: string;
  body?: string;
  action?: ComponentChildren;
}) {
  return (
    <div {...stylex.props(styles.center)}>
      <h1 {...stylex.props(ui.title)}>{title}</h1>
      {body ? <p {...stylex.props(ui.tertiary)}>{body}</p> : null}
      {action}
    </div>
  );
}

// ------------------------------------------------------- conversation --

export function Conversation({ routeId }: { routeId: string | null }) {
  const session = useStore((state) => state.session);
  const approvals = useStore((state) => state.approvals);
  const link = useStore((state) => state.link);
  const opening = useStore((state) => state.opening);
  const tick = useStore((state) => state.tick);
  const noticeText = useStore((state) => state.notice);
  const scroller = useRef<HTMLDivElement>(null);
  const column = useRef<HTMLDivElement>(null);
  const pinned = useRef(true);
  const [showLatest, setShowLatest] = useState(false);
  const shown = session && (!routeId || session.id === routeId) ? session : null;
  const now = Date.now();

  useLayoutEffect(() => {
    const box = scroller.current;
    if (box && pinned.current) box.scrollTop = box.scrollHeight;
  });
  useEffect(() => {
    const box = scroller.current;
    const content = column.current;
    if (!box || !content) return undefined;
    const follow = new ResizeObserver(() => {
      if (pinned.current) box.scrollTop = box.scrollHeight;
    });
    follow.observe(content);
    follow.observe(box);
    return () => follow.disconnect();
  }, [shown?.id]);
  useEffect(() => {
    pinned.current = true;
    setShowLatest(false);
  }, [shown?.id]);

  let body: ComponentChildren;
  if (!shown) {
    if (opening?.error) {
      body = (
        <Center
          title="This chat did not open."
          body={opening.error}
          action={
            <Button onClick={() => void bind(routeId, true).catch(() => {})}>Try again</Button>
          }
        />
      );
    } else if (!link.everOpen && (link.status === "offline" || link.status === "unavailable")) {
      body = (
        <Center title="eukhe is not reachable" body="This page connects on its own once it is." />
      );
    } else body = null;
  } else {
    const results = new Map<string, Message>();
    for (const message of shown.messages)
      if (message.role === "toolResult" && message.toolCallId)
        results.set(message.toolCallId, message);
    const turns = groupTurns(shown.messages);
    const empty = !turns.length && !shown.live && !shown.pending.length && !shown.queue.queuedCount;
    const notesByTurn = new Map<number, Note[]>();
    for (const item of shown.notes) {
      const owner =
        turns.findLast((turn) => turn.start < Math.max(item.index, 1)) ?? turns[turns.length - 1];
      const key = owner ? owner.start : -1;
      notesByTurn.set(key, [...(notesByTurn.get(key) ?? []), item]);
    }
    const phase = derivePhase({ session: shown, approvals }, now, fmt);
    const folder = basename(shown.state.cwd);
    body = empty ? (
      <Center title="What should eukhe do?" body={folder ? `in ${folder}` : ""} />
    ) : (
      <div ref={column} {...stylex.props(styles.column)}>
        {turns.map((turn, index) => {
          const isLast = index === turns.length - 1;
          const notes = notesByTurn.get(turn.start) ?? [];
          return (
            <TurnView
              key={turn.start}
              turn={turn}
              isLast={isLast}
              session={shown}
              results={results}
              notes={notes}
              now={now}
              signature={turnSignature(turn, shown, isLast, notes, results, tick)}
            />
          );
        })}
        {phase.running ? (
          <div role="status" {...stylex.props(styles.activity)}>
            <span {...stylex.props(ui.shimmer)}>{phase.label}</span>
            {phase.action ? (
              <TextButton
                onClick={() =>
                  void run({
                    type: phase.action === "cancelRetry" ? "abort_retry" : "abort_compaction",
                  }).catch((error: Error) => notice(error.message))
                }
              >
                Cancel
              </TextButton>
            ) : null}
          </div>
        ) : null}
        {approvals.map((item) => (
          <ApprovalCard key={item.requestId} item={item} />
        ))}
        <PendingList session={shown} />
        {noticeText ? (
          <p role="alert" {...stylex.props(ui.small, styles.notice)}>
            <span>{noticeText}</span>
            <TextButton onClick={() => store.set({ notice: null })}>Dismiss</TextButton>
          </p>
        ) : null}
      </div>
    );
  }

  return (
    <div {...stylex.props(styles.stage)}>
      <div
        ref={scroller}
        tabIndex={-1}
        role="log"
        aria-label="Conversation"
        onScroll={(event) => {
          const box = event.currentTarget;
          const distance = box.scrollHeight - box.scrollTop - box.clientHeight;
          pinned.current = distance <= STICK_PX;
          setShowLatest(!pinned.current);
        }}
        {...stylex.props(styles.scroller)}
      >
        {body}
      </div>
      {showLatest && shown ? (
        <button
          type="button"
          onClick={() => {
            const box = scroller.current;
            if (!box) return;
            pinned.current = true;
            box.scrollTo({
              top: box.scrollHeight,
              behavior: matchMedia("(prefers-reduced-motion: reduce)").matches
                ? "instant"
                : "smooth",
            });
          }}
          {...stylex.props(ui.reset, ui.focusRing, styles.latest)}
        >
          Latest
          <ArrowDown aria-hidden="true" {...stylex.props(ui.iconSmall)} />
        </button>
      ) : null}
    </div>
  );
}

/** Stop the running turn (Esc, or the composer's Stop). */
export function stopTurn(): void {
  request("abort").catch((error: Error) => notice(`Not stopped. ${error.message}`));
}

const styles = stylex.create({
  stage: {
    position: "relative",
    flexGrow: 1,
    minHeight: 0,
    display: "flex",
    flexDirection: "column",
  },
  scroller: {
    flexGrow: 1,
    minHeight: 0,
    overflowY: "auto",
    overflowX: "hidden",
    overscrollBehavior: "contain",
    outline: "none",
    display: "flex",
    flexDirection: "column",
  },
  column: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x8,
    width: "100%",
    maxWidth: size.column,
    marginInline: "auto",
    paddingInline: { default: space.x6, [media.phone]: space.x4 },
    paddingTop: space.x4,
    paddingBottom: space.x8,
  },
  center: {
    margin: "auto",
    display: "flex",
    flexDirection: "column",
    alignItems: "center",
    rowGap: space.x2,
    paddingInline: space.x6,
    textAlign: "center",
  },
  turn: { display: "flex", flexDirection: "column", rowGap: space.x4, minWidth: 0 },
  answer: { display: "flex", flexDirection: "column", rowGap: space.x4, minWidth: 0 },
  bubbleRow: { display: "flex", flexDirection: "column", alignItems: "flex-end", rowGap: space.x1 },
  bubble: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x2,
    maxWidth: { default: "80%", [media.phone]: "88%" },
    paddingBlock: space.x25,
    paddingInline: space.x4,
    borderRadius: radius.bubble,
    backgroundColor: colors.surface,
    color: colors.primary,
    minWidth: 0,
  },
  pendingBubble: { opacity: opacity.dim },
  bubbleText: { whiteSpace: "pre-wrap", overflowWrap: "anywhere" },
  bubbleImages: { display: "flex", flexWrap: "wrap", gap: space.x2 },
  bubbleImage: {
    display: "block",
    maxWidth: "100%",
    maxHeight: size.image,
    borderRadius: radius.control,
  },
  bubbleMeta: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x4,
    color: colors.tertiary,
  },
  disclosure: {
    display: "inline-flex",
    alignItems: "center",
    columnGap: space.x2,
    minHeight: { default: size.control, [media.touch]: size.touch },
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: { default: colors.secondary, ":hover": { [media.hover]: colors.primary } },
    borderRadius: radius.control,
  },
  extra: { color: colors.tertiary },
  chevron: { transition: `transform ${motion.fast} ease-out`, transform: "rotate(-90deg)" },
  chevronOpen: { transform: "rotate(0deg)" },
  thinking: {
    marginTop: space.x2,
    paddingInlineStart: space.x3,
    borderInlineStartWidth: stroke.hairline,
    borderInlineStartStyle: "solid",
    borderInlineStartColor: colors.hairline,
    fontSize: type.small,
    lineHeight: type.blockLine,
    color: colors.secondary,
    whiteSpace: "pre-wrap",
    overflowWrap: "anywhere",
  },
  nested: { marginTop: space.x2 },
  toolList: { display: "flex", flexDirection: "column", marginTop: space.x1 },
  tool: {
    borderTopWidth: stroke.hairline,
    borderTopStyle: "solid",
    borderTopColor: colors.hairline,
  },
  toolRow: {
    display: "grid",
    gridTemplateColumns: "auto minmax(0, 1fr) auto",
    alignItems: "center",
    columnGap: space.x4,
    width: "100%",
    minHeight: { default: size.row, [media.touch]: size.touch },
    paddingInline: space.x2,
    borderRadius: radius.control,
    backgroundColor: { default: "transparent", ":hover": { [media.hover]: colors.hover } },
  },
  toolName: { fontSize: type.small, color: colors.secondary },
  toolTarget: { fontSize: type.small, color: colors.tertiary },
  toolState: { fontSize: type.small, color: colors.tertiary },
  failed: { color: colors.danger },
  tail: {
    margin: 0,
    paddingInline: space.x2,
    paddingBottom: space.x2,
    fontSize: type.tiny,
    lineHeight: type.smallLine,
    color: colors.tertiary,
    whiteSpace: "pre-wrap",
    overflowWrap: "anywhere",
  },
  toolDetails: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x2,
    paddingBottom: space.x3,
  },
  mono: { borderRadius: radius.control, backgroundColor: colors.surface, overflow: "hidden" },
  monoHead: {
    display: "flex",
    alignItems: "center",
    justifyContent: "space-between",
    minHeight: size.row,
    paddingInlineStart: space.x4,
    paddingInlineEnd: space.x3,
    fontSize: type.small,
    lineHeight: type.smallLine,
    color: colors.tertiary,
  },
  monoText: {
    margin: 0,
    maxHeight: size.pane,
    overflow: "auto",
    paddingInline: space.x4,
    paddingBottom: space.x3,
    fontSize: type.small,
    lineHeight: type.blockLine,
    whiteSpace: "pre-wrap",
    overflowWrap: "anywhere",
    outline: "none",
  },
  meta: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x4,
    color: colors.tertiary,
    minHeight: size.control,
  },
  metaEnd: { display: "flex", columnGap: space.x4, marginInlineStart: "auto" },
  error: {
    display: "flex",
    flexWrap: "wrap",
    alignItems: "center",
    columnGap: space.x4,
    fontWeight: weight.medium,
    color: colors.primary,
  },
  activity: {
    display: "flex",
    alignItems: "center",
    columnGap: space.x4,
    height: space.x6,
    fontSize: type.text,
  },
  approval: {
    display: "flex",
    flexDirection: "column",
    rowGap: space.x2,
    padding: space.x4,
    borderRadius: radius.control,
    backgroundColor: colors.primary,
    color: colors.bg,
  },
  approvalCommand: {
    margin: 0,
    fontSize: type.small,
    lineHeight: type.blockLine,
    whiteSpace: "pre-wrap",
    overflowWrap: "anywhere",
  },
  approvalEffect: { opacity: opacity.quiet },
  approvalButtons: {
    display: "flex",
    justifyContent: "flex-end",
    columnGap: space.x2,
    marginTop: space.x2,
  },
  approvalButton: {
    display: "inline-flex",
    alignItems: "center",
    justifyContent: "center",
    height: size.touch,
    paddingInline: space.x5,
    borderRadius: radius.control,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.bg,
    fontWeight: weight.medium,
    opacity: { default: 1, ":disabled": opacity.dim },
    outline: { default: "none", ":focus-visible": `${stroke.hairline} solid ${colors.bg}` },
    outlineOffset: stroke.offset,
  },
  approve: { backgroundColor: colors.bg, color: colors.primary },
  notice: { display: "flex", alignItems: "center", columnGap: space.x4, color: colors.secondary },
  latest: {
    position: "absolute",
    bottom: space.x4,
    left: "50%",
    zIndex: layer.latest,
    display: "inline-flex",
    alignItems: "center",
    columnGap: space.x1,
    height: { default: size.item, [media.touch]: size.touch },
    paddingInline: space.x3,
    transform: "translateX(-50%)",
    borderRadius: radius.control,
    borderWidth: stroke.hairline,
    borderStyle: "solid",
    borderColor: colors.hairline,
    backgroundColor: colors.raised,
    color: colors.secondary,
    fontSize: type.small,
    boxShadow: shadows.latest,
  },
});
