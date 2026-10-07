// Produces `ts_records.json`: durable record JSON written by the TS package
// (`@earendil-works/pi-durable` v1.0.4), for the Rust serde round-trip tests.
// Regenerate from a directory with the npm packages installed:
//   node --input-type=module < ts_records.mjs > ts_records.json
import { BACKGROUND_CONTEXT as context } from "@earendil-works/chord/context";
import {
	CompactionEntry,
	MemoryStorage,
	ResetEntry,
	SystemEntry,
	ToolResultEntry,
	UserEntry,
	AssistantEntry,
	createSession,
	defineDoc,
	defineDocFamily,
	defineEntry,
	defineTask,
} from "@earendil-works/pi-durable";

class LoggingStorage extends MemoryStorage {
	batches = [];
	async commit(writes, ctx) {
		this.batches.push(JSON.stringify(writes));
		return super.commit(writes, ctx);
	}
}

const storage = new LoggingStorage();
const session = createSession(storage);

const initial = () => ({ value: 0 });
const SessionDoc = defineDoc({ kind: "t.session", version: 1, scope: "session", initial });
const LatestDoc = defineDoc({ kind: "t.latest", version: 1, scope: "conversation", history: "latest", fork: "current", initial });
const RewindableDoc = defineDoc({ kind: "t.rewindable", version: 2, scope: "conversation", history: "rewindable", fork: "asOf", initial });
const InitialDoc = defineDoc({ kind: "t.initial", version: 1, scope: "conversation", history: "rewindable", fork: "initial", initial });
const TaskDoc = defineDoc({ kind: "t.task", version: 1, scope: "task", initial });
const Family = defineDocFamily({
	kind: "t.family",
	version: 1,
	family: true,
	scope: "conversation",
	history: "latest",
	fork: "initial",
	initial: (seed) => ({ value: seed, "2": "index", "1": "first" }),
});
const Note = defineEntry("t.note");

const Echo = defineTask({
	name: "t.echo",
	version: 3,
	initial: (input) => ({ phase: "run", input }),
	phases: { run: async () => {} },
	abort: async () => {},
});

const usage = {
	input: 1,
	output: 2,
	cacheRead: 0,
	cacheWrite: 0,
	totalTokens: 3,
	cost: { input: 0.001, output: 0.002, cacheRead: 0, cacheWrite: 0, total: 0.003 },
};

const ids = {};
await session.commit(async (tx) => {
	const root = await tx.createConversation({ ownership: { kind: "ownerless" } });
	ids.root = root.id;
	const user = await tx.appendEntry(UserEntry, root.id, {
		model: [{ role: "user", content: "hello \u2028 \"world\" é😀", timestamp: 1700000000000 }],
	});
	ids.user = user.id;
	await tx.appendEntry(SystemEntry, root.id, {
		model: [{ role: "system", content: "", sections: { preamble: "Be brief.", old: null }, timestamp: 1700000000001 }],
	});
	const assistant = await tx.appendEntry(AssistantEntry, root.id, {
		model: [
			{
				role: "assistant",
				content: [
					{ type: "thinking", thinking: "hmm" },
					{ type: "text", text: "Calling" },
					{ type: "toolCall", id: "call_1", name: "read", arguments: { path: "a.txt", lines: [1, 2.5] } },
				],
				api: "anthropic-messages",
				provider: "anthropic",
				model: "claude",
				usage,
				stopReason: "toolUse",
				timestamp: 1700000000002,
			},
		],
	});
	ids.assistant = assistant.id;
	await tx.appendEntry(ToolResultEntry, root.id, {
		model: [
			{
				role: "toolResult",
				toolCallId: "call_1",
				toolName: "read",
				content: [{ type: "text", text: "contents" }],
				isError: false,
				timestamp: 1700000000003,
			},
		],
		data: { diagnostics: [{ severity: "warn", message: "truncated", code: "truncated" }, { severity: "info", message: "ok" }] },
	});
	await tx.appendEntry(root.id, {
		kind: "t.edits",
		edits: [
			{ target: user.id, action: "omit" },
			{ target: assistant.id, action: "replace", messages: [{ role: "user", content: [{ type: "text", text: "x" }], timestamp: 5 }] },
		],
		data: null,
	});
	await tx.appendEntry(Note, root.id, { data: { text: "n", nested: [1, -0.5, 1e21, true, null] } });
	await tx.appendEntry(ResetEntry, root.id, { head: "self" });
	await tx.appendEntry(root.id, {
		kind: CompactionEntry.kind,
		head: user.id,
		model: [{ role: "user", content: [{ type: "text", text: "summary" }], timestamp: 6 }],
		data: { reason: "threshold" },
	});
	const sessionDoc = await tx.doc(SessionDoc);
	sessionDoc.value = 1;
	await tx.doc(LatestDoc, root.id);
	await tx.doc(RewindableDoc, root.id);
	await tx.doc(InitialDoc, root.id);
	await tx.doc(Family, root.id, "k\"ey", 7);
	ids.task = await tx.createTask(Echo, { text: "hi" }, { ownership: { kind: "conversation" }, conversationId: root.id });
	ids.child = await tx.createTask(Echo, null, { ownership: { kind: "task", taskId: ids.task } });
	await tx.doc(TaskDoc, ids.task);
	const queued = await tx.createSubmission({ conversationId: root.id, requestId: "req-1", type: "input", status: "queued" });
	ids.queued = queued.id;
	const placed = await tx.createSubmission({ conversationId: root.id, type: "input", status: "placed", entry: user.id });
	ids.placed = placed.id;
	const write = await tx.createSubmission({ conversationId: root.id, type: "write", status: "queued" });
	ids.write = write.id;
	await tx.createSubmission({ conversationId: root.id, type: "write", status: "unanswered", reason: "stale" });
	await tx.createSubmission({ conversationId: root.id, type: "write", status: "done", entry: user.id });
}, context);

await session.commit(async (tx) => {
	(await tx.doc(RewindableDoc, ids.root)).value = 2;
	(await tx.doc(LatestDoc, ids.root)).value = 3;
	(await tx.doc(Family, ids.root, "k\"ey", 7)).list = ["a", { b: 1 }];
	tx.placeSubmission(ids.queued, ids.user);
	tx.placeSubmission(ids.write, ids.user);
	tx.settleSubmission(ids.placed, { status: "unanswered", reason: "failed", detail: { codes: ["x"] } });
}, context);

await session.commit(async (tx) => {
	tx.settleSubmission(ids.queued, { status: "done", answer: ids.assistant });
	await tx.retireDoc(SessionDoc);
}, context);

await session.commit(async (tx) => {
	const child = await tx.createConversation({ ownership: { kind: "task", taskId: ids.task } });
	const fork = await tx.forkConversation(ids.root, ids.assistant, { ownership: { kind: "ownerless" } });
	ids.forkChild = child.id;
	ids.fork = fork.id;
}, context);

// Task state transitions are scheduler work; write TS-shaped records directly.
const stored = await storage.task(ids.task, context);
const variants = [
	{ ...stored, state: { status: "running", checkpoint: stored.state.checkpoint }, memos: { kept: true, n: 1 } },
	{ ...stored, state: { status: "waiting", checkpoint: { phase: "wait" }, on: [ids.child], policy: "allSettled" }, abortRequested: true },
	{ ...stored, state: { status: "waiting", checkpoint: { phase: "wait" }, on: [ids.child], policy: "failFast" } },
	{ ...stored, state: { status: "completing", outcome: { status: "failed", error: { message: "held", detail: { reason: "model_error" } }, result: { entryId: 3 } } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "completed", result: { entryId: 4, control: { terminate: true } } } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "aborted" } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "aborted", reason: "user", result: null } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "orphaned", reason: "missing_task" } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "faulted", error: { message: "threw" } } } },
	{ ...stored, state: { status: "terminal", outcome: { status: "completed", result: null } } },
];
for (const value of variants) await storage.commit([{ type: "task", value }], context);

const records = {
	conversations: (await storage.scanConversations({}, 100, undefined, context)).items,
	entries: (await storage.scanEntries({ conversationId: ids.root }, 100, undefined, context)).items,
	entryLookup: await storage.entry(ids.user, context),
	tasks: [await storage.task(ids.child, context), ...variants],
	submissions: (await storage.scanSubmissions({}, 100, undefined, context)).items,
	documents: [
		...(await storage.scanDocuments({ scope: { kind: "conversation", conversationId: ids.root }, at: "current" }, 100, undefined, context)).items,
		...(await storage.scanDocuments({ scope: { kind: "conversation", conversationId: ids.fork }, at: "current" }, 100, undefined, context)).items,
		...(await storage.scanDocuments({ scope: { kind: "task", taskId: ids.task }, at: "current" }, 100, undefined, context)).items,
		await storage.findDocument({ kind: "t.session", scope: { kind: "session" } }, 1, context),
	],
	stored: await storage.document(
		(await storage.findDocument({ kind: "t.rewindable", scope: { kind: "conversation", conversationId: ids.root } }, "current", context)).id,
		"current",
		context,
	),
};

process.stdout.write(
	JSON.stringify({ batches: storage.batches.map((batch) => JSON.parse(batch)), records }, null, "\t") + "\n",
);
await session.close(context);
