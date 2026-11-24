// The dynamic workflow script API, over the `wf.*` host globals. The tool
// declares `args` and `__wfLimits` before this prelude and runs the
// script's body after it, all in one async function body.
const __wfQueue = [];
let __wfFree = __wfLimits.concurrency;
let __wfOrdinal = 0;
let __wfSpawned = 0;
let __wfPhase = null;
const __wfSeen = new Map();
const __wfIgnore = () => undefined;
const __wfUpdates = [];
// The writing agents called since the last microtask: one group.
let __wfBatch = null;
// The writing agents of the run whose `wf.agent` has not settled, and how
// many settled so far.
let __wfWriting = 0;
let __wfWritten = 0;
// The writing groups that wait for room in the agent tree: each asks
// again once a writing agent settles.
let __wfWaiting = [];
// The errors the run's problems hold: a refused group rejects each of its
// agents with one error.
const __wfReported = new Set();

function __wfSettled() {
	return Promise.all(__wfUpdates.map((update) => update.then(__wfIgnore, __wfIgnore)));
}

function __wfAcquire() {
	if (__wfFree > 0) {
		__wfFree -= 1;
		return Promise.resolve();
	}
	return new Promise((resolve) => __wfQueue.push(resolve));
}

function __wfRelease() {
	const next = __wfQueue.shift();
	if (next === undefined) {
		__wfFree += 1;
	} else {
		next();
	}
}

// Join the group of the writing agents called in this turn of the script:
// the group starts once the turn yields, so `parallel()` and the first
// stage of `pipeline()` start their writing agents together.
function __wfJoinBatch(request) {
	let batch = __wfBatch;
	if (batch === null) {
		const started = [];
		batch = started;
		__wfBatch = started;
		void Promise.resolve().then(() => {
			__wfBatch = null;
			__wfStartBatch(started);
		});
	}
	const joined = batch;
	return new Promise((resolve, reject) => {
		joined.push({ request, resolve, reject });
	});
}

// Start the next wave of a writing group: the host checks the whole
// group, starts the longest first run of its agents one batch holds, and
// defers the rest. A wave that started may leave room for another batch,
// so the rest ask again at once; a group none of whose agents fit (the
// host defers it only while a writing agent of the run runs) waits for a
// writing agent to settle, or asks again at once when one settled during
// the ask. A refusal rejects every agent of the group.
function __wfStartBatch(group) {
	const written = __wfWritten;
	wf.batch({ agents: group.map((writer) => writer.request), writing: __wfWriting }).then(
		(reply) => {
			const deferred = new Set(reply.deferred);
			const now = group.filter((writer) => !deferred.has(writer.request.ordinal));
			const later = group.filter((writer) => deferred.has(writer.request.ordinal));
			for (const writer of now) {
				__wfRunWriter(writer);
			}
			if (later.length === 0) {
				return;
			}
			if (now.length > 0 || __wfWritten !== written) {
				__wfStartBatch(later);
			} else {
				__wfWaiting.push(later);
			}
		},
		(error) => {
			for (const writer of group) {
				writer.reject(error);
			}
		},
	);
}

function __wfRunWriter(writer) {
	__wfWriting += 1;
	wf.agent(writer.request).then(
		(answer) => {
			__wfWriterSettled();
			writer.resolve(answer);
		},
		(error) => {
			__wfWriterSettled();
			writer.reject(error);
		},
	);
}

// A writing agent settled: its batch may have returned its nodes, so every
// waiting group asks again.
function __wfWriterSettled() {
	__wfWriting -= 1;
	__wfWritten += 1;
	const waiting = __wfWaiting;
	__wfWaiting = [];
	for (const group of waiting) {
		__wfStartBatch(group);
	}
}

// Record why a slot of `parallel()` or an item of `pipeline()` became
// `null`, once per error: the run's report lists it.
function __wfProblem(where, error) {
	if (__wfReported.has(error)) {
		return null;
	}
	__wfReported.add(error);
	const text =
		error instanceof Error ? (error.name === "Error" ? error.message : `${error.name}: ${error.message}`) : String(error);
	const done = wf.problem({ message: `${where}: ${text}` });
	__wfUpdates.push(done);
	done.then(__wfIgnore, __wfIgnore);
	return null;
}

const budget = Object.freeze({
	size: __wfLimits.size,
	concurrency: __wfLimits.concurrency,
	maxAgents: __wfLimits.maxAgents,
	writers: __wfLimits.writers,
	spawned: () => __wfSpawned,
});

function phase(title) {
	__wfPhase = String(title);
	const done = wf.phase({ title: __wfPhase });
	__wfUpdates.push(done);
	done.then(__wfIgnore, __wfIgnore);
	return done;
}

function log(message) {
	const done = wf.log({ message: typeof message === "string" ? message : JSON.stringify(message) });
	__wfUpdates.push(done);
	done.then(__wfIgnore, __wfIgnore);
	return done;
}

async function agent(prompt, opts) {
	if (typeof prompt !== "string" || prompt.trim() === "") {
		throw new TypeError("agent(prompt, opts): prompt must be a non-empty string");
	}
	if (opts !== undefined && (typeof opts !== "object" || opts === null || Array.isArray(opts))) {
		throw new TypeError("agent(prompt, opts): opts must be an object");
	}
	const options = Object.assign({}, opts);
	if (options.phase === undefined && __wfPhase !== null) {
		options.phase = __wfPhase;
	}
	const ordinal = ++__wfOrdinal;
	const identity = JSON.stringify([prompt, options]);
	const occurrence = __wfSeen.get(identity) ?? 0;
	__wfSeen.set(identity, occurrence + 1);
	const request = { ordinal, occurrence, prompt, options };
	if (options.scope !== undefined && options.scope !== null) {
		const answer = await __wfJoinBatch(request);
		if (!answer.cached) {
			__wfSpawned += 1;
		}
		return answer.result;
	}
	await __wfAcquire();
	try {
		const answer = await wf.agent(request);
		if (!answer.cached) {
			__wfSpawned += 1;
		}
		return answer.result;
	} finally {
		__wfRelease();
	}
}

function parallel(thunks) {
	if (!Array.isArray(thunks)) {
		throw new TypeError("parallel(thunks) takes an array of functions");
	}
	return Promise.all(
		thunks.map((thunk, slot) => {
			try {
				return Promise.resolve(thunk()).then(
					(value) => (value === undefined ? null : value),
					(error) => __wfProblem(`parallel slot ${slot}`, error),
				);
			} catch (error) {
				return Promise.resolve(__wfProblem(`parallel slot ${slot}`, error));
			}
		}),
	);
}

function pipeline(items, ...stages) {
	if (!Array.isArray(items)) {
		throw new TypeError("pipeline(items, ...stages) takes an array of items");
	}
	return Promise.all(
		items.map(async (item, index) => {
			let value = item;
			for (const [at, stage] of stages.entries()) {
				if (value === null || value === undefined) {
					return null;
				}
				try {
					value = await stage(value, item, index);
				} catch (error) {
					return __wfProblem(`pipeline item ${index} stage ${at + 1}`, error);
				}
			}
			return value === undefined ? null : value;
		}),
	);
}
