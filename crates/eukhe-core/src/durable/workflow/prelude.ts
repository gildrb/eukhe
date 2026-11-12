// The dynamic workflow script API, over the `wf.*` host globals. The tool
// declares `args` and `__wfLimits` before this prelude and runs the
// script's body after it, all in one async function body.
const __wfQueue: (() => void)[] = [];
let __wfFree = __wfLimits.concurrency;
let __wfOrdinal = 0;
let __wfSpawned = 0;
let __wfPhase: string | null = null;
const __wfSeen = new Map<string, number>();
const __wfIgnore = () => undefined;
const __wfUpdates: Promise<undefined>[] = [];

function __wfSettled(): Promise<undefined[]> {
	return Promise.all(__wfUpdates.map((update) => update.then(__wfIgnore, __wfIgnore)));
}

function __wfAcquire(): Promise<void> {
	if (__wfFree > 0) {
		__wfFree -= 1;
		return Promise.resolve();
	}
	return new Promise<void>((resolve) => __wfQueue.push(resolve));
}

function __wfRelease() {
	const next = __wfQueue.shift();
	if (next === undefined) {
		__wfFree += 1;
	} else {
		next();
	}
}

const budget = Object.freeze({
	size: __wfLimits.size,
	concurrency: __wfLimits.concurrency,
	maxAgents: __wfLimits.maxAgents,
	spawned: () => __wfSpawned,
});

function phase(title: string): Promise<undefined> {
	__wfPhase = String(title);
	const done = wf.phase({ title: __wfPhase });
	__wfUpdates.push(done);
	done.then(__wfIgnore, __wfIgnore);
	return done;
}

function log(message: unknown): Promise<undefined> {
	const done = wf.log({ message: typeof message === "string" ? message : JSON.stringify(message) });
	__wfUpdates.push(done);
	done.then(__wfIgnore, __wfIgnore);
	return done;
}

async function agent(prompt: string, opts?: AgentOptions): Promise<unknown> {
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
	await __wfAcquire();
	try {
		const answer = await wf.agent({ ordinal, occurrence, prompt, options });
		if (!answer.cached) {
			__wfSpawned += 1;
		}
		return answer.result;
	} finally {
		__wfRelease();
	}
}

function parallel<T>(thunks: (() => T | PromiseLike<T>)[]): Promise<(T | null)[]> {
	if (!Array.isArray(thunks)) {
		throw new TypeError("parallel(thunks) takes an array of functions");
	}
	return Promise.all(
		thunks.map((thunk) => {
			try {
				return Promise.resolve(thunk()).then(
					(value) => (value === undefined ? null : value),
					() => null,
				);
			} catch {
				return Promise.resolve(null);
			}
		}),
	);
}

function pipeline(items: unknown[], ...stages: PipelineStage[]): Promise<unknown[]> {
	if (!Array.isArray(items)) {
		throw new TypeError("pipeline(items, ...stages) takes an array of items");
	}
	return Promise.all(
		items.map(async (item, index) => {
			let value = item;
			for (const stage of stages) {
				if (value === null || value === undefined) {
					return null;
				}
				try {
					value = await stage(value, item, index);
				} catch {
					return null;
				}
			}
			return value === undefined ? null : value;
		}),
	);
}
