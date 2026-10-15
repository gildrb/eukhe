// Evaluated in the VM before `prelude.js`, so the prelude's lockdown freezes what it installs. Makes a run
// deterministic, as pi-codemode's deterministic mode does through WASI (`runtime/vm.js`):
// - Time: `Date` reads virtual time, `startedAt` and then the `now` of the result being processed
//   (`setNow`), never going backwards.
// - Timezone: UTC, not the host's. Local-time getters, setters, constructors, parsing, and formatting
//   use UTC; `getTimezoneOffset()` is 0.
// - Randomness: `Math.random()` draws from mulberry32 over the seed.
// `WeakRef` and `FinalizationRegistry` are not added to the context at all (`vm.rs`).
//
// Evaluates to `(startedAt, seed) => { setNow, bridge, describe }`:
// - `setNow(ms)`: the clock while the next result is processed.
// - `bridge(post)`: the prelude's `bridge(kind, a, b, c)`, posting `[kind, a, b, c]` as JSON text (`undefined`
//   becomes `null`; the prelude never passes `null`), with strings made well-formed so the host can decode them.
// - `describe(error)`: a compile error as `{ name, message, stack }` JSON (pi-codemode `describeException`).
(function (startedAt, seed) {
	"use strict";

	const stringify = JSON.stringify;
	const construct = Reflect.construct;
	const isNaNNumber = Number.isNaN;
	const isFiniteNumber = Number.isFinite;
	const max = Math.max;
	const floor = Math.floor;
	const abs = Math.abs;
	const imul = Math.imul;
	const RealDate = Date;
	const proto = RealDate.prototype;
	const realParse = RealDate.parse;
	const realUTC = RealDate.UTC;
	const getTime = proto.getTime;
	const call = (fn, self, ...args) => Reflect.apply(fn, self, args);

	let now = startedAt;

	// The ISO format QuickJS parses strictly (`js_date_parse_isostring`): group 1 is the time, group 2 the zone.
	const ISO = /^(?:[+-]\d{6}|\d{4})(?:-\d\d(?:-\d\d)?)?(T\d\d:\d\d(?::\d\d(?:[.,]\d+)?)?)?(Z|[+-]\d+(?::\d\d)?)?$/;

	// Text QuickJS would read in the host's local time is read as UTC. An ISO date-time without a zone gets
	// "Z"; date-only ISO text is UTC already. Any other format goes to QuickJS's free-form parser after a
	// leading "GMT": a zone in the text overrides it, so zoned text keeps its zone and the rest reads as UTC.
	function parseUtc(text) {
		const iso = ISO.exec(text);
		if (iso === null) return realParse("GMT " + text);
		return iso[1] !== undefined && iso[2] === undefined ? realParse(text + "Z") : realParse(text);
	}

	// OrdinaryToPrimitive with the default hint (valueOf first), as `new Date(value)` applies it.
	function primitive(value) {
		if ((typeof value !== "object" || value === null) && typeof value !== "function") return value;
		const toPrimitive = value[Symbol.toPrimitive];
		if (toPrimitive !== undefined && toPrimitive !== null) return call(toPrimitive, value, "default");
		for (const name of ["valueOf", "toString"]) {
			const method = value[name];
			if (typeof method === "function") {
				const result = call(method, value);
				if ((typeof result !== "object" || result === null) && typeof result !== "function") return result;
			}
		}
		throw new TypeError("Cannot convert object to primitive value");
	}

	function timeOf(date) {
		return call(getTime, date);
	}

	function isDate(value) {
		if (typeof value !== "object" || value === null) return false;
		try {
			timeOf(value);
			return true;
		} catch {
			return false;
		}
	}

	const DAYS = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];
	const MONTHS = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"];
	const pad = (value, width) => String(value).padStart(width, "0");
	const year = (value) => (value < 0 ? "-" + pad(abs(value), 6) : pad(value, 4));

	function dateText(date) {
		return (
			DAYS[date.getUTCDay()] + " " + MONTHS[date.getUTCMonth()] + " " + pad(date.getUTCDate(), 2) + " " +
			year(date.getUTCFullYear())
		);
	}

	function timeText(date) {
		return pad(date.getUTCHours(), 2) + ":" + pad(date.getUTCMinutes(), 2) + ":" + pad(date.getUTCSeconds(), 2);
	}

	function localeTime(date) {
		const hours = date.getUTCHours();
		const twelve = hours % 12 === 0 ? 12 : hours % 12;
		return twelve + ":" + pad(date.getUTCMinutes(), 2) + ":" + pad(date.getUTCSeconds(), 2) + (hours < 12 ? " AM" : " PM");
	}

	function localeDate(date) {
		return date.getUTCMonth() + 1 + "/" + date.getUTCDate() + "/" + date.getUTCFullYear();
	}

	// `this` must be a Date (the getter's TypeError otherwise); an invalid one formats as "Invalid Date".
	function format(render) {
		return function () {
			if (isNaNNumber(timeOf(this))) return "Invalid Date";
			return render(this);
		};
	}

	function VirtualDate(...args) {
		if (new.target === undefined) return call(proto.toString, construct(RealDate, [now]));
		let time;
		if (args.length === 0) time = now;
		else if (args.length === 1) {
			const value = args[0];
			if (isDate(value)) time = timeOf(value);
			else {
				const prim = primitive(value);
				time = typeof prim === "string" ? parseUtc(prim) : timeOf(construct(RealDate, [prim]));
			}
		} else time = realUTC(...args);
		return construct(RealDate, [time], new.target);
	}
	Object.defineProperty(VirtualDate, "length", { value: 7 });
	Object.defineProperty(VirtualDate, "name", { value: "Date" });
	VirtualDate.prototype = proto;
	// Method shorthands: a named function expression `now` would shadow the clock.
	const statics = {
		now() {
			return floor(now);
		},
		parse(text) {
			return parseUtc(String(text));
		},
	};
	VirtualDate.now = statics.now;
	VirtualDate.parse = statics.parse;
	VirtualDate.UTC = realUTC;
	Object.defineProperty(proto, "constructor", { value: VirtualDate, writable: true, configurable: true });

	const UTC_METHODS = [
		"FullYear",
		"Month",
		"Date",
		"Day",
		"Hours",
		"Minutes",
		"Seconds",
		"Milliseconds",
	];
	for (const name of UTC_METHODS) {
		const getter = proto["getUTC" + name];
		Object.defineProperty(proto, "get" + name, {
			value: function () {
				return call(getter, this);
			},
			writable: true,
			configurable: true,
		});
		if (name === "Day") continue;
		const setter = proto["setUTC" + name];
		Object.defineProperty(proto, "set" + name, {
			value: function (...values) {
				return call(setter, this, ...values);
			},
			writable: true,
			configurable: true,
		});
	}
	// Annex B: two-digit-year forms of the local getter and setter.
	if (typeof proto.getYear === "function") {
		proto.getYear = function getYear() {
			const time = timeOf(this);
			return isNaNNumber(time) ? time : this.getUTCFullYear() - 1900;
		};
	}
	if (typeof proto.setYear === "function") {
		proto.setYear = function setYear(value) {
			const number = Number(value);
			const full = number >= 0 && number <= 99 && floor(number) === number ? 1900 + number : number;
			const time = timeOf(this);
			const base = isNaNNumber(time) ? construct(RealDate, [0]) : this;
			return this.setTime(realUTC(full, base.getUTCMonth(), base.getUTCDate(), base.getUTCHours(),
				base.getUTCMinutes(), base.getUTCSeconds(), base.getUTCMilliseconds()));
		};
	}
	proto.getTimezoneOffset = function getTimezoneOffset() {
		const time = timeOf(this);
		return isNaNNumber(time) ? time : 0;
	};
	proto.toString = format((date) => dateText(date) + " " + timeText(date) + " GMT+0000 (Coordinated Universal Time)");
	proto.toDateString = format(dateText);
	proto.toTimeString = format((date) => timeText(date) + " GMT+0000 (Coordinated Universal Time)");
	proto.toLocaleString = format((date) => localeDate(date) + ", " + localeTime(date));
	proto.toLocaleDateString = format(localeDate);
	proto.toLocaleTimeString = format(localeTime);
	Object.defineProperty(globalThis, "Date", { value: VirtualDate, writable: true, configurable: true });

	// mulberry32: one 32-bit draw per call; two draws make a double in [0, 1) with 53 random bits.
	let state = (seed ^ 0x9e3779b9) >>> 0;
	function draw() {
		state = (state + 0x6d2b79f5) >>> 0;
		let value = imul(state ^ (state >>> 15), 1 | state);
		value = (value + imul(value ^ (value >>> 7), 61 | value)) ^ value;
		return (value ^ (value >>> 14)) >>> 0;
	}
	Object.defineProperty(Math, "random", {
		value: function random() {
			return ((draw() >>> 5) * 67108864 + (draw() >>> 6)) / 9007199254740992;
		},
		writable: true,
		configurable: true,
	});

	const wellFormed = (value) => (typeof value === "string" ? value.toWellFormed() : value);

	return {
		setNow(value) {
			if (isFiniteNumber(value)) now = max(now, value);
		},
		bridge(post) {
			return (kind, a, b, c) => post(stringify([kind, wellFormed(a), wellFormed(b), wellFormed(c)]));
		},
		describe(error) {
			const name = String(error?.name ?? "Error");
			const message = String(error?.message ?? error);
			const head = message ? name + ": " + message : name;
			const stack = typeof error?.stack === "string" ? error.stack.trimEnd() : "";
			return stringify({ name, message, stack: stack ? head + "\n" + stack : head });
		},
	};
})
