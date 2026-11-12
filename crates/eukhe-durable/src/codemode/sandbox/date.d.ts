// The types host.ts replaces `Date` with. `interface Date` merges into the lib's Date (a `type`
// cannot merge).

/** `Reflect.apply` as host.ts calls it: typed for a known function, `unknown` for any other. */
type Call = {
  <T, A extends unknown[], R>(fn: (this: T, ...args: A) => R, self: T, ...args: A): R;
  (fn: Function, self: unknown, ...args: unknown[]): unknown;
};

/** An object `new Date(value)` converts to a primitive: the conversion methods it may call. */
type Convertible = {
  readonly [Symbol.toPrimitive]?: ((this: Convertible, hint: string) => unknown) | null;
  readonly [method: string]: unknown;
};

/** What a script may pass `Date`: anything, converted as `new Date(value)` converts it. */
type DateArgument = string | number | bigint | boolean | symbol | null | undefined | Convertible;

/**
 * `Date.UTC`, which converts each part to a number: a method signature (checked bivariantly)
 * lets the lib's `number` parameters take what a script passes.
 */
type DateUtc = { utc(...parts: DateArgument[]): number }["utc"];

interface Date {
  /** Annex B: the year minus 1900. */
  getYear(): number;
  /** Annex B: sets the year; 0 to 99 means 1900 to 1999. */
  setYear(year: unknown): number;
  /** host.ts reads and replaces the prototype's methods by name (`"getUTC" + name`). */
  [method: string]: (this: Date, ...args: never[]) => unknown;
}
