// What prelude.ts gives the script, and what it keeps for it. The `interface`s and the
// `namespace` merge into the lib's (a `type` cannot merge); they state facts prelude.ts relies on
// so its code stays pi-codemode's, byte for byte (the codemode fingerprint hashes it).

/** A tool or host global as the script calls it: the result's value, or the call's error. */
type HostFunction = (...args: unknown[]) => Promise<unknown>;

/** A call waiting for its result. */
type Pending = { resolve: (value: unknown) => void; reject: (error: unknown) => void };

/** What `image()` reads from an object: an `image_url`, or an image block `{ type, data }`. */
type ImageFields = { readonly image_url?: unknown; readonly type?: unknown; readonly data?: unknown };

/** What a script may pass `image()`: anything; a string is a URL. */
type ImageArgument = string | ImageFields | number | bigint | boolean | symbol | null | undefined;

/** The store's writes, in order: `[key]` deletes it, `[key, json]` sets it. */
type StoreWrite = [key: string] | [key: string, json: string];

declare const ownKeyOf: unique symbol;

/** A key `Reflect.ownKeys` read from a `T`: an own property of it until something deletes it. */
type OwnKey<T> = (string | symbol) & { readonly [ownKeyOf]: T };

declare namespace Reflect {
  function ownKeys<T extends object>(target: T): OwnKey<T>[];
}

/**
 * A `Map` whose `has` and `set` tell the checker which key it holds: after `m.has(k)` is true, or
 * after `m.set(k, v)`, `m.get(k)` gives a `V`. `set` returns nothing here (it asserts), so its
 * result is not chained; a variable calling it needs a type annotation. `get` is a property so
 * that its key is checked strictly: knowing one key is held says nothing of another.
 */
type KeyedMap<K, V> = Omit<Map<K, V>, "has" | "set"> & {
  has<Q extends K>(key: Q): this is { readonly get: (key: Q) => V } & KeyedMap<K, V>;
  set<Q extends K>(key: Q, value: V): asserts this is { readonly get: (key: Q) => V } & KeyedMap<K, V>;
};

interface MapConstructor {
  /**
   * `new Map<K, V, "keyed">(…)` makes a `KeyedMap`. Without that third type argument the rest
   * parameter wants an impossible argument, so a plain `new Map(…)` keeps the lib's signatures.
   */
  new <K, V, Kind>(entries?: Iterable<readonly [K, V]> | null, ...keyed: Kind extends "keyed" ? [] : [never]): KeyedMap<K, V>;
}

interface IteratorConstructor {
  /** Wraps any object with a `next` method; `next` is first called when the wrapper is iterated. */
  from(value: { next(): unknown }): IteratorObject<unknown, unknown, unknown>;
}

interface ObjectConstructor {
  /** Every own property's descriptor, symbol keys included. */
  getOwnPropertyDescriptors(o: unknown): { [key: PropertyKey]: PropertyDescriptor };
  /** The descriptor of a property the object literal `o` defines itself: always there. */
  getOwnPropertyDescriptor<K extends PropertyKey>(o: { readonly [P in K]: unknown }, p: K): PropertyDescriptor;
  /** The descriptor of a key `Reflect.ownKeys` read from `o`, nothing deleted since: always there. */
  getOwnPropertyDescriptor<T extends object>(o: T, p: OwnKey<T>): PropertyDescriptor;
}
