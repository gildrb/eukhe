// Facts about built-ins that the ES lib does not state and template.ts relies on. The interfaces
// merge into the lib's, which a `type` alias cannot do.

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

/** An array with at least one element: `pop` gives one. */
type NonEmptyArray<T> = { pop(): T } & [T, ...T[]];

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the ES lib's MapConstructor
interface MapConstructor {
  /**
   * `new Map<K, V, "keyed">(…)` makes a `KeyedMap`. Without that third type argument the rest
   * parameter wants an impossible argument, so a plain `new Map(…)` keeps the lib's signatures.
   */
  new <K, V, Kind>(entries?: Iterable<readonly [K, V]> | null, ...keyed: Kind extends "keyed" ? [] : [never]): KeyedMap<K, V>;
}

// oxlint-disable-next-line typescript/consistent-type-definitions -- merges into the ES lib's String
interface String {
  /** Splitting by a non-empty separator gives at least one part (`"".split(".")` is `[""]`). */
  split<S extends string>(separator: string extends S ? never : S extends "" ? never : S): NonEmptyArray<string>;
}
