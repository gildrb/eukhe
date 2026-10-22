# The wire format of the compiled Bend core

Every entry of the compiled Bend core (`bend/core.bend`, called from Rust
through `eukhe_bend::call` or a `eukhe_bend::Stepper`) reads its input and
writes its reply as text in this format. `bend/wire.bend` is the Bend side
(an encoder `put_x` and a total decoder `get_x` per primitive);
`src/wire.rs` is the Rust side (`Writer`, `Reader`). LAWS.bend section
`wire` pins the Bend side: for every value `x` and every `rest`,
`get_x(put_x(x, rest)) == Got{x, rest}`, and `get_x(s) == Got{x, rest}`
only when `s == put_x(x, rest)`: every other input decodes to `Bad{}`.
One Rust test feeds Rust-encoded values through the real `call` and checks
that the Bend side reads them back.

## Grammar

Values are self-delimiting and concatenate with no separator. A decoder
knows the type it reads: there are no type tags on the wire.

| Type | Encoding | Examples |
|---|---|---|
| `Nat` | canonical decimal (no leading zero; `0` alone), 1 to 14 digits, then `,` | `0,` `42,` `99999999999999,` |
| `U32` | a `Nat` that is at most 4294967295 | `7,` `4294967295,` |
| `Bool` | `T` or `F` | `T` |
| `String` | its length in chars (Unicode scalar values; Rust `chars().count()`), a `Nat`, then the chars as UTF-8 | `0,` `5,héllo` `3,a,b` |
| `List<A>` | its length (a `Nat`), then each item | `[1, 22]` = `2,1,22,` ; `[]` = `0,` |
| `Maybe<A>` | `0,` for `None`, `1,` then the value for `Some` | `0,` `1,5,` |
| a constructor | its tag (a `Nat`: the index of the constructor in its type, from 0), then its fields in order | `Pair{3, "ab"}` with tag 0 = `0,3,2,ab` |
| a record (one constructor) | its fields in order, no tag | `(1, T)` = `1,T` |
| a reply | the value, or the error form: `E ` then a text to the end of the reply | `E unknown entry` |

A request is one value (usually a record) that MUST be the whole input:
the Bend entry checks that nothing is left (`W.end`). A reply never starts
with `E` unless it is the error form (no encoding starts with `E`).

Bounds: a `Nat` has at most 14 digits (at most 99999999999999 = 10^14 - 1,
below the runtime's 2^48 - 1), decided while reading: the decoder refuses
the 15th digit, so it never folds a value the runtime cannot hold. Rust
`Writer::nat` refuses a larger value (`WireError::NatTooLarge`); Bend's
`put_nat` writes every digit of a larger value, which every decoder
refuses. Counts (string lengths, list lengths) are Nats too.

A String has at most `STR_MAX` = 8 Mi chars (`Writer::str` refuses a
longer one): Bend's `put_str` and `get_str` are flat loops, but a model
that recurses over a String takes one stack frame per char (and
`get_list` / `put_list` one per item), and the shim's 256 MiB evaluation
stack holds about 16 Mi of them; a deeper run faults and ends the
process. A larger text belongs in a stepper's state, fed in pieces.

Examples of a whole request. A record `{ name: String, tries: Nat, tags:
List<String>, cap: Maybe<U32>, on: Bool }` with `("héllo", 3, ["a", "bc"],
Some(7), true)`:

```
5,héllo3,2,1,a2,bc1,7,T
```

A state-machine step `step(state, event) -> (state, actions)` encodes the
same way: the state as a record, the event as a constructor (tag + fields),
the actions as a `List` of constructors.

## Bend side (`bend/wire.bend`, `import ./wire.bend as W`)

```python
type W.Dec<-A: Data>: W.Got{value: A, rest: String} | W.Bad{}

W.put_nat(n: Nat, rest: String) -> String        W.get_nat(s: String) -> W.Dec<Nat>
W.put_u32(x: U32, rest: String) -> String        W.get_u32(s: String) -> W.Dec<U32>
W.put_bool(b: Bool, rest: String) -> String      W.get_bool(s: String) -> W.Dec<Bool>
W.put_str(a: String, rest: String) -> String     W.get_str(s: String) -> W.Dec<String>
W.put_list(~A, ~put, xs, rest) -> String         W.get_list(~A, ~get, s) -> W.Dec<List<&2, A>>
W.err(text: String) -> String                    W.end(s: String) -> Bool
```

An encoder answers the encoding of its value followed by `rest`, so a
record is `W.put_nat(a, W.put_str(b, W.put_bool(c, rest)))`: no append, no
`String.concat` (a recursive result inside `String.concat` is O(n^2)). A
tag is `W.put_nat(<index>n, ...)`; a decoder of a type with several
constructors reads the tag with `W.get_nat` and matches it (an unknown tag
is `W.Bad{}`). `W.put_list` / `W.get_list` are templates over the item's
codec: `W.put_list(~Nat, ~W.put_nat, xs, rest)`. An area's codec proves its
own round trip (LAWS.bend, the area's section) from the `wire` laws.

An entry: `def ffi(input: String) -> String`: decode the request; on
`W.Bad{}` or input left over answer `W.err("<what>")`, never a default;
else call the model and encode the reply.

## Rust side (`eukhe_bend::wire`)

```rust
pub enum WireError {
    NatTooLarge(u64),          // Writer: a Nat above 99_999_999_999_999
    StrTooLong(usize),         // Writer: a String above STR_MAX = 8 Mi chars
    Rejected(String),          // the reply is the error form: the text after "E "
    Malformed { at: usize, expected: &'static str }, // byte offset in the reply
    Trailing { at: usize },    // Reader::end: input left over
}

pub struct Writer { /* String buffer + first error */ }
impl Writer {
    pub fn new() -> Writer;
    pub fn nat(&mut self, n: u64) -> &mut Writer;     // records NatTooLarge
    pub fn u32(&mut self, n: u32) -> &mut Writer;
    pub fn bool(&mut self, b: bool) -> &mut Writer;
    pub fn str(&mut self, s: &str) -> &mut Writer;
    pub fn tag(&mut self, t: u32) -> &mut Writer;     // a constructor's index
    pub fn count(&mut self, n: usize) -> &mut Writer; // a List's length (then write the items)
    pub fn none(&mut self) -> &mut Writer;            // Maybe: None
    pub fn some(&mut self) -> &mut Writer;            // Maybe: Some (then write the value)
    pub fn finish(&mut self) -> Result<String, WireError>;
}

pub struct Reader<'a> { /* the reply and an offset */ }
impl<'a> Reader<'a> {
    pub fn reply(reply: &'a str) -> Result<Reader<'a>, WireError>; // "E <text>" -> Rejected
    pub fn new(src: &'a str) -> Reader<'a>;                        // a request (tests)
    pub fn nat(&mut self) -> Result<u64, WireError>;
    pub fn u32(&mut self) -> Result<u32, WireError>;
    pub fn bool(&mut self) -> Result<bool, WireError>;
    pub fn str(&mut self) -> Result<&'a str, WireError>;
    pub fn tag(&mut self) -> Result<u32, WireError>;
    pub fn tag_of(&mut self, ctors: u32, expected: &'static str) -> Result<u32, WireError>; // Malformed for tag >= ctors
    pub fn count(&mut self) -> Result<usize, WireError>;
    pub fn maybe(&mut self) -> Result<bool, WireError>; // true: Some, the value follows
    pub fn end(self) -> Result<(), WireError>;          // Trailing if input is left
}
```

The Rust decoders follow the same grammar exactly (canonical digits, at
most 14, U32 range, string length in chars). A decode error or a
`Rejected` reply is an error value the caller handles: never a silent
default, never a panic.

## Calls, steppers and errors (`eukhe_bend`)

```rust
pub fn call(entry: Entry, input: &str) -> Result<String, CallError>;
impl Stepper {
    pub fn open(entry: Entry, input: &str) -> Result<(Stepper, String), CallError>;
    pub fn step(&mut self, input: &str) -> Result<String, CallError>; // Drop closes
}
pub enum Error { Call(CallError), Wire(WireError) }   // From both: `?` works
pub fn expect_core<T, E: Into<Error>>(entry: Entry, result: Result<T, E>) -> T;
```

An entry with a stepper (`bend/ffi_<area>.bend` exports `def open(input:
String) -> St & String` and `def step(s: St, input: String) -> St &
String`) keeps its state in the Bend heap: only events and replies cross
the wire. Use it on hot paths: decoding text costs about 50-80 ns a char,
so a call that ships a 10k-item state each time is thousands of times
slower than a step.

Error policy: a caller that encodes its own request with every number in
range (it saturates or validates first) wraps the call in `expect_core`:
a failure then means an inconsistent build, and `expect_core` panics with
the entry and the error (the one place eukhe panics on the core). A caller
that already returns a `Result` propagates `eukhe_bend::Error`.
