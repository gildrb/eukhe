# ffi_arg_repair: the entry of the compiled Bend core for charitable
# argument repair (bend/arg_repair.bend; Rust: eukhe-bend
# rules/arg_repair.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the schema: its declared arguments (List: the name, the
#            `type` and the `items.type` as Maybe<String>), whether it is
#            closed (Bool); the dialect: its aliases, then its refused keys
#            (List each: two Strings, the key then the canonical name or
#            the hint); the sent arguments (List: the key, its decoding as
#            Maybe<String>, the value)
#   value    0 null | 1 a boolean (Bool) | 2 a number (its JSON text) |
#            3 a string: its text (Maybe<String>), its f64 reading's JSON
#            text (Maybe<String>), its shape (0 plain | 1 opens with `{`,
#            reads as an object (Bool) | 2 opens with `[`, reads as an array
#            (Bool)) | 4 an array | 5 an object
#   reply    0, the outs (List: the name, the value read as Maybe<to>), the
#            records (List: 0 an alias, the key then the name | 1 a value
#            read as the declared type, the name) | 1, the refusal (0 refused: the key,
#            the hint | 1 unknown: the key, the declared names
#            (List<String>) | 2 ambiguous: the name, the first key, the key)
#   to       0 a boolean (Bool) | 1 a number (its JSON text) | 2 a string |
#            3 the one-item array of the sent string | 4 the object, 5 the
#            array the sent string spells
#
# Malformed input, or input left after the request, answers
# `E arg_repair: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./arg_repair.bend as Ar

# A request of the entry
type Req is Data:
  Req{schema: Ar.Schema, dialect: Ar.Dialect, args: List<&2, Ar.Arg>}

# Requests
# --------

def get_ms.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ms.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_ms.some(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_ms.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_ms.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a Maybe<String> at the start of s
def get_ms(s: String) -> W.Dec<Maybe<&2, String>>:
  get_ms.start(W.get_nat(s))

def get_prop.items(n: String, k: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ar.Prop>:
  match r:
    case W.Got{i, s}:
      W.Got{Ar.Prop{n, k, i}, s}
    case W.Bad{}:
      W.Bad{}

def get_prop.kind(n: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ar.Prop>:
  match r:
    case W.Got{k, s}:
      get_prop.items(n, k, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_prop.name(r: W.Dec<String>) -> W.Dec<Ar.Prop>:
  match r:
    case W.Got{n, s}:
      get_prop.kind(n, get_ms(s))
    case W.Bad{}:
      W.Bad{}

# a declared argument at the start of s
def get_prop(s: String) -> W.Dec<Ar.Prop>:
  get_prop.name(W.get_str(s))

def get_kv.text(k: String, r: W.Dec<String>) -> W.Dec<Ar.KV>:
  match r:
    case W.Got{x, s}:
      W.Got{Ar.KV{k, x}, s}
    case W.Bad{}:
      W.Bad{}

def get_kv.key(r: W.Dec<String>) -> W.Dec<Ar.KV>:
  match r:
    case W.Got{k, s}:
      get_kv.text(k, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

# an alias or a refused key at the start of s
def get_kv(s: String) -> W.Dec<Ar.KV>:
  get_kv.key(W.get_str(s))

def get_shape.brace(r: W.Dec<Bool>) -> W.Dec<Ar.Shape>:
  match r:
    case W.Got{b, s}:
      W.Got{Ar.SBrace{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_shape.bracket(r: W.Dec<Bool>) -> W.Dec<Ar.Shape>:
  match r:
    case W.Got{b, s}:
      W.Got{Ar.SBracket{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_shape.tag(t: Nat, s: String) -> W.Dec<Ar.Shape>:
  match t:
    case 0n:
      W.Got{Ar.SPlain{}, s}
    case 1n:
      get_shape.brace(W.get_bool(s))
    case 2n:
      get_shape.bracket(W.get_bool(s))
    case 3n+u:
      W.Bad{}

def get_shape(r: W.Dec<Nat>) -> W.Dec<Ar.Shape>:
  match r:
    case W.Got{t, s}:
      get_shape.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_str.shape(x: Maybe<&2, String>, n: Maybe<&2, String>, r: W.Dec<Ar.Shape>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{h, s}:
      W.Got{Ar.VStr{x, n, h}, s}
    case W.Bad{}:
      W.Bad{}

def get_str.num(x: Maybe<&2, String>, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{n, s}:
      get_str.shape(x, n, get_shape(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_str.text(r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{x, s}:
      get_str.num(x, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_bool.val(r: W.Dec<Bool>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{b, s}:
      W.Got{Ar.VBool{b}, s}
    case W.Bad{}:
      W.Bad{}

def get_num.val(r: W.Dec<String>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{x, s}:
      W.Got{Ar.VNum{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_val.tag(t: Nat, s: String) -> W.Dec<Ar.Val>:
  match t:
    case 0n:
      W.Got{Ar.VNull{}, s}
    case 1n:
      get_bool.val(W.get_bool(s))
    case 2n:
      get_num.val(W.get_str(s))
    case 3n:
      get_str.text(get_ms(s))
    case 4n:
      W.Got{Ar.VArr{}, s}
    case 5n:
      W.Got{Ar.VObj{}, s}
    case 6n+u:
      W.Bad{}

def get_val(r: W.Dec<Nat>) -> W.Dec<Ar.Val>:
  match r:
    case W.Got{t, s}:
      get_val.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_arg.val(k: String, m: Maybe<&2, String>, r: W.Dec<Ar.Val>) -> W.Dec<Ar.Arg>:
  match r:
    case W.Got{v, s}:
      W.Got{Ar.Arg{k, m, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_arg.plain(k: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ar.Arg>:
  match r:
    case W.Got{m, s}:
      get_arg.val(k, m, get_val(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_arg.key(r: W.Dec<String>) -> W.Dec<Ar.Arg>:
  match r:
    case W.Got{k, s}:
      get_arg.plain(k, get_ms(s))
    case W.Bad{}:
      W.Bad{}

# a sent argument at the start of s
def get_arg(s: String) -> W.Dec<Ar.Arg>:
  get_arg.key(W.get_str(s))

def get_req.args(sc: Ar.Schema, d: Ar.Dialect, r: W.Dec<List<&2, Ar.Arg>>) -> W.Dec<Req>:
  match r:
    case W.Got{xs, s}:
      W.Got{Req{sc, d, xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.refused(sc: Ar.Schema, als: List<&2, Ar.KV>, r: W.Dec<List<&2, Ar.KV>>) -> W.Dec<Req>:
  match r:
    case W.Got{rs, s}:
      get_req.args(sc, Ar.Dialect{als, rs}, W.get_list(~Ar.Arg, ~get_arg, s))
    case W.Bad{}:
      W.Bad{}

def get_req.aliases(sc: Ar.Schema, r: W.Dec<List<&2, Ar.KV>>) -> W.Dec<Req>:
  match r:
    case W.Got{als, s}:
      get_req.refused(sc, als, W.get_list(~Ar.KV, ~get_kv, s))
    case W.Bad{}:
      W.Bad{}

def get_req.closed(ps: List<&2, Ar.Prop>, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_req.aliases(Ar.Schema{ps, c}, W.get_list(~Ar.KV, ~get_kv, s))
    case W.Bad{}:
      W.Bad{}

def get_req.props(r: W.Dec<List<&2, Ar.Prop>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      get_req.closed(ps, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.props(W.get_list(~Ar.Prop, ~get_prop, s))

# Replies
# -------

def put_to(t: Ar.To, rest: String) -> String:
  match t:
    case Ar.TBool{b}:
      W.put_nat(0n, W.put_bool(b, rest))
    case Ar.TNum{x}:
      W.put_nat(1n, W.put_str(x, rest))
    case Ar.TStr{x}:
      W.put_nat(2n, W.put_str(x, rest))
    case Ar.TOne{}:
      W.put_nat(3n, rest)
    case Ar.TObj{}:
      W.put_nat(4n, rest)
    case Ar.TArr{}:
      W.put_nat(5n, rest)

def put_mto(m: Maybe<&2, Ar.To>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{t}:
      W.put_nat(1n, put_to(t, rest))

def put_out(o: Ar.Out, rest: String) -> String:
  match o:
    case Ar.Out{k, m}:
      W.put_str(k, put_mto(m, rest))

def put_record(r: Ar.Record, rest: String) -> String:
  match r:
    case Ar.RAlias{f, t}:
      W.put_nat(0n, W.put_str(f, W.put_str(t, rest)))
    case Ar.RCoerce{k, f, t}:
      W.put_nat(1n, W.put_str(k, rest))

def put_refusal(x: Ar.Refusal, rest: String) -> String:
  match x:
    case Ar.Refused{k, h}:
      W.put_nat(0n, W.put_str(k, W.put_str(h, rest)))
    case Ar.Unknown{k, ns}:
      W.put_nat(1n, W.put_str(k, W.put_list(~String, ~W.put_str, ns, rest)))
    case Ar.Ambiguous{c, f, k}:
      W.put_nat(2n, W.put_str(c, W.put_str(f, W.put_str(k, rest))))

def put_verdict(v: Ar.Verdict) -> String:
  match v:
    case Ar.Repaired{os, rs}:
      W.put_nat(0n, W.put_list(~Ar.Out, ~put_out, os, W.put_list(~Ar.Record, ~put_record, rs, "")))
    case Ar.Rejected{x}:
      W.put_nat(1n, put_refusal(x, ""))

# the reply of a request: the model's verdict, encoded
def answer(q: Req) -> String:
  match q:
    case Req{sc, d, xs}:
      put_verdict(Ar.repair(sc, d, xs))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("arg_repair: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("arg_repair: malformed request")

# the entry: decode the request, answer the model's verdict
def ffi(input: String) -> String:
  ffi.got(get_req(input))
