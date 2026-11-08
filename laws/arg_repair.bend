# eukhe: the laws of area arg_repair

import Base
import ../bend/arg_repair.bend as Ar
import ../bend/ffi_arg_repair.bend as FAr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase
import ../spec/harness/arguments.bend as ArgSpec

# (H1) Charitable argument repair
# -------------------------------
# bend/arg_repair.bend, run as the compiled core by bend/ffi_arg_repair.bend
# (eukhe-bend rules/arg_repair.rs; asked by eukhe-durable
# harness/tool/arguments.rs `repair_arguments` for every tool call before
# validation, and through eukhe-core documents/contract.rs for every kernel
# `fs.*` request). Every input is free: any schema, dialect, sent keys,
# decodings and values.
#
# R1: the verdict on every call is the spec's (spec/harness/arguments.bend
#     S1-S5): the keys, the refusals in argument order, the values read,
#     the records.
# R2: every change gives exactly one record, in order, and nothing changes
#     without one: an argument's key decoded (S1), its key read as another
#     name, its value read as the declared type; nothing else is recorded.
# R3: a repaired call repairs to itself: repairing it again (its keys
#     plain, its values as read) reads no key as another name, reads no
#     value, records nothing, when the dialect is well formed (each alias's
#     canonical name declared, and not refused). NOT pinned: a key encoded
#     in more than 3 JSON string layers decodes one layer more each time
#     (Rust decodes at most 3).
# R4: a declared key that is not decoded is never renamed; a key no alias
#     names is never renamed; no argument is dropped or added.
# R5: an undeclared alias is read as its first canonical name, a declared
#     one for a well-formed dialect.
# R6: a refused key refuses the call, whatever else is sent; a closed
#     schema refuses a key it does not declare and no alias names. The
#     first such argument names it: refused with the dialect's first hint
#     for it, unknown with the declared names in order. An open schema
#     keeps an unknown key (R4).
# R7: a value is read as its declared type exactly when the spec's S4
#     spells it, and only as that type: a boolean for `boolean`, a number
#     for `integer` and `number`, a string for `string`, the object for
#     `object`, an array for `array`.
# R8: the entry answers each request Rust writes (the grammar of
#     bend/ffi_arg_repair.bend; every length within the wire) with the
#     spec's verdict spelled, reads exactly the request and nothing after
#     it, and answers any other input with the exact error form
#     `E arg_repair: malformed request`.
# R9: an alias's canonical name is admitted as that name sent would be: a
#     refused name refuses the call (its first hint), a name a closed
#     schema does not declare is unknown (the declared names), each
#     naming the canonical name; so every repaired call repairs to itself,
#     whatever the dialect.

# Spec helpers
# ------------

# R3: a value as read, as Rust sends it back: a string with its text and
# no other reading (a string read is only ever read for `string`, which
# reads no string)
def ar_to_val(t: Ar.To) -> Ar.Val:
  match t:
    case Ar.TBool{b}:
      Ar.VBool{b}
    case Ar.TNum{x}:
      Ar.VNum{x}
    case Ar.TStr{x}:
      Ar.VStr{Some{x}, None{}, Ar.SPlain{}}
    case Ar.TOne{}:
      Ar.VArr{}
    case Ar.TObj{}:
      Ar.VObj{}
    case Ar.TArr{}:
      Ar.VArr{}

def ar_value(v: Ar.Val, m: Maybe<&2, Ar.To>) -> Ar.Val:
  match m:
    case None{}:
      v
    case Some{t}:
      ar_to_val(t)

# R3: the repaired call, sent again: each out's name, plain, with its value
# as read (the sent value when kept)
def ar_after.one(a: Ar.Arg, o: Ar.Out) -> Ar.Arg:
  match a:
    case Ar.Arg{k, p, v}:
      match o:
        case Ar.Out{c, m}:
          Ar.Arg{c, None{}, ar_value(v, m)}

def ar_after(args: List<&2, Ar.Arg>, os: List<&2, Ar.Out>) -> List<&2, Ar.Arg>:
  match args:
    case Nil{}:
      Nil{}
    case a <> t:
      match os:
        case Nil{}:
          Nil{}
        case o <> u:
          ar_after.one(a, o) <> ar_after(t, u)

# R3: the outs of a call that changes nothing
def ar_kept(os: List<&2, Ar.Out>) -> List<&2, Ar.Out>:
  match os:
    case Nil{}:
      Nil{}
    case o <> t:
      match o:
        case Ar.Out{c, m}:
          Ar.Out{c, None{}} <> ar_kept(t)

def ar_wf.alias(+ps: List<&2, Ar.Prop>, +rs: List<&2, Ar.KV>, als: List<&2, Ar.KV>) -> Bool:
  match als:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case Ar.KV{a, +c}:
          Bool.and(Bool.and(ArgSpec.is_some(ArgSpec.declared(c, ps)), Bool.not(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs)))), ar_wf.alias(ps, rs, t))

# R3, R5: a well-formed dialect: each alias's canonical name is declared
# and not refused
def ar_wf(sc: Ar.Schema, d: Ar.Dialect) -> Bool:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, rs}:
          ar_wf.alias(ps, rs, als)

# the key a sent argument is read as before its name (S1)
def ar_cur(dm: Maybe<&2, String>, k: String) -> String:
  match dm:
    case None{}:
      k
    case Some{p}:
      p

def ar_dec_rec(dm: Maybe<&2, String>, k: String) -> List<&2, Ar.Record>:
  match dm:
    case None{}:
      Nil{}
    case Some{p}:
      [Ar.RAlias{k, p}]

def ar_changes.one(+dm: Maybe<&2, String>, +k: String, v: Ar.Val, o: Ar.Out) -> List<&2, Ar.Record>:
  match o:
    case Ar.Out{+c, +m}:
      +cur = ar_cur(dm, k)
      List.append(&2, Ar.Record, ar_dec_rec(dm, k), List.append(&2, Ar.Record, ArgSpec.renamed(String.eq(c, cur), cur, c), ArgSpec.read_rec(c, v, m)))

# R2: the changes of a call, from the sent arguments and their outs: per
# argument, its decoding, its renaming, its value read
def ar_changes.arg(+ks: List<&2, String>, a: Ar.Arg, o: Ar.Out) -> List<&2, Ar.Record>:
  match a:
    case Ar.Arg{+k, p, v}:
      ar_changes.one(ArgSpec.decoding(ks, k, p), k, v, o)

def ar_changes(+ks: List<&2, String>, args: List<&2, Ar.Arg>, os: List<&2, Ar.Out>) -> List<&2, Ar.Record>:
  match args:
    case Nil{}:
      Nil{}
    case a <> t:
      match os:
        case Nil{}:
          Nil{}
        case o <> u:
          List.append(&2, Ar.Record, ar_changes.arg(ks, a, o), ar_changes(ks, t, u))

# R2: a verdict with its records replaced by the changes of its outs
def ar_rec(+args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Ar.Verdict:
  match v:
    case Ar.Repaired{+os, rs}:
      Ar.Repaired{os, ar_changes(ArgSpec.sent_keys(args), args, os)}
    case Ar.Rejected{x}:
      Ar.Rejected{x}

def ar_implies(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      True{}

def ar_none(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

def ar_keys_ok.one(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, dm: Maybe<&2, String>, +k: String, +c: String) -> Bool:
  +plain = ar_none(dm)
  Bool.and(ar_implies(Bool.and(plain, ArgSpec.is_some(ArgSpec.declared(k, ps))), String.eq(c, k)), ar_implies(Bool.and(plain, ar_none(ArgSpec.first_text(k, als))), String.eq(c, k)))

def ar_keys_ok.arg(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, a: Ar.Arg, o: Ar.Out) -> Bool:
  match a:
    case Ar.Arg{+k, p, v}:
      match o:
        case Ar.Out{c, m}:
          ar_keys_ok.one(ps, als, ArgSpec.decoding(ks, k, p), k, c)

def ar_keys_ok.go(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, args: List<&2, Ar.Arg>, os: List<&2, Ar.Out>) -> Bool:
  match args:
    case Nil{}:
      match os:
        case Nil{}:
          True{}
        case o <> u:
          False{}
    case a <> t:
      match os:
        case Nil{}:
          False{}
        case o <> u:
          Bool.and(ar_keys_ok.arg(ps, als, ks, a, o), ar_keys_ok.go(ps, als, ks, t, u))

# R4: one out per argument, in order, and an argument whose key is not
# decoded keeps its key when the key is declared, and when no alias names
# it
def ar_keys_ok(sc: Ar.Schema, d: Ar.Dialect, +args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Bool:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, xs}:
          match v:
            case Ar.Repaired{os, rs}:
              ar_keys_ok.go(ps, als, ArgSpec.sent_keys(args), args, os)
            case Ar.Rejected{x}:
              True{}

def ar_alias_ok.at(m: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cur: String, +c: String) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      ar_implies(Bool.not(ArgSpec.is_some(ArgSpec.declared(cur, ps))), Bool.and(String.eq(c, a), ArgSpec.is_some(ArgSpec.declared(a, ps))))

def ar_alias_ok.arg(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, a: Ar.Arg, o: Ar.Out) -> Bool:
  match a:
    case Ar.Arg{+k, p, v}:
      match o:
        case Ar.Out{c, m}:
          +cur = ar_cur(ArgSpec.decoding(ks, k, p), k)
          ar_alias_ok.at(ArgSpec.first_text(cur, als), ps, cur, c)

def ar_alias_ok.go(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, args: List<&2, Ar.Arg>, os: List<&2, Ar.Out>) -> Bool:
  match args:
    case Nil{}:
      True{}
    case a <> t:
      match os:
        case Nil{}:
          True{}
        case o <> u:
          Bool.and(ar_alias_ok.arg(ps, als, ks, a, o), ar_alias_ok.go(ps, als, ks, t, u))

# R5: each argument whose key (decoded) is an undeclared alias is read as
# the alias's first canonical name, a declared one
def ar_alias_ok(sc: Ar.Schema, d: Ar.Dialect, +args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Bool:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, xs}:
          match v:
            case Ar.Repaired{os, rs}:
              ar_alias_ok.go(ps, als, ArgSpec.sent_keys(args), args, os)
            case Ar.Rejected{x}:
              True{}

def ar_rejected(v: Ar.Verdict) -> Bool:
  match v:
    case Ar.Repaired{os, rs}:
      False{}
    case Ar.Rejected{x}:
      True{}

def ar_some_refused.go(+rs: List<&2, Ar.KV>, +ks: List<&2, String>, args: List<&2, Ar.Arg>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Ar.Arg{+k, p, v}:
          Bool.or(Maybe.is_some(&2, String, ArgSpec.first_text(ar_cur(ArgSpec.decoding(ks, k, p), k), rs)), ar_some_refused.go(rs, ks, t))

# R6: some argument's key (decoded) is refused
def ar_some_refused(d: Ar.Dialect, +args: List<&2, Ar.Arg>) -> Bool:
  match d:
    case Ar.Dialect{als, rs}:
      ar_some_refused.go(rs, ArgSpec.sent_keys(args), args)

def ar_some_unknown.go(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, args: List<&2, Ar.Arg>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Ar.Arg{+k, p, v}:
          +cur = ar_cur(ArgSpec.decoding(ks, k, p), k)
          Bool.or(Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(cur, ps))), ar_none(ArgSpec.first_text(cur, als))), ar_some_unknown.go(ps, als, ks, t))

# R6: some argument's key (decoded) is undeclared and no alias
def ar_some_unknown(sc: Ar.Schema, d: Ar.Dialect, +args: List<&2, Ar.Arg>) -> Bool:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, rs}:
          ar_some_unknown.go(ps, als, ArgSpec.sent_keys(args), args)

def ar_bad_target(+ps: List<&2, Ar.Prop>, cl: Bool, +rs: List<&2, Ar.KV>, m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+c}:
      Bool.or(Maybe.is_some(&2, String, ArgSpec.first_text(c, rs)), Bool.and(cl, Bool.not(ArgSpec.is_some(ArgSpec.declared(c, ps)))))

def ar_some_bad_alias.go(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, args: List<&2, Ar.Arg>) -> Bool:
  match args:
    case Nil{}:
      False{}
    case a <> t:
      match a:
        case Ar.Arg{+k, p, v}:
          +cur = ar_cur(ArgSpec.decoding(ks, k, p), k)
          Bool.or(Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(cur, ps))), ar_bad_target(ps, cl, rs, ArgSpec.first_text(cur, als))), ar_some_bad_alias.go(ps, cl, als, rs, ks, t))

# R9: some argument's key (decoded) is an undeclared alias whose first
# canonical name is refused, or not declared by a closed schema
def ar_some_bad_alias(sc: Ar.Schema, d: Ar.Dialect, +args: List<&2, Ar.Arg>) -> Bool:
  match sc:
    case Ar.Schema{ps, cl}:
      match d:
        case Ar.Dialect{als, rs}:
          ar_some_bad_alias.go(ps, cl, als, rs, ArgSpec.sent_keys(args), args)

def ar_is_kind(m: Maybe<&2, String>, +t: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      String.eq(x, t)

def ar_typed.to(+m: Maybe<&2, String>, t: Ar.To) -> Bool:
  match t:
    case Ar.TBool{b}:
      ar_is_kind(m, "boolean")
    case Ar.TNum{x}:
      Bool.or(ar_is_kind(m, "integer"), ar_is_kind(m, "number"))
    case Ar.TStr{x}:
      ar_is_kind(m, "string")
    case Ar.TOne{}:
      ar_is_kind(m, "array")
    case Ar.TObj{}:
      ar_is_kind(m, "object")
    case Ar.TArr{}:
      ar_is_kind(m, "array")

# R7: a value read is of the declared argument's type (none read: no
# claim)
def ar_typed.read(p: Maybe<&2, Ar.Prop>, t: Ar.To) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{q}:
      match q:
        case Ar.Prop{n, k, i}:
          ar_typed.to(k, t)

def ar_typed(p: Maybe<&2, Ar.Prop>, r: Maybe<&2, Ar.To>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{t}:
      ar_typed.read(p, t)

# Fixtures: the Rust tests' schemas and dialects
# ----------------------------------------------

def ar_s(x: String) -> Ar.Val:
  Ar.VStr{Some{x}, None{}, Ar.SPlain{}}

def ar_grep() -> Ar.Schema:
  Ar.Schema{[Ar.Prop{"path", Some{"string"}, None{}}, Ar.Prop{"case", Some{"boolean"}, None{}}, Ar.Prop{"skip", Some{"integer"}, None{}}], True{}}

def ar_grep_dialect() -> Ar.Dialect:
  Ar.Dialect{[Ar.KV{"file_path", "path"}], [Ar.KV{"old_string", "send a hashline patch"}]}

def ar_edit() -> Ar.Schema:
  Ar.Schema{[Ar.Prop{"path", Some{"string"}, None{}}, Ar.Prop{"paths", Some{"array"}, Some{"string"}}, Ar.Prop{"edits", Some{"array"}, Some{"object"}}, Ar.Prop{"options", Some{"object"}, None{}}, Ar.Prop{"lines", Some{"array"}, Some{"integer"}}, Ar.Prop{"ranges", Some{"array"}, Some{"integer"}}, Ar.Prop{"title", Some{"string"}, None{}}], True{}}

def ar_arg(k: String, v: Ar.Val) -> Ar.Arg:
  Ar.Arg{k, None{}, v}

# R8: the spelling of a request and of its reply
# ---------------------------------------------

def ar_w_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def ar_w_prop(p: Ar.Prop, rest: String) -> String:
  match p:
    case Ar.Prop{n, k, i}:
      Wr.put_str(n, ar_w_ms(k, ar_w_ms(i, rest)))

def ar_w_props.items(ps: List<&2, Ar.Prop>, rest: String) -> String:
  match ps:
    case Nil{}:
      rest
    case p <> t:
      ar_w_prop(p, ar_w_props.items(t, rest))

def ar_w_kv(e: Ar.KV, rest: String) -> String:
  match e:
    case Ar.KV{k, x}:
      Wr.put_str(k, Wr.put_str(x, rest))

def ar_w_kvs.items(xs: List<&2, Ar.KV>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case e <> t:
      ar_w_kv(e, ar_w_kvs.items(t, rest))

def ar_w_shape(sh: Ar.Shape, rest: String) -> String:
  match sh:
    case Ar.SPlain{}:
      Wr.put_nat(0n, rest)
    case Ar.SBrace{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))
    case Ar.SBracket{b}:
      Wr.put_nat(2n, Wr.put_bool(b, rest))

def ar_w_val(v: Ar.Val, rest: String) -> String:
  match v:
    case Ar.VNull{}:
      Wr.put_nat(0n, rest)
    case Ar.VBool{b}:
      Wr.put_nat(1n, Wr.put_bool(b, rest))
    case Ar.VNum{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))
    case Ar.VStr{t, n, sh}:
      Wr.put_nat(3n, ar_w_ms(t, ar_w_ms(n, ar_w_shape(sh, rest))))
    case Ar.VArr{}:
      Wr.put_nat(4n, rest)
    case Ar.VObj{}:
      Wr.put_nat(5n, rest)

def ar_w_arg(a: Ar.Arg, rest: String) -> String:
  match a:
    case Ar.Arg{k, p, v}:
      Wr.put_str(k, ar_w_ms(p, ar_w_val(v, rest)))

def ar_w_args.items(xs: List<&2, Ar.Arg>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case a <> t:
      ar_w_arg(a, ar_w_args.items(t, rest))

def ar_w_req(q: FAr.Req, rest: String) -> String:
  match q:
    case FAr.Req{sc, d, +xs}:
      match sc:
        case Ar.Schema{+ps, cl}:
          match d:
            case Ar.Dialect{+als, +rs}:
              Wr.put_nat(List.length(&2, Ar.Prop, ps), ar_w_props.items(ps, Wr.put_bool(cl, Wr.put_nat(List.length(&2, Ar.KV, als), ar_w_kvs.items(als, Wr.put_nat(List.length(&2, Ar.KV, rs), ar_w_kvs.items(rs, Wr.put_nat(List.length(&2, Ar.Arg, xs), ar_w_args.items(xs, rest)))))))))

def ar_w_to(t: Ar.To, rest: String) -> String:
  match t:
    case Ar.TBool{b}:
      Wr.put_nat(0n, Wr.put_bool(b, rest))
    case Ar.TNum{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case Ar.TStr{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))
    case Ar.TOne{}:
      Wr.put_nat(3n, rest)
    case Ar.TObj{}:
      Wr.put_nat(4n, rest)
    case Ar.TArr{}:
      Wr.put_nat(5n, rest)

def ar_w_mto(m: Maybe<&2, Ar.To>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, ar_w_to(x, rest))

def ar_w_out(o: Ar.Out, rest: String) -> String:
  match o:
    case Ar.Out{k, m}:
      Wr.put_str(k, ar_w_mto(m, rest))

def ar_w_outs.items(os: List<&2, Ar.Out>, rest: String) -> String:
  match os:
    case Nil{}:
      rest
    case o <> t:
      ar_w_out(o, ar_w_outs.items(t, rest))

def ar_w_rec(r: Ar.Record, rest: String) -> String:
  match r:
    case Ar.RAlias{f, x}:
      Wr.put_nat(0n, Wr.put_str(f, Wr.put_str(x, rest)))
    case Ar.RCoerce{k, f, x}:
      Wr.put_nat(1n, Wr.put_str(k, rest))

def ar_w_recs.items(rs: List<&2, Ar.Record>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> t:
      ar_w_rec(r, ar_w_recs.items(t, rest))

def ar_w_verdict(v: Ar.Verdict) -> String:
  match v:
    case Ar.Repaired{+os, +rs}:
      Wr.put_nat(0n, Wr.put_nat(List.length(&2, Ar.Out, os), ar_w_outs.items(os, Wr.put_nat(List.length(&2, Ar.Record, rs), ar_w_recs.items(rs, "")))))
    case Ar.Rejected{x}:
      match x:
        case Ar.Refused{k, h}:
          Wr.put_nat(1n, Wr.put_nat(0n, Wr.put_str(k, Wr.put_str(h, ""))))
        case Ar.Unknown{k, ns}:
          Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_str(k, LawsBase.wire_spell_strs(ns, ""))))
        case Ar.Ambiguous{c, f, k}:
          Wr.put_nat(1n, Wr.put_nat(2n, Wr.put_str(c, Wr.put_str(f, Wr.put_str(k, "")))))

def ar_w_reply(q: FAr.Req) -> String:
  match q:
    case FAr.Req{sc, d, xs}:
      ar_w_verdict(ArgSpec.repair(sc, d, xs))

def ar_fit_ms(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      LawsBase.wire_fits(String.length(x))

def ar_fit_prop(p: Ar.Prop) -> Bool:
  match p:
    case Ar.Prop{+n, k, i}:
      Bool.and(LawsBase.wire_fits(String.length(n)), Bool.and(ar_fit_ms(k), ar_fit_ms(i)))

def ar_fit_props(ps: List<&2, Ar.Prop>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case p <> t:
      Bool.and(ar_fit_prop(p), ar_fit_props(t))

def ar_fit_kv(e: Ar.KV) -> Bool:
  match e:
    case Ar.KV{+k, +x}:
      Bool.and(LawsBase.wire_fits(String.length(k)), LawsBase.wire_fits(String.length(x)))

def ar_fit_kvs(xs: List<&2, Ar.KV>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(ar_fit_kv(e), ar_fit_kvs(t))

def ar_fit_val(v: Ar.Val) -> Bool:
  match v:
    case Ar.VNull{}:
      True{}
    case Ar.VBool{b}:
      True{}
    case Ar.VNum{+x}:
      LawsBase.wire_fits(String.length(x))
    case Ar.VStr{t, n, sh}:
      Bool.and(ar_fit_ms(t), ar_fit_ms(n))
    case Ar.VArr{}:
      True{}
    case Ar.VObj{}:
      True{}

def ar_fit_arg(a: Ar.Arg) -> Bool:
  match a:
    case Ar.Arg{+k, p, v}:
      Bool.and(LawsBase.wire_fits(String.length(k)), Bool.and(ar_fit_ms(p), ar_fit_val(v)))

def ar_fit_args(xs: List<&2, Ar.Arg>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> t:
      Bool.and(ar_fit_arg(a), ar_fit_args(t))

# every length of the request fits the wire
def ar_fit_req(q: FAr.Req) -> Bool:
  match q:
    case FAr.Req{sc, d, +xs}:
      match sc:
        case Ar.Schema{+ps, cl}:
          match d:
            case Ar.Dialect{+als, +rs}:
              Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Prop, ps)), Bool.and(ar_fit_props(ps), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, als)), Bool.and(ar_fit_kvs(als), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.KV, rs)), Bool.and(ar_fit_kvs(rs), Bool.and(LawsBase.wire_fits(List.length(&2, Ar.Arg, xs)), ar_fit_args(xs))))))))

# Laws: the decision (R1-R7)
# --------------------------

# LAW arg_repair_spec (R1): the verdict on every call is the spec's
# EXCLUDES: a key decoded though the decoding is sent too, a refused key
#   read as an alias, an alias read over a declared key, an unknown key kept
#   by a closed schema, refusals out of argument order, a value read as
#   another type, records out of order
law arg_repair_spec:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  {Ar.repair(sc, d, args) == ArgSpec.repair(sc, d, args) : Ar.Verdict}

# LAW arg_repair_recorded (R2): the records of every repaired call are
# exactly its changes, in order: one per decoded key, per key read as
# another name, per value read
# EXCLUDES: a silent rename or coercion, a record for a kept key or value,
#   a record twice, records out of order, a coercion record naming the sent
#   key instead of the name or another value
law arg_repair_recorded:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  {Ar.repair(sc, d, args) == ar_rec(args, Ar.repair(sc, d, args)) : Ar.Verdict}

# LAW arg_repair_idempotent (R3): repairing a repaired call changes
# nothing: the same names, no value read, no record
# EXCLUDES: an alias chain read one link per repair, a value read twice
#   (a string read as a number read as a string), a repaired call refused
law arg_repair_idempotent:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for +os: List<&2, Ar.Out>
  for +rs: List<&2, Ar.Record>
  for wf: {ar_wf(sc, d) == True{} : Bool}
  for ok: {Ar.repair(sc, d, args) == Ar.Repaired{os, rs} : Ar.Verdict}
  {Ar.repair(sc, d, ar_after(args, os)) == Ar.Repaired{ar_kept(os), Nil{}} : Ar.Verdict}

# LAW arg_repair_never_renames (R4): a repaired call has one out per sent
# argument, in order; a key not decoded keeps its name when it is declared
# (alias or not) and when no alias names it
# EXCLUDES: a declared key read as an alias's canonical name, an open
#   schema's unknown key renamed, a dropped or added argument
law arg_repair_never_renames:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  {ar_keys_ok(sc, d, args, Ar.repair(sc, d, args)) == True{} : Bool}

# LAW arg_repair_alias_maps_to_declared (R5): an undeclared alias is read
# as its first canonical name, declared when the dialect is well formed
# EXCLUDES: a later alias's name read, an alias kept as sent, an alias read
#   as a name the schema does not declare
law arg_repair_alias_maps_to_declared:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for wf: {ar_wf(sc, d) == True{} : Bool}
  {ar_alias_ok(sc, d, args, Ar.repair(sc, d, args)) == True{} : Bool}

# LAW arg_repair_refused_rejects (R6): a call with a refused key anywhere is
# refused
# EXCLUDES: a refused key dropped, renamed or kept, a refusal only for the
#   first argument
law arg_repair_refused_rejects:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for bad: {ar_some_refused(d, args) == True{} : Bool}
  {ar_rejected(Ar.repair(sc, d, args)) == True{} : Bool}

# LAW arg_repair_unknown_rejects (R6): a closed schema refuses a call with
# a key, anywhere, it does not declare and no alias names
# EXCLUDES: an unknown key dropped or kept by a closed schema
law arg_repair_unknown_rejects:
  for +ps: List<&2, Ar.Prop>
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for bad: {ar_some_unknown(Ar.Schema{ps, True{}}, d, args) == True{} : Bool}
  {ar_rejected(Ar.repair(Ar.Schema{ps, True{}}, d, args)) == True{} : Bool}

# LAW arg_repair_refused_exact (R6): a first argument with a refused key
# (not decoded) names the key and the dialect's first hint for it
# EXCLUDES: another hint, another key, a refusal of another kind
law arg_repair_refused_exact:
  for +sc: Ar.Schema
  for +als: List<&2, Ar.KV>
  for +rs: List<&2, Ar.KV>
  for +k: String
  for +h: String
  for +v: Ar.Val
  for +t: List<&2, Ar.Arg>
  for hit: {ArgSpec.first_text(k, rs) == Some{h} : Maybe<&2, String>}
  {Ar.repair(sc, Ar.Dialect{als, rs}, Ar.Arg{k, None{}, v} <> t) == Ar.Rejected{Ar.Refused{k, h}} : Ar.Verdict}

# LAW arg_repair_unknown_exact (R6): a closed schema's first argument with
# an undeclared key no alias names and no refusal names (not decoded) is
# unknown, naming the declared names in order
# EXCLUDES: valid names out of order or missing, another key named
law arg_repair_unknown_exact:
  for +ps: List<&2, Ar.Prop>
  for +als: List<&2, Ar.KV>
  for +rs: List<&2, Ar.KV>
  for +k: String
  for +v: Ar.Val
  for +t: List<&2, Ar.Arg>
  for nr: {ArgSpec.first_text(k, rs) == None{} : Maybe<&2, String>}
  for na: {ArgSpec.first_text(k, als) == None{} : Maybe<&2, String>}
  for nd: {ArgSpec.declared(k, ps) == None{} : Maybe<&2, Ar.Prop>}
  {Ar.repair(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, Ar.Arg{k, None{}, v} <> t) == Ar.Rejected{Ar.Unknown{k, ArgSpec.declared_names(ps)}} : Ar.Verdict}

# LAW arg_repair_alias_refused_exact (R9): a first argument whose key (not
# decoded, not refused) is an undeclared alias of a refused name refuses
# the call as that name sent would: the name and its first hint
# EXCLUDES: the refused name passed to the tool under the alias, the alias
#   named instead of the refused name, another hint
law arg_repair_alias_refused_exact:
  for +ps: List<&2, Ar.Prop>
  for +cl: Bool
  for +als: List<&2, Ar.KV>
  for +rs: List<&2, Ar.KV>
  for +k: String
  for +c: String
  for +h: String
  for +v: Ar.Val
  for +t: List<&2, Ar.Arg>
  for nr: {ArgSpec.first_text(k, rs) == None{} : Maybe<&2, String>}
  for nd: {ArgSpec.declared(k, ps) == None{} : Maybe<&2, Ar.Prop>}
  for al: {ArgSpec.first_text(k, als) == Some{c} : Maybe<&2, String>}
  for hit: {ArgSpec.first_text(c, rs) == Some{h} : Maybe<&2, String>}
  {Ar.repair(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, Ar.Arg{k, None{}, v} <> t) == Ar.Rejected{Ar.Refused{c, h}} : Ar.Verdict}

# LAW arg_repair_alias_unknown_exact (R9): a closed schema's first argument
# whose key (not decoded, not refused) is an undeclared alias of a name it
# does not declare (and no refusal names) is unknown as that name sent
# would be: the name and the declared names in order
# EXCLUDES: an undeclared name passed to the tool under the alias, the
#   alias named instead of its canonical name
law arg_repair_alias_unknown_exact:
  for +ps: List<&2, Ar.Prop>
  for +als: List<&2, Ar.KV>
  for +rs: List<&2, Ar.KV>
  for +k: String
  for +c: String
  for +v: Ar.Val
  for +t: List<&2, Ar.Arg>
  for nr: {ArgSpec.first_text(k, rs) == None{} : Maybe<&2, String>}
  for nd: {ArgSpec.declared(k, ps) == None{} : Maybe<&2, Ar.Prop>}
  for al: {ArgSpec.first_text(k, als) == Some{c} : Maybe<&2, String>}
  for cr: {ArgSpec.first_text(c, rs) == None{} : Maybe<&2, String>}
  for cd: {ArgSpec.declared(c, ps) == None{} : Maybe<&2, Ar.Prop>}
  {Ar.repair(Ar.Schema{ps, True{}}, Ar.Dialect{als, rs}, Ar.Arg{k, None{}, v} <> t) == Ar.Rejected{Ar.Unknown{c, ArgSpec.declared_names(ps)}} : Ar.Verdict}

# LAW arg_repair_alias_rejects (R9): a call with an argument, anywhere,
# whose key (decoded) is an undeclared alias of a refused name, or of a
# name a closed schema does not declare, is refused
# EXCLUDES: an alias's canonical name passed without the check a sent key
#   gets, for a later argument too
law arg_repair_alias_rejects:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for bad: {ar_some_bad_alias(sc, d, args) == True{} : Bool}
  {ar_rejected(Ar.repair(sc, d, args)) == True{} : Bool}

# LAW arg_repair_idempotent_any (R3, R9): repairing a repaired call changes
# nothing, for every dialect: the same names, no value read, no record
# EXCLUDES: an alias read as a name the schema does not declare or the
#   dialect refuses, which the call repaired again rejects; an alias chain
#   read one link per repair; a value read twice
law arg_repair_idempotent_any:
  for +sc: Ar.Schema
  for +d: Ar.Dialect
  for +args: List<&2, Ar.Arg>
  for +os: List<&2, Ar.Out>
  for +rs: List<&2, Ar.Record>
  for ok: {Ar.repair(sc, d, args) == Ar.Repaired{os, rs} : Ar.Verdict}
  {Ar.repair(sc, d, ar_after(args, os)) == Ar.Repaired{ar_kept(os), Nil{}} : Ar.Verdict}

# LAW arg_repair_coerce_spec (R7): every value is read as the spec's S4
# reads it, for every declared argument
# EXCLUDES: a boolean word in another case set, padding not trimmed, an
#   integer past i64 or with a sign doubled, a lone string wrapped for
#   items of another type, `[...]` text wrapped instead of read
law arg_repair_coerce_spec:
  for +p: Maybe<&2, Ar.Prop>
  for +v: Ar.Val
  {Ar.coerce(p, v) == ArgSpec.read(p, v) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_typed (R7): a value is read only as its declared
# argument's type
# EXCLUDES: a boolean read for an integer, a string read for a number, an
#   array read for an object, a value read for an undeclared argument
law arg_repair_coerce_typed:
  for +p: Maybe<&2, Ar.Prop>
  for +v: Ar.Val
  {ar_typed(p, Ar.coerce(p, v)) == True{} : Bool}

# LAW arg_repair_example (R1, R2): anchor: the Rust tests: an alias with a
# boolean and an integer read; strings that spell no declared scalar
# EXCLUDES: a spec that drifts from the Rust it replaced
law arg_repair_example:
  {[Ar.repair(ar_grep(), ar_grep_dialect(), [ar_arg("file_path", ar_s("a.rs")), ar_arg("case", ar_s("False")), ar_arg("skip", ar_s(" 3 "))]), Ar.repair(ar_grep(), ar_grep_dialect(), [ar_arg("path", ar_s("true")), ar_arg("case", ar_s("maybe"))])] == [Ar.Repaired{[Ar.Out{"path", None{}}, Ar.Out{"case", Some{Ar.TBool{False{}}}}, Ar.Out{"skip", Some{Ar.TNum{"3"}}}], [Ar.RAlias{"file_path", "path"}, Ar.RCoerce{"case", ar_s("False"), Ar.TBool{False{}}}, Ar.RCoerce{"skip", ar_s(" 3 "), Ar.TNum{"3"}}]}, Ar.Repaired{[Ar.Out{"path", None{}}, Ar.Out{"case", None{}}], Nil{}}] : List<&2, Ar.Verdict>}

# LAW arg_repair_refusal_example (R6): anchor: the Rust tests: an unknown
# key, a key twice, a refused key, an encoded key whose plain key is sent
# too; an open schema keeps an unknown key
# EXCLUDES: a spec that drifts from the Rust it replaced
law arg_repair_refusal_example:
  {[Ar.repair(ar_grep(), ar_grep_dialect(), [ar_arg("pattern", ar_s("x"))]), Ar.repair(ar_grep(), ar_grep_dialect(), [ar_arg("path", ar_s("a")), ar_arg("file_path", ar_s("b"))]), Ar.repair(ar_grep(), ar_grep_dialect(), [ar_arg("old_string", ar_s("a"))]), Ar.repair(ar_grep(), ar_grep_dialect(), [Ar.Arg{"\"path\"", Some{"path"}, ar_s("a")}, ar_arg("path", ar_s("b"))]), Ar.repair(Ar.Schema{Nil{}, False{}}, Ar.Dialect{Nil{}, Nil{}}, [ar_arg("text", ar_s("hi"))])] == [Ar.Rejected{Ar.Unknown{"pattern", ["path", "case", "skip"]}}, Ar.Rejected{Ar.Ambiguous{"path", "path", "file_path"}}, Ar.Rejected{Ar.Refused{"old_string", "send a hashline patch"}}, Ar.Rejected{Ar.Unknown{"\"path\"", ["path", "case", "skip"]}}, Ar.Repaired{[Ar.Out{"text", None{}}], Nil{}}] : List<&2, Ar.Verdict>}

# LAW arg_repair_decoded_example (R1, R2): anchor: the Rust test: keys in
# JSON strings decoded (two layers to an alias, one to a boolean)
# EXCLUDES: a decoded key not recorded, the alias read before the decoding
law arg_repair_decoded_example:
  {Ar.repair(ar_grep(), ar_grep_dialect(), [Ar.Arg{"\"\\\"file_path\\\"\"", Some{"file_path"}, ar_s("a.rs")}, Ar.Arg{"\"case\"", Some{"case"}, ar_s("yes")}]) == Ar.Repaired{[Ar.Out{"path", None{}}, Ar.Out{"case", Some{Ar.TBool{True{}}}}], [Ar.RAlias{"\"\\\"file_path\\\"\"", "file_path"}, Ar.RAlias{"file_path", "path"}, Ar.RAlias{"\"case\"", "case"}, Ar.RCoerce{"case", ar_s("yes"), Ar.TBool{True{}}}]} : Ar.Verdict}

# LAW arg_repair_container_example (R7): anchor: the Rust test: a number
# and a boolean read as strings, a lone string wrapped, JSON text read as
# an array and an object, broken JSON and a lone string for integer items
# kept
# EXCLUDES: a spec that drifts from the Rust it replaced
law arg_repair_container_example:
  {Ar.repair(ar_edit(), Ar.Dialect{Nil{}, Nil{}}, [ar_arg("path", Ar.VNum{"42"}), ar_arg("paths", ar_s("src/a.rs")), ar_arg("edits", Ar.VStr{Some{"[{}]"}, None{}, Ar.SBracket{True{}}}), ar_arg("options", Ar.VStr{Some{" {'dry': True} "}, None{}, Ar.SBrace{True{}}}), ar_arg("lines", Ar.VStr{Some{"[1,"}, None{}, Ar.SBracket{False{}}}), ar_arg("ranges", Ar.VStr{Some{"7"}, Some{"7.0"}, Ar.SPlain{}}), ar_arg("title", Ar.VBool{False{}})]) == Ar.Repaired{[Ar.Out{"path", Some{Ar.TStr{"42"}}}, Ar.Out{"paths", Some{Ar.TOne{}}}, Ar.Out{"edits", Some{Ar.TArr{}}}, Ar.Out{"options", Some{Ar.TObj{}}}, Ar.Out{"lines", None{}}, Ar.Out{"ranges", None{}}, Ar.Out{"title", Some{Ar.TStr{"false"}}}], [Ar.RCoerce{"path", Ar.VNum{"42"}, Ar.TStr{"42"}}, Ar.RCoerce{"paths", ar_s("src/a.rs"), Ar.TOne{}}, Ar.RCoerce{"edits", Ar.VStr{Some{"[{}]"}, None{}, Ar.SBracket{True{}}}, Ar.TArr{}}, Ar.RCoerce{"options", Ar.VStr{Some{" {'dry': True} "}, None{}, Ar.SBrace{True{}}}, Ar.TObj{}}, Ar.RCoerce{"title", Ar.VBool{False{}}, Ar.TStr{"false"}}]} : Ar.Verdict}

# LAW arg_repair_scalar_example (R7): anchor: spellings at the edges:
# White_Space (NBSP, ideographic space) trimmed, ASCII case, a `+` sign,
# leading zeros, `-0`, i64's bounds and one past, a sign alone, a long
# string (no text) for a boolean, an f64 reading for `number`, a string
# kept for `string`
# EXCLUDES: ASCII-only trimming, `on`/`off` dropped, an i64 bound off by
#   one, `-0` kept as `-0`, a sign without digits read
law arg_repair_scalar_example:
  {[Ar.coerce(Some{Ar.Prop{"b", Some{"boolean"}, None{}}}, ar_s("\u{a0}ON\u{3000}")), Ar.coerce(Some{Ar.Prop{"b", Some{"boolean"}, None{}}}, ar_s("No")), Ar.coerce(Some{Ar.Prop{"b", Some{"boolean"}, None{}}}, Ar.VStr{None{}, None{}, Ar.SPlain{}}), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("+007")), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("-0")), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("9223372036854775807")), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("9223372036854775808")), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("-9223372036854775808")), Ar.coerce(Some{Ar.Prop{"i", Some{"integer"}, None{}}}, ar_s("-")), Ar.coerce(Some{Ar.Prop{"n", Some{"number"}, None{}}}, Ar.VStr{Some{" 3 "}, Some{"3.0"}, Ar.SPlain{}}), Ar.coerce(Some{Ar.Prop{"s", Some{"string"}, None{}}}, ar_s("1")), Ar.coerce(None{}, ar_s("1"))] == [Some{Ar.TBool{True{}}}, Some{Ar.TBool{False{}}}, None{}, Some{Ar.TNum{"7"}}, Some{Ar.TNum{"0"}}, Some{Ar.TNum{"9223372036854775807"}}, None{}, Some{Ar.TNum{"-9223372036854775808"}}, None{}, Some{Ar.TNum{"3.0"}}, None{}, None{}] : List<&2, Maybe<&2, Ar.To>>}

# Laws: the entry (R8)
# --------------------

# LAW arg_repair_entry_answers (R8): the entry answers every request Rust
# spells, every length within the wire, with the spec's verdict spelled
# EXCLUDES: fields read in another order, the aliases and the refused keys
#   swapped, a value tag misread, a record or an out lost, a default
law arg_repair_entry_answers:
  for +q: FAr.Req
  for fit: {ar_fit_req(q) == True{} : Bool}
  {FAr.ffi(ar_w_req(q, "")) == ar_w_reply(q) : String}

# LAW arg_repair_entry_left_over (R8): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law arg_repair_entry_left_over:
  for +q: FAr.Req
  for +c: Char
  for +t: String
  for fit: {ar_fit_req(q) == True{} : Bool}
  {FAr.ffi(ar_w_req(q, SCon{c, t})) == Wr.err("arg_repair: malformed request") : String}

# LAW arg_repair_entry_reads (R8): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown value,
#   shape or Maybe tag, a short field, a list shorter than its count,
#   input left over)
law arg_repair_entry_reads:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FAr.ffi(s)) == False{} : Bool}
  exs q: FAr.Req
  {s == ar_w_req(q, "") : String} & {ar_fit_req(q) == True{} : Bool}

# LAW arg_repair_entry_refuses (R8): every error the entry answers is
# exactly `E arg_repair: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law arg_repair_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FAr.ffi(s)) == True{} : Bool}
  {FAr.ffi(s) == Wr.err("arg_repair: malformed request") : String}

# LAW arg_repair_entry_example (R8): anchor: the wire strings Rust sends
# and the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law arg_repair_entry_example:
  {[FAr.ffi("3,4,path1,6,string0,4,case1,7,boolean0,4,skip1,7,integer0,T1,9,file_path4,path1,10,old_string21,send a hashline patch3,9,file_path0,3,1,4,a.rs0,0,4,case0,3,1,5,False0,0,4,skip0,3,1,3, 3 0,0,"), FAr.ffi("0,F0,0,1,4,text0,3,0,0,0,"), FAr.ffi("0,T0,0,1,4,text0,0,"), FAr.ffi("0,F0,0,0,x"), FAr.ffi("0,F0,0,1,4,text0,6,")] == ["0,3,4,path0,4,case1,0,F4,skip1,1,1,33,0,9,file_path4,path1,4,case1,4,skip", "0,1,4,text0,0,", "1,1,4,text0,", Wr.err("arg_repair: malformed request"), Wr.err("arg_repair: malformed request")] : List<&2, String>}
