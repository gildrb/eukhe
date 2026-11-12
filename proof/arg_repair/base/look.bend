# eukhe: lemmas of the proofs of area arg_repair: the code's lookups
# compute the words the laws use (spec/harness/arguments.bend): a key among
# the sent keys, the sent keys, the declared names, the first declared
# argument of a name, the first text of a key, a key's decoding, the
# renaming and the reading records (induction over the list, rs.*)

import Base
import ../../../bend/arg_repair.bend as Ar
import ../../../spec/harness/arguments.bend as ArgSpec

def rs.has(+k: String, ks: List<&2, String>) -> {Ar.has(k, ks) == ArgSpec.member(k, ks) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +x <> +t:
      %rs.has(k, t) : {Bool.or(String.eq(k, x), Ar.has(k, t)) == Bool.or(String.eq(k, x), _) : Bool}
      {==}

def rs.keys(args: List<&2, Ar.Arg>) -> {Ar.keys(args) == ArgSpec.sent_keys(args) : List<&2, String>}:
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      match a:
        case Ar.Arg{+k, +p, +v}:
          %rs.keys(t) : {k <> Ar.keys(t) == k <> _ : List<&2, String>}
          {==}

def rs.names(ps: List<&2, Ar.Prop>) -> {Ar.names(ps) == ArgSpec.declared_names(ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      match p:
        case Ar.Prop{+n, +k, +i}:
          %rs.names(t) : {n <> Ar.names(t) == n <> _ : List<&2, String>}
          {==}

def rs.prop_at(b: Bool, p: Ar.Prop, r: Maybe<&2, Ar.Prop>) -> {Ar.prop.at(b, p, r) == ArgSpec.declared.at(b, p, r) : Maybe<&2, Ar.Prop>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.prop(+k: String, ps: List<&2, Ar.Prop>) -> {Ar.prop(k, ps) == ArgSpec.declared(k, ps) : Maybe<&2, Ar.Prop>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      match p:
        case Ar.Prop{+n, +i, +j}:
          %rs.prop(k, t) : {Ar.prop.at(String.eq(k, n), Ar.Prop{n, i, j}, Ar.prop(k, t)) == ArgSpec.declared.at(String.eq(k, n), Ar.Prop{n, i, j}, _) : Maybe<&2, Ar.Prop>}
          rs.prop_at(String.eq(k, n), Ar.Prop{n, i, j}, Ar.prop(k, t))

def rs.found(m: Maybe<&2, Ar.Prop>) -> {Ar.found(m) == ArgSpec.is_some(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      {==}

def rs.pick_at(b: Bool, x: String, r: Maybe<&2, String>) -> {Ar.pick.at(b, x, r) == ArgSpec.first_text.at(b, x, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.lookup(+k: String, kvs: List<&2, Ar.KV>) -> {Ar.lookup(k, kvs) == ArgSpec.first_text(k, kvs) : Maybe<&2, String>}:
  match kvs:
    case Nil{}:
      {==}
    case +e <> +t:
      match e:
        case Ar.KV{+x, +c}:
          %rs.lookup(k, t) : {Ar.pick.at(String.eq(k, x), c, Ar.lookup(k, t)) == ArgSpec.first_text.at(String.eq(k, x), c, _) : Maybe<&2, String>}
          rs.pick_at(String.eq(k, x), c, Ar.lookup(k, t))

def rs.keep(b: Bool, p: String) -> {Ar.decoded.of(b, p) == ArgSpec.decoding.keep(b, p) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.decoded(+ks: List<&2, String>, +k: String, m: Maybe<&2, String>) -> {Ar.decoded(ks, k, m) == ArgSpec.decoding(ks, k, m) : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      %rs.has(p, ks) : {Ar.decoded.of(Bool.or(String.eq(p, k), Ar.has(p, ks)), p) == ArgSpec.decoding.keep(Bool.or(String.eq(p, k), _), p) : Maybe<&2, String>}
      rs.keep(Bool.or(String.eq(p, k), Ar.has(p, ks)), p)

def rs.rename(same: Bool, k: String, c: String) -> {Ar.rename(same, k, c) == ArgSpec.renamed(same, k, c) : List<&2, Ar.Record>}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.coerced(c: String, v: Ar.Val, to: Maybe<&2, Ar.To>) -> {Ar.coerced(c, v, to) == ArgSpec.read_rec(c, v, to) : List<&2, Ar.Record>}:
  match to:
    case None{}:
      {==}
    case Some{+x}:
      {==}
