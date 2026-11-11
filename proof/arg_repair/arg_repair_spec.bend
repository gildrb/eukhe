# eukhe: the proof of LAW arg_repair_spec
#
# PROOF: each lookup of the model computes the spec's (induction over the
# list, rs.*); the name a key is read as is the spec's (rs.named); one
# argument's step is the spec's (rs.step, with arg_repair_coerce_spec for
# the value); the walk over the arguments is the spec's by induction, the
# names taken so far generalized (rs.go).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./arg_repair_coerce_spec.bend as PCoerceSpec

# Lookups
# -------

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

def rs.taken_at(b: Bool, x: String, r: Maybe<&2, String>) -> {Ar.pick.at(b, x, r) == ArgSpec.taken.at(b, x, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rs.first(+c: String, ss: List<&2, Ar.Seen>) -> {Ar.first_of(c, ss) == ArgSpec.taken(c, ss) : Maybe<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +t:
      match s:
        case Ar.Seen{+n, +k}:
          %rs.first(c, t) : {Ar.pick.at(String.eq(c, n), k, Ar.first_of(c, t)) == ArgSpec.taken.at(String.eq(c, n), k, _) : Maybe<&2, String>}
          rs.taken_at(String.eq(c, n), k, Ar.first_of(c, t))

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

# Names
# -----

def rs.closed(dec: Bool, cl: Bool, +k: String, +ps: List<&2, Ar.Prop>) -> {Ar.named.closed(dec, cl, k, ps) == ArgSpec.name.own(dec, cl, k, ps) : Ar.Named}:
  match dec:
    case True{}:
      {==}
    case False{}:
      match cl:
        case True{}:
          %rs.names(ps) : {Ar.NUnknown{k, Ar.names(ps)} == Ar.NUnknown{k, _} : Ar.Named}
          {==}
        case False{}:
          {==}

def rs.chain(al: Maybe<&2, String>, +c: String, +ps: List<&2, Ar.Prop>) -> {Ar.named.chain(al, c, ps) == ArgSpec.name.chain(al, c, ps) : Ar.Named}:
  match al:
    case None{}:
      {==}
    case Some{+e}:
      %rs.names(ps) : {Ar.NUnknown{c, Ar.names(ps)} == Ar.NUnknown{c, _} : Ar.Named}
      {==}

def rs.target(h: Maybe<&2, String>, dec: Bool, cl: Bool, al: Maybe<&2, String>, +c: String, +ps: List<&2, Ar.Prop>) -> {Ar.named.target(h, dec, cl, al, c, ps) == ArgSpec.name.target(h, dec, cl, al, c, ps) : Ar.Named}:
  match h:
    case Some{+x}:
      {==}
    case None{}:
      match dec:
        case True{}:
          {==}
        case False{}:
          match cl:
            case True{}:
              %rs.names(ps) : {Ar.NUnknown{c, Ar.names(ps)} == Ar.NUnknown{c, _} : Ar.Named}
              {==}
            case False{}:
              rs.chain(al, c, ps)

def rs.alias(al: Maybe<&2, String>, dec: Bool, cl: Bool, +k: String, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>) -> {Ar.named.alias(al, dec, cl, k, ps, als, rs) == ArgSpec.name.alias(al, dec, cl, k, ps, als, rs) : Ar.Named}:
  match al:
    case Some{+c}:
      match dec:
        case True{}:
          {==}
        case False{}:
          %rs.lookup(c, rs) : {Ar.named.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps) == ArgSpec.name.target(_, ArgSpec.is_some(ArgSpec.declared(c, ps)), cl, ArgSpec.first_text(c, als), c, ps) : Ar.Named}
          %rs.prop(c, ps) : {Ar.named.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps) == ArgSpec.name.target(Ar.lookup(c, rs), ArgSpec.is_some(_), cl, ArgSpec.first_text(c, als), c, ps) : Ar.Named}
          %rs.found(Ar.prop(c, ps)) : {Ar.named.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps) == ArgSpec.name.target(Ar.lookup(c, rs), _, cl, ArgSpec.first_text(c, als), c, ps) : Ar.Named}
          %rs.lookup(c, als) : {Ar.named.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps) == ArgSpec.name.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, _, c, ps) : Ar.Named}
          rs.target(Ar.lookup(c, rs), Ar.found(Ar.prop(c, ps)), cl, Ar.lookup(c, als), c, ps)
    case None{}:
      rs.closed(dec, cl, k, ps)

def rs.hint(h: Maybe<&2, String>, sc: Ar.Schema, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String) -> {Ar.named.hint(h, sc, als, rs, k) == ArgSpec.name.refused(h, sc, als, rs, k) : Ar.Named}:
  match h:
    case Some{+x}:
      {==}
    case None{}:
      match sc:
        case Ar.Schema{+ps, +cl}:
          %rs.lookup(k, als) : {Ar.named.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs) == ArgSpec.name.alias(_, ArgSpec.is_some(ArgSpec.declared(k, ps)), cl, k, ps, als, rs) : Ar.Named}
          %rs.prop(k, ps) : {Ar.named.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs) == ArgSpec.name.alias(Ar.lookup(k, als), ArgSpec.is_some(_), cl, k, ps, als, rs) : Ar.Named}
          %rs.found(Ar.prop(k, ps)) : {Ar.named.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs) == ArgSpec.name.alias(Ar.lookup(k, als), _, cl, k, ps, als, rs) : Ar.Named}
          rs.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, k, ps, als, rs)

# the name a key is read as is the spec's
def rs.named(+sc: Ar.Schema, d: Ar.Dialect, +k: String) -> {Ar.named(sc, d, k) == ArgSpec.name(sc, d, k) : Ar.Named}:
  match d:
    case Ar.Dialect{+als, +rs}:
      %rs.lookup(k, rs) : {Ar.named.hint(Ar.lookup(k, rs), sc, als, rs, k) == ArgSpec.name.refused(_, sc, als, rs, k) : Ar.Named}
      rs.hint(Ar.lookup(k, rs), sc, als, rs, k)

# Steps
# -----

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

def rs.ok(+same: Bool, +c: String, +to: Maybe<&2, Ar.To>, -r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val) -> {Ar.step.ok(same, c, to, r0, k, v) == ArgSpec.take.ok(same, c, to, r0, k, v) : Ar.Step}:
  %rs.rename(same, k, c) : {Ar.step.ok(same, c, to, r0, k, v) == Ar.StepOk{Ar.Out{c, to}, List.append(&2, Ar.Record, r0, List.append(&2, Ar.Record, _, ArgSpec.read_rec(c, v, to))), Ar.Seen{c, k}} : Ar.Step}
  %rs.coerced(c, v, to) : {Ar.step.ok(same, c, to, r0, k, v) == Ar.StepOk{Ar.Out{c, to}, List.append(&2, Ar.Record, r0, List.append(&2, Ar.Record, Ar.rename(same, k, c), _)), Ar.Seen{c, k}} : Ar.Step}
  {==}

def rs.free(f: Maybe<&2, String>, +c: String, +ps: List<&2, Ar.Prop>, -r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val) -> {Ar.step.first(f, c, ps, r0, k, v) == ArgSpec.take.free(f, c, ps, r0, k, v) : Ar.Step}:
  match f:
    case Some{+x}:
      {==}
    case None{}:
      %rs.prop(c, ps) : {Ar.step.ok(String.eq(c, k), c, Ar.coerce(Ar.prop(c, ps), v), r0, k, v) == ArgSpec.take.ok(String.eq(c, k), c, ArgSpec.read(_, v), r0, k, v) : Ar.Step}
      %ArgRepair.arg_repair_coerce_spec(Ar.prop(c, ps), v) : {Ar.step.ok(String.eq(c, k), c, Ar.coerce(Ar.prop(c, ps), v), r0, k, v) == ArgSpec.take.ok(String.eq(c, k), c, _, r0, k, v) : Ar.Step}
      rs.ok(String.eq(c, k), c, Ar.coerce(Ar.prop(c, ps), v), r0, k, v)

def rs.step_named(n: Ar.Named, +ps: List<&2, Ar.Prop>, +ss: List<&2, Ar.Seen>, -r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val) -> {Ar.step.named(n, ps, ss, r0, k, v) == ArgSpec.take.named(n, ps, ss, r0, k, v) : Ar.Step}:
  match n:
    case Ar.NRefused{+j, +x}:
      {==}
    case Ar.NUnknown{+j, +ns}:
      {==}
    case Ar.NAs{+c}:
      %rs.first(c, ss) : {Ar.step.first(Ar.first_of(c, ss), c, ps, r0, k, v) == ArgSpec.take.free(_, c, ps, r0, k, v) : Ar.Step}
      rs.free(Ar.first_of(c, ss), c, ps, r0, k, v)

def rs.key(sc: Ar.Schema, +d: Ar.Dialect, +ss: List<&2, Ar.Seen>, -r0: List<&2, Ar.Record>, +k: String, +v: Ar.Val) -> {Ar.step.key(sc, d, ss, r0, k, v) == ArgSpec.take.key(sc, d, ss, r0, k, v) : Ar.Step}:
  match sc:
    case Ar.Schema{+ps, +cl}:
      %rs.named(Ar.Schema{ps, cl}, d, k) : {Ar.step.named(Ar.named(Ar.Schema{ps, cl}, d, k), ps, ss, r0, k, v) == ArgSpec.take.named(_, ps, ss, r0, k, v) : Ar.Step}
      rs.step_named(Ar.named(Ar.Schema{ps, cl}, d, k), ps, ss, r0, k, v)

def rs.read(+sc: Ar.Schema, +d: Ar.Dialect, +ss: List<&2, Ar.Seen>, +k: String, dm: Maybe<&2, String>, +v: Ar.Val) -> {Ar.step.read(sc, d, ss, k, dm, v) == ArgSpec.take.decoded(sc, d, ss, k, dm, v) : Ar.Step}:
  match dm:
    case None{}:
      rs.key(sc, d, ss, Nil{}, k, v)
    case Some{+p}:
      rs.key(sc, d, ss, [Ar.RAlias{k, p}], p, v)

# one argument's step is the spec's
def rs.step(+sc: Ar.Schema, +d: Ar.Dialect, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, a: Ar.Arg) -> {Ar.step(sc, d, ks, ss, a) == ArgSpec.take(sc, d, ks, ss, a) : Ar.Step}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      %rs.decoded(ks, k, m) : {Ar.step.read(sc, d, ss, k, Ar.decoded(ks, k, m), v) == ArgSpec.take.decoded(sc, d, ss, k, _, v) : Ar.Step}
      rs.read(sc, d, ss, k, Ar.decoded(ks, k, m), v)

# The walk
# --------

def rs.next(st: Ar.Step, -ss: List<&2, Ar.Seen>) -> {Ar.seen.next(st, ss) == ArgSpec.walk.next(st, ss) : List<&2, Ar.Seen>}:
  match st:
    case Ar.StepOk{+o, +r, +s}:
      {==}
    case Ar.StepNo{+x}:
      {==}

def rs.cons(st: Ar.Step, rest: Ar.Verdict) -> {Ar.go.cons(st, rest) == ArgSpec.walk.cons(st, rest) : Ar.Verdict}:
  match st:
    case Ar.StepOk{+o, +r, +s}:
      match rest:
        case Ar.Repaired{+os, +rs}:
          {==}
        case Ar.Rejected{+x}:
          {==}
    case Ar.StepNo{+x}:
      {==}

def rs.go(args: List<&2, Ar.Arg>, +sc: Ar.Schema, +d: Ar.Dialect, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>) -> {Ar.go(args, sc, d, ks, ss) == ArgSpec.walk(args, sc, d, ks, ss) : Ar.Verdict}:
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      +st = Ar.step(sc, d, ks, ss, a)
      %rs.step(sc, d, ks, ss, a) : {Ar.go.cons(st, Ar.go(t, sc, d, ks, Ar.seen.next(st, ss))) == ArgSpec.walk.cons(_, ArgSpec.walk(t, sc, d, ks, ArgSpec.walk.next(_, ss))) : Ar.Verdict}
      %rs.next(st, ss) : {Ar.go.cons(st, Ar.go(t, sc, d, ks, Ar.seen.next(st, ss))) == ArgSpec.walk.cons(st, ArgSpec.walk(t, sc, d, ks, _)) : Ar.Verdict}
      %rs.go(t, sc, d, ks, Ar.seen.next(st, ss)) : {Ar.go.cons(st, Ar.go(t, sc, d, ks, Ar.seen.next(st, ss))) == ArgSpec.walk.cons(st, _) : Ar.Verdict}
      rs.cons(st, Ar.go(t, sc, d, ks, Ar.seen.next(st, ss)))

def ArgRepair.arg_repair_spec(sc, d, args):
  %rs.keys(args) : {Ar.go(args, sc, d, Ar.keys(args), Nil{}) == ArgSpec.walk(args, sc, d, _, Nil{}) : Ar.Verdict}
  rs.go(args, sc, d, Ar.keys(args), Nil{})
