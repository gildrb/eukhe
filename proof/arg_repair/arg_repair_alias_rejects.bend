# eukhe: the proof of LAW arg_repair_alias_rejects
#
# PROOF: by induction over the arguments, the names taken generalized
# (ba.go): when the bad alias is this argument's, its key read (decoded or
# not) is refused, or its canonical name is refused or unknown
# (ba.named), so its step refuses the call (ba.no); else the rest of the
# call is refused (the hypothesis), and a refusal of the rest refuses the
# call (ba.rest).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./arg_repair_spec.bend as PSpec

def ba.is_no(n: Ar.Named) -> Bool:
  match n:
    case Ar.NRefused{j, x}:
      True{}
    case Ar.NUnknown{j, ns}:
      True{}
    case Ar.NAs{c}:
      False{}

# Lookups as the spec's
# ---------------------

def ba.bt_eq(+ps: List<&2, Ar.Prop>, +cl: Bool, +rs: List<&2, Ar.KV>, +a: String) -> {Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(Ar.found(Ar.prop(a, ps))))) == ArgRepair.ar_bad_target(ps, cl, rs, Some{a}) : Bool}:
  %PSpec.rs.lookup(a, rs) : {Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(Ar.found(Ar.prop(a, ps))))) == Bool.or(Maybe.is_some(&2, String, _), Bool.and(cl, Bool.not(ArgSpec.is_some(ArgSpec.declared(a, ps))))) : Bool}
  %PSpec.rs.prop(a, ps) : {Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(Ar.found(Ar.prop(a, ps))))) == Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(ArgSpec.is_some(_)))) : Bool}
  %PSpec.rs.found(Ar.prop(a, ps)) : {Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(Ar.found(Ar.prop(a, ps))))) == Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(_))) : Bool}
  {==}

def ba.head_eq(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +k: String, +m: Maybe<&2, String>) -> {Bool.and(Bool.not(Ar.found(Ar.prop(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), als))) == Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), ps))), ArgRepair.ar_bad_target(ps, cl, rs, ArgSpec.first_text(ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k), als))) : Bool}:
  +cur = ArgRepair.ar_cur(Ar.decoded(ks, k, m), k)
  %PSpec.rs.decoded(ks, k, m) : {Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(cur, als))) == Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(ArgRepair.ar_cur(_, k), ps))), ArgRepair.ar_bad_target(ps, cl, rs, ArgSpec.first_text(ArgRepair.ar_cur(_, k), als))) : Bool}
  %PSpec.rs.prop(cur, ps) : {Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(cur, als))) == Bool.and(Bool.not(ArgSpec.is_some(_)), ArgRepair.ar_bad_target(ps, cl, rs, ArgSpec.first_text(cur, als))) : Bool}
  %PSpec.rs.found(Ar.prop(cur, ps)) : {Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(cur, als))) == Bool.and(Bool.not(_), ArgRepair.ar_bad_target(ps, cl, rs, ArgSpec.first_text(cur, als))) : Bool}
  %PSpec.rs.lookup(cur, als) : {Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(cur, als))) == Bool.and(Bool.not(Ar.found(Ar.prop(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, _)) : Bool}
  {==}

# Names
# -----

# a canonical name refused, or undeclared by a closed schema, is no name
def ba.target(h: Maybe<&2, String>, dec: Bool, cl: Bool, al: Maybe<&2, String>, -a: String, -ps: List<&2, Ar.Prop>, bad: {Bool.or(Maybe.is_some(&2, String, h), Bool.and(cl, Bool.not(dec))) == True{} : Bool}) -> {ba.is_no(Ar.named.target(h, dec, cl, al, a, ps)) == True{} : Bool}:
  match h:
    case Some{x}:
      {==}
    case None{}:
      match dec:
        case True{}:
          match cl:
            case True{}:
              AB.ab.absurd({ba.is_no(Ar.named.target(None{}, True{}, True{}, al, a, ps)) == True{} : Bool}, bad)
            case False{}:
              AB.ab.absurd({ba.is_no(Ar.named.target(None{}, True{}, False{}, al, a, ps)) == True{} : Bool}, bad)
        case False{}:
          match cl:
            case True{}:
              {==}
            case False{}:
              AB.ab.absurd({ba.is_no(Ar.named.target(None{}, False{}, False{}, al, a, ps)) == True{} : Bool}, bad)

def ba.alias(al: Maybe<&2, String>, dec: Bool, +cl: Bool, +ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, -k: String, bad: {Bool.and(Bool.not(dec), ArgRepair.ar_bad_target(ps, cl, rs, al)) == True{} : Bool}) -> {ba.is_no(Ar.named.alias(al, dec, cl, k, ps, als, rs)) == True{} : Bool}:
  match al:
    case Some{+a}:
      match dec:
        case True{}:
          AB.ab.absurd({ba.is_no(Ar.named.alias(Some{a}, True{}, cl, k, ps, als, rs)) == True{} : Bool}, bad)
        case False{}:
          ba.target(Ar.lookup(a, rs), Ar.found(Ar.prop(a, ps)), cl, Ar.lookup(a, als), a, ps, Equal.trans(Bool, Bool.or(Maybe.is_some(&2, String, Ar.lookup(a, rs)), Bool.and(cl, Bool.not(Ar.found(Ar.prop(a, ps))))), ArgRepair.ar_bad_target(ps, cl, rs, Some{a}), True{}, ba.bt_eq(ps, cl, rs, a), bad))
    case None{}:
      match dec:
        case True{}:
          AB.ab.absurd({ba.is_no(Ar.named.alias(None{}, True{}, cl, k, ps, als, rs)) == True{} : Bool}, bad)
        case False{}:
          AB.ab.absurd({ba.is_no(Ar.named.alias(None{}, False{}, cl, k, ps, als, rs)) == True{} : Bool}, bad)

def ba.hint(hr: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, bad: {Bool.and(Bool.not(Ar.found(Ar.prop(k, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(k, als))) == True{} : Bool}) -> {ba.is_no(Ar.named.hint(hr, Ar.Schema{ps, cl}, als, rs, k)) == True{} : Bool}:
  match hr:
    case Some{x}:
      {==}
    case None{}:
      ba.alias(Ar.lookup(k, als), Ar.found(Ar.prop(k, ps)), cl, ps, als, rs, k, bad)

# a key read that is an undeclared alias of a bad name is no name
def ba.named(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +k: String, bad: {Bool.and(Bool.not(Ar.found(Ar.prop(k, ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(k, als))) == True{} : Bool}) -> {ba.is_no(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k)) == True{} : Bool}:
  ba.hint(Ar.lookup(k, rs), ps, cl, als, rs, k, bad)

# Steps
# -----

# a step on no name refuses the call
def ba.no(n: Ar.Named, -ps: List<&2, Ar.Prop>, -ss: List<&2, Ar.Seen>, -r0: List<&2, Ar.Record>, -k: String, -v: Ar.Val, -rest: Ar.Verdict, e: {ba.is_no(n) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(Ar.step.named(n, ps, ss, r0, k, v), rest)) == True{} : Bool}:
  match n:
    case Ar.NRefused{j, x}:
      {==}
    case Ar.NUnknown{j, ns}:
      {==}
    case Ar.NAs{c}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.go.cons(Ar.step.named(Ar.NAs{c}, ps, ss, r0, k, v), rest)) == True{} : Bool}, e)

def ba.read(dm: Maybe<&2, String>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ss: List<&2, Ar.Seen>, +k: String, +v: Ar.Val, -rest: Ar.Verdict, bad: {Bool.and(Bool.not(Ar.found(Ar.prop(ArgRepair.ar_cur(dm, k), ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(ArgRepair.ar_cur(dm, k), als))) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(Ar.step.read(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ss, k, dm, v), rest)) == True{} : Bool}:
  match dm:
    case None{}:
      ba.no(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, k), ps, ss, Nil{}, k, v, rest, ba.named(ps, cl, als, rs, k, bad))
    case Some{+p}:
      ba.no(Ar.named(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, p), ps, ss, [Ar.RAlias{k, p}], p, v, rest, ba.named(ps, cl, als, rs, p, bad))

# a refused rest refuses the call
def ba.rest(st: Ar.Step, rest: Ar.Verdict, ih: {ArgRepair.ar_rejected(rest) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go.cons(st, rest)) == True{} : Bool}:
  match st:
    case Ar.StepNo{x}:
      {==}
    case Ar.StepOk{o, r, s}:
      match rest:
        case Ar.Rejected{x}:
          {==}
        case Ar.Repaired{os, xs}:
          AB.ab.absurd({ArgRepair.ar_rejected(Ar.go.cons(Ar.StepOk{o, r, s}, Ar.Repaired{os, xs})) == True{} : Bool}, ih)

def ba.or(b1: Bool, -b2: Bool, -G: Type, eb: {Bool.or(b1, b2) == True{} : Bool}, f1: {b1 == True{} : Bool} -> G, f2: {b2 == True{} : Bool} -> G) -> G:
  match b1:
    case True{}:
      f1({==})
    case False{}:
      f2(eb)

def ba.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>, bad: {ArgRepair.ar_some_bad_alias.go(ps, cl, als, rs, ks, args) == True{} : Bool}) -> {ArgRepair.ar_rejected(Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) == True{} : Bool}:
  match args:
    case Nil{}:
      AB.ab.absurd({ArgRepair.ar_rejected(Ar.Repaired{Nil{}, Nil{}}) == True{} : Bool}, bad)
    case +a <> +t:
      match a:
        case Ar.Arg{+k, +m, +v}:
          +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, Ar.Arg{k, m, v})
          +rest = Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss))
          +cur = ArgRepair.ar_cur(ArgSpec.decoding(ks, k, m), k)
          +b1 = Bool.and(Bool.not(ArgSpec.is_some(ArgSpec.declared(cur, ps))), ArgRepair.ar_bad_target(ps, cl, rs, ArgSpec.first_text(cur, als)))
          +b1r = Bool.and(Bool.not(Ar.found(Ar.prop(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), ps))), ArgRepair.ar_bad_target(ps, cl, rs, Ar.lookup(ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), als)))
          ba.or(b1, ArgRepair.ar_some_bad_alias.go(ps, cl, als, rs, ks, t), {ArgRepair.ar_rejected(Ar.go.cons(st, rest)) == True{} : Bool}, bad, h1 => ba.read(Ar.decoded(ks, k, m), ps, cl, als, rs, ss, k, v, rest, Equal.trans(Bool, b1r, b1, True{}, ba.head_eq(ps, cl, als, rs, ks, k, m), h1)), h2 => ba.rest(st, rest, ba.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss), h2)))

def ba.keys(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +args: List<&2, Ar.Arg>, bad: {ArgRepair.ar_some_bad_alias.go(ps, cl, als, rs, ArgSpec.sent_keys(args), args) == True{} : Bool}) -> {ArgRepair.ar_some_bad_alias.go(ps, cl, als, rs, Ar.keys(args), args) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Ar.keys(args), ArgSpec.sent_keys(args), PSpec.rs.keys(args)) : {ArgRepair.ar_some_bad_alias.go(ps, cl, als, rs, _, args) == True{} : Bool}
  bad

def ArgRepair.arg_repair_alias_rejects(sc, d, args, bad):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          ba.go(args, ps, cl, als, rs, Ar.keys(args), Nil{}, ba.keys(ps, cl, als, rs, args, bad))
