# eukhe: the proof of LAW arg_repair_recorded
#
# PROOF: by induction over the arguments, the sent keys and the names
# taken generalized (rc.go): a repaired step's records are its decoding,
# its renaming and its reading (sv.step), which are the laws' changes of
# its out (rc.ok, with base/look.bend's decoding, renaming and reading);
# the rest's records are the rest's changes (the hypothesis).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB
import ./base/step.bend as SV
import ./base/look.bend as PSpec

# a verdict with its records replaced by the changes of its outs, the
# sent keys ks given
def rc.RC(+ks: List<&2, String>, +args: List<&2, Ar.Arg>, v: Ar.Verdict) -> Ar.Verdict:
  match v:
    case Ar.Repaired{+os, rs}:
      Ar.Repaired{os, ArgRepair.ar_changes(ks, args, os)}
    case Ar.Rejected{x}:
      Ar.Rejected{x}

def rc.conv(+args: List<&2, Ar.Arg>, v: Ar.Verdict) -> {rc.RC(ArgSpec.sent_keys(args), args, v) == ArgRepair.ar_rec(args, v) : Ar.Verdict}:
  match v:
    case Ar.Repaired{os, xs}:
      {==}
    case Ar.Rejected{x}:
      {==}

def rc.recs(v: Ar.Verdict) -> List<&2, Ar.Record>:
  match v:
    case Ar.Repaired{os, rs}:
      rs
    case Ar.Rejected{x}:
      Nil{}

def rc.ok(+ks: List<&2, String>, +k: String, +m: Maybe<&2, String>, +v: Ar.Val, +c: String, +to: Maybe<&2, Ar.To>, +r: List<&2, Ar.Record>, +s: Ar.Seen, +t: List<&2, Ar.Arg>, rest: Ar.Verdict, hr: {r == List.append(&2, Ar.Record, ArgRepair.ar_dec_rec(Ar.decoded(ks, k, m), k), List.append(&2, Ar.Record, Ar.rename(String.eq(c, ArgRepair.ar_cur(Ar.decoded(ks, k, m), k)), ArgRepair.ar_cur(Ar.decoded(ks, k, m), k), c), Ar.coerced(c, v, to))) : List<&2, Ar.Record>}, ih: {rest == rc.RC(ks, t, rest) : Ar.Verdict}) -> {Ar.go.cons(Ar.StepOk{Ar.Out{c, to}, r, s}, rest) == rc.RC(ks, Ar.Arg{k, m, v} <> t, Ar.go.cons(Ar.StepOk{Ar.Out{c, to}, r, s}, rest)) : Ar.Verdict}:
  match rest:
    case Ar.Rejected{x}:
      {==}
    case Ar.Repaired{+os, +xs}:
      +dm = Ar.decoded(ks, k, m)
      +cur = ArgRepair.ar_cur(dm, k)
      +L = {Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, r, xs)} : Ar.Verdict}
      %Equal.cong(Ar.Verdict, List<&2, Ar.Record>, w => rc.recs(w), Ar.Repaired{os, xs}, Ar.Repaired{os, ArgRepair.ar_changes(ks, t, os)}, ih) : {L == Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, ArgRepair.ar_changes.one(ArgSpec.decoding(ks, k, m), k, v, Ar.Out{c, to}), _)} : Ar.Verdict}
      %PSpec.rs.decoded(ks, k, m) : {L == Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, ArgRepair.ar_changes.one(_, k, v, Ar.Out{c, to}), xs)} : Ar.Verdict}
      %PSpec.rs.rename(String.eq(c, cur), cur, c) : {L == Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, List.append(&2, Ar.Record, ArgRepair.ar_dec_rec(dm, k), List.append(&2, Ar.Record, _, ArgSpec.read_rec(c, v, to))), xs)} : Ar.Verdict}
      %PSpec.rs.coerced(c, v, to) : {L == Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, List.append(&2, Ar.Record, ArgRepair.ar_dec_rec(dm, k), List.append(&2, Ar.Record, Ar.rename(String.eq(c, cur), cur, c), _)), xs)} : Ar.Verdict}
      %hr : {L == Ar.Repaired{Ar.Out{c, to} <> os, List.append(&2, Ar.Record, _, xs)} : Ar.Verdict}
      {==}

def rc.cons(+ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg, +t: List<&2, Ar.Arg>, st: Ar.Step, h: SV.sv.SVa(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a, st), rest: Ar.Verdict, ih: {rest == rc.RC(ks, t, rest) : Ar.Verdict}) -> {Ar.go.cons(st, rest) == rc.RC(ks, a <> t, Ar.go.cons(st, rest)) : Ar.Verdict}:
  match a:
    case Ar.Arg{+k, +m, +v}:
      match st:
        case Ar.StepNo{x}:
          {==}
        case Ar.StepOk{o, +r, +s}:
          match o:
            case Ar.Out{+c, +to}:
              (hn, (hf, (hto, (hs, (hr, hx))))) = h
              rc.ok(ks, k, m, v, c, to, r, s, t, rest, hr, ih)

def rc.go(args: List<&2, Ar.Arg>, +ps: List<&2, Ar.Prop>, +cl: Bool, +als: List<&2, Ar.KV>, +rs: List<&2, Ar.KV>, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>) -> {Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss) == rc.RC(ks, args, Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss)) : Ar.Verdict}:
  match args:
    case Nil{}:
      {==}
    case +a <> +t:
      +st = Ar.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a)
      rc.cons(ps, cl, als, rs, ks, ss, a, t, st, SV.sv.step(Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, ss, a), Ar.go(t, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, ks, Ar.seen.next(st, ss)), rc.go(t, ps, cl, als, rs, ks, Ar.seen.next(st, ss)))

def ArgRepair.arg_repair_recorded(sc, d, args):
  match sc:
    case Ar.Schema{+ps, +cl}:
      match d:
        case Ar.Dialect{+als, +rs}:
          +v = Ar.go(args, Ar.Schema{ps, cl}, Ar.Dialect{als, rs}, Ar.keys(args), Nil{})
          %rc.conv(args, v) : {v == _ : Ar.Verdict}
          %PSpec.rs.keys(args) : {v == rc.RC(_, args, v) : Ar.Verdict}
          rc.go(args, ps, cl, als, rs, Ar.keys(args), Nil{})
