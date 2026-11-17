# eukhe: the proof of LAW irreversible_history_ids
#
# PROOF: by induction on the records. A new key answers New with the
# next id and the ledger grows by one (LA.irb.rec_new, LA.irb.keep_new,
# LA.irb.len_last): ids 1 to n then n + 1 are the ids 1 to n + 1
# (LA.irb.app_assoc). A known key answers Known, which adds no id, and
# leaves the ledger (LA.irb.rec_known, LA.irb.keep_known).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def ihi.known(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, +rest: List<&2, Ir.Entry>, s: Sigma<&1, &1, Nat, n => {Ir.record(es, k) == Ir.Known{n} : Ir.Recorded}>, kk: {Ir.keep(es, k, r) == es : List<&2, Ir.Entry>}, ih: {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.keep(es, k, r))), Irreversible.ir_news(Irreversible.ir_answers(rest, Ir.keep(es, k, r)))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, Ir.keep(es, k, r)))) : List<&2, Nat>}) -> {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), Irreversible.ir_news(Ir.record(es, k) <> Irreversible.ir_answers(rest, Ir.keep(es, k, r)))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, Ir.keep(es, k, r)))) : List<&2, Nat>}:
  match s:
    case (n, e):
      +kp = Ir.keep(es, k, r)
      +ns = Irreversible.ir_news(Irreversible.ir_answers(rest, kp))
      %Equal.sym(Ir.Recorded, Ir.record(es, k), Ir.Known{n}, e) : {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), Irreversible.ir_news(_ <> Irreversible.ir_answers(rest, kp))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, kp))) : List<&2, Nat>}
      +e2 = Equal.cong(List<&2, Ir.Entry>, List<&2, Nat>, z => List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, z)), ns), kp, es, kk)
      Equal.trans(List<&2, Nat>, List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), ns), List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, kp)), ns), Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, kp))), Equal.sym(List<&2, Nat>, List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, kp)), ns), List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), ns), e2), ih)

def ihi.step(+es: List<&2, Ir.Entry>, +k: Nat, +r: Nat, +rest: List<&2, Ir.Entry>, b: Bool, +eb: {Irreversible.ir_has(es, k) == b : Bool}, ih: {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.keep(es, k, r))), Irreversible.ir_news(Irreversible.ir_answers(rest, Ir.keep(es, k, r)))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, Ir.keep(es, k, r)))) : List<&2, Nat>}) -> {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), Irreversible.ir_news(Ir.record(es, k) <> Irreversible.ir_answers(rest, Ir.keep(es, k, r)))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, Ir.keep(es, k, r)))) : List<&2, Nat>}:
  match b:
    case True{}:
      ihi.known(es, k, r, rest, LA.irb.rec_known(es, k, eb), LA.irb.keep_known(es, k, r, eb), ih)
    case False{}:
      +kp = Ir.keep(es, k, r)
      +ns = Irreversible.ir_news(Irreversible.ir_answers(rest, kp))
      +n = {1n+List.length(&2, Ir.Entry, es) : Nat}
      +u = Irreversible.ir_upto(List.length(&2, Ir.Entry, es))
      %Equal.sym(Ir.Recorded, Ir.record(es, k), Ir.New{n}, LA.irb.rec_new(es, k, eb)) : {List.append(&2, Nat, u, Irreversible.ir_news(_ <> Irreversible.ir_answers(rest, kp))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, kp))) : List<&2, Nat>}
      +lk = Equal.trans(Nat, List.length(&2, Ir.Entry, kp), List.length(&2, Ir.Entry, List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}])), n, Equal.cong(List<&2, Ir.Entry>, Nat, z => List.length(&2, Ir.Entry, z), kp, List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]), LA.irb.keep_new(es, k, r, eb)), LA.irb.len_last(es, Ir.Entry{k, r}))
      +e1 = LA.irb.app_assoc(Nat, u, [n], ns)
      +e2 = Equal.cong(Nat, List<&2, Nat>, z => List.append(&2, Nat, Irreversible.ir_upto(z), ns), List.length(&2, Ir.Entry, kp), n, lk)
      +a = List.append(&2, Nat, u, n <> ns)
      +m = List.append(&2, Nat, List.append(&2, Nat, u, [n]), ns)
      +c = List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, kp)), ns)
      Equal.trans(List<&2, Nat>, a, m, Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, kp))), Equal.sym(List<&2, Nat>, m, a, e1), Equal.trans(List<&2, Nat>, m, c, Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(rest, kp))), Equal.sym(List<&2, Nat>, c, m, e2), ih))

def ihi.go(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>) -> {List.append(&2, Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)), Irreversible.ir_news(Irreversible.ir_answers(ops, es))) == Irreversible.ir_upto(List.length(&2, Ir.Entry, Ir.history(ops, es))) : List<&2, Nat>}:
  match ops:
    case Nil{}:
      LA.irb.app_nil(Nat, Irreversible.ir_upto(List.length(&2, Ir.Entry, es)))
    case op <> +rest:
      match op:
        case Ir.Entry{+k, +r}:
          ihi.step(es, k, r, rest, Irreversible.ir_has(es, k), {==}, ihi.go(rest, Ir.keep(es, k, r)))

def Irreversible.irreversible_history_ids(ops, es):
  ihi.go(ops, es)
