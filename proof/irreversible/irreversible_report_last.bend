# eukhe: the proof of LAW irreversible_report_last
#
# PROOF: by induction on the ledger, counting ids from at: the entry
# appended last has id |es| + 1 + at (LA.irb.add_succ), and picking an
# entry in front commutes with appending after (irr.add_app).

import Base
import ../../bend/irreversible.bend as Ir
import ../../laws/irreversible.bend as Irreversible
import ./base.bend as LA

def irr.add_nil(b: Bool, n: Nat) -> {Ir.report.add(b, n, Nil{}) == Irreversible.ir_in_run(b, n) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def irr.add_app(b: Bool, +n: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {Ir.report.add(b, n, List.append(&2, Nat, xs, ys)) == List.append(&2, Nat, Ir.report.add(b, n, xs), ys) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def irr.go(es: List<&2, Ir.Entry>, +k: Nat, +q: Nat, +r: Nat, +at: Nat) -> {Ir.report.go(List.append(&2, Ir.Entry, es, [Ir.Entry{k, q}]), r, at) == List.append(&2, Nat, Ir.report.go(es, r, at), Irreversible.ir_in_run(Nat.is_eq(q, r), Nat.add(List.length(&2, Ir.Entry, es), 1n+at))) : List<&2, Nat>}:
  match es:
    case Nil{}:
      irr.add_nil(Nat.is_eq(q, r), 1n+at)
    case e <> +t:
      match e:
        case Ir.Entry{j, p}:
          +h = Nat.is_eq(q, r)
          +b = Nat.is_eq(p, r)
          +g = Ir.report.go(t, r, 1n+at)
          +n = List.length(&2, Ir.Entry, t)
          +rhs = List.append(&2, Nat, Ir.report.add(b, 1n+at, g), Irreversible.ir_in_run(h, 1n+Nat.add(n, 1n+at)))
          %Equal.sym(List<&2, Nat>, Ir.report.go(List.append(&2, Ir.Entry, t, [Ir.Entry{k, q}]), r, 1n+at), List.append(&2, Nat, g, Irreversible.ir_in_run(h, Nat.add(n, 1n+(1n+at)))), irr.go(t, k, q, r, 1n+at)) : {Ir.report.add(b, 1n+at, _) == rhs : List<&2, Nat>}
          %Equal.sym(Nat, Nat.add(n, 1n+(1n+at)), 1n+Nat.add(n, 1n+at), LA.irb.add_succ(n, 1n+at)) : {Ir.report.add(b, 1n+at, List.append(&2, Nat, g, Irreversible.ir_in_run(h, _))) == rhs : List<&2, Nat>}
          irr.add_app(b, 1n+at, g, Irreversible.ir_in_run(h, 1n+Nat.add(n, 1n+at)))

def Irreversible.irreversible_report_last(es, k, q, r):
  %LA.irb.add_one(List.length(&2, Ir.Entry, es)) : {Ir.report(List.append(&2, Ir.Entry, es, [Ir.Entry{k, q}]), r) == List.append(&2, Nat, Ir.report(es, r), Irreversible.ir_in_run(Nat.is_eq(q, r), _)) : List<&2, Nat>}
  irr.go(es, k, q, r, 0n)
