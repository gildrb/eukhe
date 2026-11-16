# eukhe: the proof of LAW ledger_ack_durable
#
# By induction on the operations: an operation's epoch leaves the log
# before it, then what it acknowledged, then maybe more
# (log_plan_ack_durable); the operations after it start from that disk.

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./base.bend as LA
import ./log_plan_ack_durable.bend as PPlanAck

# the log f after the operations, from the log m == (l ++ a) ++ x the first
# of them left and f == m ++ k: the log l before, then (a ++ x) ++ k
def pl.lk_join(+l: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, +x: List<&2, List<&2, Nat>>, +k: List<&2, List<&2, Nat>>, -m: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, h1: {m == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, l, a), x) : List<&2, List<&2, Nat>>}, h2: {f == List.append(&2, List<&2, Nat>, m, k) : List<&2, List<&2, Nat>>}) -> {f == List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, a, x), k)) : List<&2, List<&2, Nat>>}:
  +la = List.append(&2, List<&2, Nat>, l, a)
  +rhs = List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, a, x), k))
  %Equal.sym(List<&2, List<&2, Nat>>, f, List.append(&2, List<&2, Nat>, m, k), h2) : {_ == rhs : List<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, Nat>>, m, List.append(&2, List<&2, Nat>, la, x), h1) : {List.append(&2, List<&2, Nat>, _, k) == rhs : List<&2, List<&2, Nat>>}
  %LA.pl.assoc(List<&2, Nat>, la, x, k) : {_ == rhs : List<&2, List<&2, Nat>>}
  %LA.pl.assoc(List<&2, Nat>, l, a, List.append(&2, List<&2, Nat>, x, k)) : {_ == rhs : List<&2, List<&2, Nat>>}
  %LA.pl.assoc(List<&2, Nat>, a, x, k) : {List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, a, List.append(&2, List<&2, Nat>, x, k))) == List.append(&2, List<&2, Nat>, l, _) : List<&2, List<&2, Nat>>}
  {==}

# one operation, then the rest
def pl.lk_cons(+e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, +d: Lg.Disk, r1: &x: List<&2, List<&2, Nat>> -> {Lg.Disk.log(Log.log_after(d, e)) == List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_acked(d, e)), x) : List<&2, List<&2, Nat>>}, r2: &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Log.log_ledger_after(rest, Log.log_after(d, e))) == List.append(&2, List<&2, Nat>, Lg.Disk.log(Log.log_after(d, e)), Log.log_ledger_kept(rest, Log.log_after(d, e), xs)) : List<&2, List<&2, Nat>>}) -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Log.log_ledger_after(e <> rest, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_kept(e <> rest, d, xs)) : List<&2, List<&2, Nat>>}:
  match r1:
    case (+x, h1):
      match r2:
        case (+xs, h2):
          +d1 = Log.log_after(d, e)
          (x <> xs, pl.lk_join(Lg.Disk.log(d), Log.log_acked(d, e), x, Log.log_ledger_kept(rest, d1, xs), Lg.Disk.log(d1), Lg.Disk.log(Log.log_ledger_after(rest, d1)), h1, h2))

def pl.ledger_ack(es: List<&2, Lg.Epoch>, +d: Lg.Disk) -> &xs: List<&2, List<&2, List<&2, Nat>>> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_kept(es, d, xs)) : List<&2, List<&2, Nat>>}:
  match es:
    case Nil{}:
      (Nil{}, LA.pl.app_nil(List<&2, Nat>, Lg.Disk.log(d)))
    case +e <> +rest:
      pl.lk_cons(e, rest, d, Log.log_plan_ack_durable(d, e), pl.ledger_ack(rest, Log.log_after(d, e)))

def Log.ledger_ack_durable(d, es):
  pl.ledger_ack(es, d)
