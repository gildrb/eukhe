# eukhe: the proof of LAW ledger_only_records
#
# By induction on the operations: an operation's epoch leaves the log
# before it, then a prefix of its records (log_plan_only_commits); the
# operations after it start from that disk.

import Base
import ../../spec/durable/log.bend as Lg
import ../../laws/log.bend as Log
import ./base.bend as LA
import ./log_plan_only_commits.bend as PPlanOnly

# the log f after the operations, from the log m == l ++ t the first of
# them left and f == m ++ k: the log l before, then t ++ k
def pl.lo_join(+l: List<&2, List<&2, Nat>>, +t: List<&2, List<&2, Nat>>, +k: List<&2, List<&2, Nat>>, -m: List<&2, List<&2, Nat>>, -f: List<&2, List<&2, Nat>>, h1: {m == List.append(&2, List<&2, Nat>, l, t) : List<&2, List<&2, Nat>>}, h2: {f == List.append(&2, List<&2, Nat>, m, k) : List<&2, List<&2, Nat>>}) -> {f == List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, t, k)) : List<&2, List<&2, Nat>>}:
  +rhs = List.append(&2, List<&2, Nat>, l, List.append(&2, List<&2, Nat>, t, k))
  %Equal.sym(List<&2, List<&2, Nat>>, f, List.append(&2, List<&2, Nat>, m, k), h2) : {_ == rhs : List<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, List<&2, Nat>>, m, List.append(&2, List<&2, Nat>, l, t), h1) : {List.append(&2, List<&2, Nat>, _, k) == rhs : List<&2, List<&2, Nat>>}
  %LA.pl.assoc(List<&2, Nat>, l, t, k) : {_ == rhs : List<&2, List<&2, Nat>>}
  {==}

# one operation, then the rest
def pl.lo_cons(+e: Lg.Epoch, +rest: List<&2, Lg.Epoch>, +d: Lg.Disk, r1: &n: Nat -> {Lg.Disk.log(Log.log_after(d, e)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n)) : List<&2, List<&2, Nat>>}, r2: &ns: List<&2, Nat> -> {Lg.Disk.log(Log.log_ledger_after(rest, Log.log_after(d, e))) == List.append(&2, List<&2, Nat>, Lg.Disk.log(Log.log_after(d, e)), Log.log_ledger_taken(rest, ns)) : List<&2, List<&2, Nat>>}) -> &ns: List<&2, Nat> -> {Lg.Disk.log(Log.log_ledger_after(e <> rest, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_taken(e <> rest, ns)) : List<&2, List<&2, Nat>>}:
  match r1:
    case (+n, h1):
      match r2:
        case (+ns, h2):
          +d1 = Log.log_after(d, e)
          (n <> ns, pl.lo_join(Lg.Disk.log(d), List.take(&2, List<&2, Nat>, Lg.Epoch.cs(e), n), Log.log_ledger_taken(rest, ns), Lg.Disk.log(d1), Lg.Disk.log(Log.log_ledger_after(rest, d1)), h1, h2))

def pl.ledger_only(es: List<&2, Lg.Epoch>, +d: Lg.Disk) -> &ns: List<&2, Nat> -> {Lg.Disk.log(Log.log_ledger_after(es, d)) == List.append(&2, List<&2, Nat>, Lg.Disk.log(d), Log.log_ledger_taken(es, ns)) : List<&2, List<&2, Nat>>}:
  match es:
    case Nil{}:
      (Nil{}, LA.pl.app_nil(List<&2, Nat>, Lg.Disk.log(d)))
    case +e <> +rest:
      pl.lo_cons(e, rest, d, Log.log_plan_only_commits(d, e), pl.ledger_only(rest, Log.log_after(d, e)))

def Log.ledger_only_records(d, es):
  pl.ledger_only(es, d)
