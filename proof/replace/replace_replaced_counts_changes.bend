# eukhe: the proof of LAW replace_replaced_counts_changes: the first start
# finds no daemon and counts none; from a running daemon b on (rrc.go),
# by induction on the starts, each start counts 1 exactly when the daemon
# after it has another build id than b (replace_replaces_new_daemon),
# which is the change of id from b to the next daemon of the trace

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./replace_replaces_new_daemon.bend as PReplaceReplacesNewDaemon

def rrc.go(ss: List<&2, Rp.Start>, +b: Rp.Build) -> {Rp.replaced.go(ss, Some{b}) == Replace.rp_id_changes.from(Rp.trace.go(ss, Some{b}), b) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      %rrc.go(rest, Rp.after(s, Some{b})) : {Rp.replaced.go(s <> rest, Some{b}) == Nat.add(Replace.rp_one_if(Replace.rp_other_than(Some{b}, Rp.after(s, Some{b}))), _) : Nat}
      %Equal.sym(Nat, Rp.replaces(s, Some{b}), Replace.rp_one_if(Replace.rp_other_than(Some{b}, Rp.after(s, Some{b}))), Replace.replace_replaces_new_daemon(s, Some{b})) : {Nat.add(_, Rp.replaced.go(rest, Some{Rp.after(s, Some{b})})) == Nat.add(Replace.rp_one_if(Replace.rp_other_than(Some{b}, Rp.after(s, Some{b}))), Rp.replaced.go(rest, Some{Rp.after(s, Some{b})})) : Nat}
      {==}

def rrc.top(ss: List<&2, Rp.Start>) -> {Rp.replaced(ss) == Replace.rp_id_changes(Rp.daemons(ss)) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Rp.Start{+c, k}:
          rrc.go(rest, c)

def Replace.replace_replaced_counts_changes(ss):
  rrc.top(ss)
