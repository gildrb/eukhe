# eukhe: the proof of LAW replace_replaces_new_daemon
#
# PROOF of LAW replace_replaces_new_daemon: split the start's relation
# into its tests (rrn.go): the same build id keeps the daemon b (0, and b's
# id is b's); an older daemon and an interactive start replace b by the
# client (1, and the ids differ: the relation saw them differ); every other
# start keeps b (0).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../cron_serve/base/logic.bend as LCronLogic

def rrn.go(same: Bool, older: Bool, newer: Bool, k: Rp.Caller, +ic: String, +ib: String, -rc: List<&2, Nat>, -rb: List<&2, Nat>, e: {String.eq(ic, ib) == same : Bool}) -> {Rp.replaces.put(Rp.verdict.put(Rp.rel.put(same, older, newer), k)) == Replace.rp_one_if(Bool.not(String.eq(Replace.rp_id_of(Rp.after.put(Rp.verdict.put(Rp.rel.put(same, older, newer), k), Rp.Build{rc, ic}, Rp.Build{rb, ib})), ib))) : Nat}:
  match same older newer k:
    case True{} _ _ _:
      %Equal.sym(Bool, String.eq(ib, ib), True{}, LCronLogic.lg.str_refl(ib)) : {0n == Replace.rp_one_if(Bool.not(_)) : Nat}
      {==}
    case False{} True{} _ Rp.Interactive{}:
      %Equal.sym(Bool, String.eq(ic, ib), False{}, e) : {1n == Replace.rp_one_if(Bool.not(_)) : Nat}
      {==}
    case False{} True{} _ Rp.Background{}:
      %Equal.sym(Bool, String.eq(ib, ib), True{}, LCronLogic.lg.str_refl(ib)) : {0n == Replace.rp_one_if(Bool.not(_)) : Nat}
      {==}
    case False{} False{} True{} _:
      %Equal.sym(Bool, String.eq(ib, ib), True{}, LCronLogic.lg.str_refl(ib)) : {0n == Replace.rp_one_if(Bool.not(_)) : Nat}
      {==}
    case False{} False{} False{} _:
      %Equal.sym(Bool, String.eq(ib, ib), True{}, LCronLogic.lg.str_refl(ib)) : {0n == Replace.rp_one_if(Bool.not(_)) : Nat}
      {==}

def rrn.start(+c: Rp.Build, k: Rp.Caller, +b: Rp.Build) -> {Rp.replaces(Rp.Start{c, k}, Some{b}) == Replace.rp_one_if(Bool.not(String.eq(Replace.rp_id_of(Rp.after(Rp.Start{c, k}, Some{b})), Replace.rp_id_of(b)))) : Nat}:
  match c b:
    case Rp.Build{+rc, +ic} Rp.Build{+rb, +ib}:
      rrn.go(String.eq(ic, ib), Rp.lt(rb, rc), Rp.lt(rc, rb), k, ic, ib, rc, rb, {==})

def Replace.replace_replaces_new_daemon(s, b):
  match s:
    case Rp.Start{+c, k}:
      rrn.start(c, k, b)
