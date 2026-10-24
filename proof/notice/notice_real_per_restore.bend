# eukhe: the proof of LAW notice_real_per_restore

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./notice_per_restore.bend as PNoticePerRestore
import ./notice_real_refines.bend as PNoticeRealRefines

def nps.sum(ns: List<&2, No.N>) -> {Notice.nt_sum(Notice.nt_shown(ns)) == No.total(ns) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{s, +c}:
          %nps.sum(t) : {Nat.add(c, Notice.nt_sum(Notice.nt_shown(t))) == Nat.add(c, _) : Nat}
          {==}

def nps.res(evs: List<&2, No.Ev>) -> {No.restores(evs) == Notice.nt_restores(evs) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case No.Restore{}:
          %nps.res(rest) : {1n+No.restores(rest) == 1n+_ : Nat}
          {==}
        case No.Live{}:
          nps.res(rest)
        case No.Reconnect{}:
          nps.res(rest)

# the rule's counts are the model's (notice_real_refines), whose total
# after one more attach is the restores (notice_per_restore)
def nps.go(+evs: List<&2, No.Ev>) -> {Notice.nt_sum(Notice.nt_counts(Notice.nt_scene(List.append(&2, No.Ev, evs, [No.Reconnect{}])))) == Notice.nt_restores(evs) : Nat}:
  +x = List.append(&2, No.Ev, evs, [No.Reconnect{}])
  %Equal.sym(List<&2, Nat>, Notice.nt_counts(Notice.nt_scene(x)), Notice.nt_shown(No.run(x)), Notice.notice_real_refines(x)) : {Notice.nt_sum(_) == Notice.nt_restores(evs) : Nat}
  %Equal.sym(Nat, Notice.nt_sum(Notice.nt_shown(No.run(x))), No.total(No.run(x)), nps.sum(No.run(x))) : {_ == Notice.nt_restores(evs) : Nat}
  Equal.trans(Nat, No.total(No.run(x)), No.restores(evs), Notice.nt_restores(evs), Notice.notice_per_restore(evs), nps.res(evs))

def Notice.notice_real_per_restore(evs):
  nps.go(evs)
