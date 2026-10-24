# eukhe: the proof of LAW commit_sweep_spec
#
# PROOF: entry by entry, the code's prefix test is the spec's
# (dcw.starts); the code's prefix computes to the spec's.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcw.gone_keep(b: Bool, +n: Nat, r: List<&2, Nat>) -> {Cm.gone.put(n, r, b) == DocCommit.sp_gone.keep(b, n, r) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcw.gone(+p: String, es: List<&2, Cm.Ent>, +n: Nat) -> {Cm.gone.go(p, es, n) == DocCommit.sp_gone(p, es, n) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Ent{+name, h}:
          %dcw.gone(p, rest, 1n+n) : {Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Bool.and(Cm.starts(p, name), Bool.not(h))) == DocCommit.sp_gone.keep(Bool.and(DocCommit.sp_starts(p, name), Bool.not(h)), n, _) : List<&2, Nat>}
          %LA.dcw.starts(p, name) : {Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Bool.and(Cm.starts(p, name), Bool.not(h))) == DocCommit.sp_gone.keep(Bool.and(_, Bool.not(h)), n, Cm.gone.go(p, rest, 1n+n)) : List<&2, Nat>}
          dcw.gone_keep(Bool.and(Cm.starts(p, name), Bool.not(h)), n, Cm.gone.go(p, rest, 1n+n))

def DocCommit.commit_sweep_spec(h, es):
  dcw.gone(Cm.prefix(h), es, 0n)
