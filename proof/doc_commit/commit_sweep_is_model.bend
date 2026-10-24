# eukhe: the proof of LAW commit_sweep_is_model
#
# PROOF: an entry is the target's own temporary file exactly when its name
# has the prefix (dcw.own), so the model's sweep removes an entry exactly
# when the code's sweep names it (dcw.model).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcw.own(a: Bool, b: Bool) -> {a == Cm.Sort.own(DocCommit.sp_sort.of(a, b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def dcw.step(b: Bool, +n: Nat, -k: Cm.Sort, -h: Bool, -r1: List<&2, Nat>, -r2: List<&2, Cm.Temp>, ih: {r1 == DocCommit.sp_ids(r2) : List<&2, Nat>}) -> {Cm.gone.put(n, r1, b) == DocCommit.sp_ids(Cm.sweep.put(Cm.Temp{n, k, h}, r2, b)) : List<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => n <> z, r1, DocCommit.sp_ids(r2), ih)
    case False{}:
      ih

def dcw.model(+p: String, es: List<&2, Cm.Ent>, +n: Nat) -> {Cm.gone.go(p, es, n) == DocCommit.sp_ids(Cm.sweep(DocCommit.sp_temps(p, es, n))) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Cm.Ent{+name, +h}:
          %dcw.own(DocCommit.sp_starts(p, name), DocCommit.sp_starts(".eukhe-tmp-", name)) : {Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Bool.and(Cm.starts(p, name), Bool.not(h))) == DocCommit.sp_ids(Cm.sweep.put(Cm.Temp{n, DocCommit.sp_sort(p, name), h}, Cm.sweep(DocCommit.sp_temps(p, rest, 1n+n)), Bool.and(_, Bool.not(h)))) : List<&2, Nat>}
          %Equal.sym(Bool, Cm.starts(p, name), DocCommit.sp_starts(p, name), LA.dcw.starts(p, name)) : {Cm.gone.put(n, Cm.gone.go(p, rest, 1n+n), Bool.and(_, Bool.not(h))) == DocCommit.sp_ids(Cm.sweep.put(Cm.Temp{n, DocCommit.sp_sort(p, name), h}, Cm.sweep(DocCommit.sp_temps(p, rest, 1n+n)), Bool.and(DocCommit.sp_starts(p, name), Bool.not(h)))) : List<&2, Nat>}
          dcw.step(Bool.and(DocCommit.sp_starts(p, name), Bool.not(h)), n, DocCommit.sp_sort(p, name), h, Cm.gone.go(p, rest, 1n+n), Cm.sweep(DocCommit.sp_temps(p, rest, 1n+n)), dcw.model(p, rest, 1n+n))

def DocCommit.commit_sweep_is_model(h, es):
  dcw.model(Cm.prefix(h), es, 0n)
