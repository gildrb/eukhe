# eukhe: the proof of LAW temp_sweep_is_shipped
#
# PROOF: by induction on the entries, the index running with them. At an
# entry the code's prefix test is Base's String.starts_with
# (LC.dcq.starts_sw), which is whether the model's sort of the entry is
# the target's own (tss.own); so the shipped sweep keeps the entry's index
# exactly when the model's sweep keeps its file (tss.step).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base/choices.bend as LC

# the model's sort is the target's own exactly when the name starts with
# the target's prefix
def tss.pick(a: Bool, b: Bool) -> {Cm.Sort.own(DocCommit.sp_sort.pick(a, b)) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def tss.own(+h: String, +n: String) -> {Cm.Sort.own(DocCommit.sp_sort(h, n)) == String.starts_with(n, DocCommit.tmp_prefix(h)) : Bool}:
  tss.pick(String.starts_with(n, DocCommit.tmp_prefix(h)), String.starts_with(n, ".eukhe-tmp-"))

# one entry: kept by both or removed by both, at index i
def tss.step(+i: Nat, -x: List<&2, Nat>, -y: List<&2, Cm.Temp>, +k: Cm.Sort, +held: Bool, b: Bool, ih: {x == DocCommit.sp_ids(y) : List<&2, Nat>}) -> {Cm.gone.put(i, x, b) == DocCommit.sp_ids(Cm.sweep.put(Cm.Temp{i, k, held}, y, b)) : List<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => i <> z, x, DocCommit.sp_ids(y), ih)
    case False{}:
      ih

def tss.go(+h: String, es: List<&2, Cm.Ent>, +i: Nat) -> {Cm.gone.go(Cm.prefix(h), es, i) == DocCommit.sp_ids(Cm.sweep(DocCommit.sp_temps(h, es, i))) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Cm.Ent{+n, +held}:
          +k = DocCommit.sp_sort(h, n)
          +same = Equal.trans(Bool, Cm.starts(Cm.prefix(h), n), String.starts_with(n, Cm.prefix(h)), Cm.Sort.own(k), LC.dcq.starts_sw(Cm.prefix(h), n), Equal.sym(Bool, Cm.Sort.own(k), String.starts_with(n, DocCommit.tmp_prefix(h)), tss.own(h, n)))
          %Equal.sym(Bool, Cm.starts(Cm.prefix(h), n), Cm.Sort.own(k), same) : {Cm.gone.put(i, Cm.gone.go(Cm.prefix(h), rest, 1n+i), Bool.and(_, Bool.not(held))) == DocCommit.sp_ids(Cm.sweep.put(Cm.Temp{i, k, held}, Cm.sweep(DocCommit.sp_temps(h, rest, 1n+i)), Bool.and(Cm.Sort.own(k), Bool.not(held)))) : List<&2, Nat>}
          tss.step(i, Cm.gone.go(Cm.prefix(h), rest, 1n+i), Cm.sweep(DocCommit.sp_temps(h, rest, 1n+i)), k, held, Bool.and(Cm.Sort.own(k), Bool.not(held)), tss.go(h, rest, 1n+i))

def DocCommit.temp_sweep_is_shipped(h, es):
  tss.go(h, es, 0n)
