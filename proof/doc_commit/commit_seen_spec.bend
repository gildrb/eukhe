# eukhe: the proof of LAW commit_seen_spec
#
# PROOF: the code drops the seen digest by its char-by-char comparison,
# the spec's (dcw.same, dcw.unsee); List.take is the spec's sp_take8.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ./base.bend as LA

def dcw.keep(b: Bool, +x: String, r: List<&2, String>) -> {Cm.unsee.put(x, r, b) == DocCommit.sp_without.keep(b, x, r) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcw.unsee(+d: String, s: List<&2, String>) -> {Cm.unsee(d, s) == DocCommit.sp_without(d, s) : List<&2, String>}:
  match s:
    case Nil{}:
      {==}
    case +x <> +rest:
      %dcw.unsee(d, rest) : {Cm.unsee(d, x <> rest) == DocCommit.sp_without.keep(LawsBase.text_same(x, d), x, _) : List<&2, String>}
      %LA.dcw.same(x, d) : {Cm.unsee(d, x <> rest) == DocCommit.sp_without.keep(_, x, Cm.unsee(d, rest)) : List<&2, String>}
      dcw.keep(Cm.same(x, d), x, Cm.unsee(d, rest))

def dcw.take(xs: List<&2, String>, n: Nat) -> {List.take(&2, String, xs, n) == DocCommit.sp_take8(n, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          {==}
    case h <> t:
      match n:
        case 0n:
          {==}
        case 1n+p:
          %dcw.take(t, p) : {h <> List.take(&2, String, t, p) == h <> _ : List<&2, String>}
          {==}

def DocCommit.commit_seen_spec(d, s):
  %dcw.unsee(d, s) : {List.take(&2, String, d <> Cm.unsee(d, s), 8n) == DocCommit.sp_take8(8n, d <> _) : List<&2, String>}
  dcw.take(d <> Cm.unsee(d, s), 8n)
