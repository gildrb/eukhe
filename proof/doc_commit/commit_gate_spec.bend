# eukhe: the proof of LAW commit_gate_spec
#
# PROOF: membership by the code's char-by-char comparison is the spec's
# (dcw.same); the rest computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcw.member(+d: String, s: List<&2, String>) -> {Cm.member(d, s) == DocCommit.sp_in(d, s) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +x <> rest:
      %LA.dcw.same(x, d) : {Cm.member(d, x <> rest) == Bool.or(_, DocCommit.sp_in(d, rest)) : Bool}
      %dcw.member(d, rest) : {Cm.member(d, x <> rest) == Bool.or(Cm.same(x, d), _) : Bool}
      {==}

def dcw.seen(b: Bool) -> {Cm.gate.seen(b) == DocCommit.sp_if(b, Cm.Proceed{}, Cm.Unseen{}) : Cm.Gate}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcw.bytes(b: Bool) -> {Cm.gate.bytes(b) == DocCommit.sp_if(b, Cm.Proceed{}, Cm.Stale{}) : Cm.Gate}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcw.gate(b: Cm.Base, d: Cm.Disk) -> {Cm.gate(b, d) == DocCommit.sp_gate(b, d) : Cm.Gate}:
  match b:
    case Cm.OnSeen{+s}:
      match d:
        case Cm.Absent{}:
          {==}
        case Cm.Present{+g, e}:
          %dcw.member(g, s) : {Cm.gate.seen(Cm.member(g, s)) == DocCommit.sp_if(_, Cm.Proceed{}, Cm.Unseen{}) : Cm.Gate}
          dcw.seen(Cm.member(g, s))
    case Cm.OnBytes{}:
      match d:
        case Cm.Absent{}:
          {==}
        case Cm.Present{g, e}:
          dcw.bytes(e)

def DocCommit.commit_gate_spec(b, d):
  dcw.gate(b, d)
