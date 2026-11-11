# eukhe: the proof of LAW write_is_gate
#
# PROOF: the model writes over a version exactly when the version is among the seen ones (dcf.wrote_go), which on digests is the shipped membership (dcl.member_dg), on which the shipped gate proceeds (dcf.gate_seen); over no file both go on.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.wrote_go(b: Bool, -d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat) -> {DocCommit.wrote(Cm.write.go(Bool.not(b), d, s, c)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def dcf.gate_seen(m: Bool) -> {m == DocCommit.proceeds(Cm.gate.seen(m)) : Bool}:
  match m:
    case True{}:
      {==}
    case False{}:
      {==}

def dcf.wr_gate(+v: Nat, +s: List<&2, Nat>, +c: Nat, -e: Bool) -> {DocCommit.wrote(Cm.write(Some{v}, s, c)) == DocCommit.proceeds(Cm.gate(Cm.OnSeen{DocCommit.dgs(s)}, Cm.Present{DocCommit.dg(v), e})) : Bool}:
  Equal.trans(Bool, DocCommit.wrote(Cm.write.go(Bool.not(Cm.mem(v, s)), Some{v}, s, c)), Cm.mem(v, s), DocCommit.proceeds(Cm.gate.seen(Cm.member(DocCommit.dg(v), DocCommit.dgs(s)))), dcf.wrote_go(Cm.mem(v, s), Some{v}, s, c), Equal.trans(Bool, Cm.mem(v, s), Cm.member(DocCommit.dg(v), DocCommit.dgs(s)), DocCommit.proceeds(Cm.gate.seen(Cm.member(DocCommit.dg(v), DocCommit.dgs(s)))), Equal.sym(Bool, Cm.member(DocCommit.dg(v), DocCommit.dgs(s)), Cm.mem(v, s), LA.dcl.member_dg(v, s)), dcf.gate_seen(Cm.member(DocCommit.dg(v), DocCommit.dgs(s)))))

def DocCommit.write_is_gate(v, s, c, e):
  (dcf.wr_gate(v, s, c, e), {==})
