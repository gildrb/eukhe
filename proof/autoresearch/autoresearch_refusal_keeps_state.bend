# eukhe: the proof of LAW autoresearch_refusal_keeps_state: per path of
# the entry (malformed, left over, snapshot, refused event, accepted
# event), the state after it; only an accepted event moves it, and its
# reply starts with tag 0, never the refusal's tag 1

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_autoresearch.bend as FAr
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/entry.bend as AutoresearchEntry
import ./base/step.bend as AS

# the text starts with the digit 0
def rks.head0(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      ArL.same_char(c, Wr.dchar(0n))

# tag 0 is not tag 1
def rks.tag(-x: String, -y: String, e: {Wr.put_nat(0n, x) == Wr.put_nat(1n, y) : String}) -> {True{} == False{} : Bool}:
  Equal.cong(String, Bool, s => rks.head0(s), Wr.put_nat(0n, x), Wr.put_nat(1n, y), e)

# a refusal reply leaves the state at Live{s}
def rks.G(+s: ArS.St, +t: String, r: FAr.St & String) -> Type:
  {AutoresearchEntry.ar_reply_of(r) == Wr.put_nat(1n, Wr.put_str(t, "")) : String} -> {AutoresearchEntry.ar_state(r) == FAr.Live{s} : FAr.St}

def rks.answer(r: ArS.Res, +s: ArS.St, +t: String) -> rks.G(s, t, FAr.answer(r, s)):
  match r:
    case ArS.Took{s2, e, stop}:
      h => AS.as.absurd_tf({FAr.Live{s2} == FAr.Live{s} : FAr.St}, rks.tag(FAr.put_eff(e, Wr.put_bool(stop, "")), Wr.put_str(t, ""), h))
    case ArS.Refuse{u}:
      h => {==}

def rks.serve(q: FAr.Q, +s: ArS.St, +t: String) -> rks.G(s, t, FAr.serve(s, q)):
  match q:
    case FAr.QEv{e}:
      rks.answer(ArP.step(s, e), s, t)
    case FAr.QSnap{}:
      h => {==}

def rks.end(w: Bool, +s: ArS.St, q: FAr.Q, +t: String) -> rks.G(s, t, FAr.step.end(w, s, q)):
  match w:
    case True{}:
      rks.serve(q, s, t)
    case False{}:
      h => {==}

def rks.q(d: Wr.Dec<FAr.Q>, +s: ArS.St, +t: String) -> rks.G(s, t, FAr.step.q(s, d)):
  match d:
    case Wr.Got{q, rest}:
      rks.end(Wr.end(rest), s, q, t)
    case Wr.Bad{}:
      h => {==}

def AutoresearchEntry.autoresearch_refusal_keeps_state(s, i, t, refused):
  rks.q(FAr.get_q(i), s, t)(refused)
