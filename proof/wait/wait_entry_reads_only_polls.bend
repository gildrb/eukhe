# eukhe: the proof of LAW wait_entry_reads_only_polls
# Whatever the stepper's poll decoder reads is three spelled Bools, then
# its rest (wire_bool_exact, Bool by Bool). Nothing read, or a rest that
# is not empty, answers the malformed-poll error, which the premise
# excludes; a poll read whole is the input's spelling.

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA

# a poll, then rest, spelled
def rp.sp(r: Wt.Polled, rest: String) -> String:
  match r:
    case Wt.Polled{w, c, l}:
      Wr.put_bool(w, Wr.put_bool(c, Wr.put_bool(l, rest)))

def rp.Poll(s: String, d: Wr.Dec<Wt.Polled>) -> Type:
  match d:
    case Wr.Got{r, rest}:
      {s == rp.sp(r, rest) : String}
    case Wr.Bad{}:
      Unit

def rp.late(-s: String, +w: Bool, +c: Bool, -s2: String, pre: {s == Wr.put_bool(w, Wr.put_bool(c, s2)) : String}, d: Wr.Dec<Bool>, inv: LA.wr.Bool(s2, d)) -> rp.Poll(s, FWt.get_ready.late(w, c, d)):
  match d:
    case Wr.Got{+l, +s3}:
      LA.wr.step(z => Wr.put_bool(w, Wr.put_bool(c, z)), s, s2, Wr.put_bool(l, s3), pre, inv)
    case Wr.Bad{}:
      Unit{}

def rp.cancel(-s: String, +w: Bool, -s1: String, pre: {s == Wr.put_bool(w, s1) : String}, d: Wr.Dec<Bool>, inv: LA.wr.Bool(s1, d)) -> rp.Poll(s, FWt.get_ready.cancel(w, d)):
  match d:
    case Wr.Got{+c, +s2}:
      rp.late(s, w, c, s2, LA.wr.step(z => Wr.put_bool(w, z), s, s1, Wr.put_bool(c, s2), pre, inv), Wr.get_bool(s2), LA.wr.bool(s2))
    case Wr.Bad{}:
      Unit{}

def rp.go(-s: String, d: Wr.Dec<Bool>, inv: LA.wr.Bool(s, d)) -> rp.Poll(s, FWt.get_ready.go(d)):
  match d:
    case Wr.Got{+w, +s1}:
      rp.cancel(s, w, s1, inv, Wr.get_bool(s1), LA.wr.bool(s1))
    case Wr.Bad{}:
      Unit{}

def rp.G(s: String) -> Type:
  Sigma<&1, &1, Wt.Polled, r => {s == WaitLaws.ww_spell(r) : String}>

# a poll read whole is the input's spelling
def rp.done(-s: String, r: Wt.Polled, pre: {s == rp.sp(r, "") : String}) -> rp.G(s):
  match r:
    case Wt.Polled{w, c, l}:
      (Wt.Polled{w, c, l}, pre)

# a poll read with input left over answers the error form
def rp.fin(-s: String, +w: Wt.W, +r: Wt.Polled, rest: String, pre: {s == rp.sp(r, rest) : String}, ok: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.step.end(Wr.end(rest), w, r))) == False{} : Bool}) -> rp.G(s):
  match rest:
    case SNil{}:
      rp.done(s, r, pre)
    case SCon{h, t}:
      LA.pw.absurd(rp.G(s), ok)

def rp.main(-s: String, +w: Wt.W, d: Wr.Dec<Wt.Polled>, inv: rp.Poll(s, d), ok: {LawsBase.wire_opens_err(WaitLaws.ww_reply(FWt.step.poll(w, d))) == False{} : Bool}) -> rp.G(s):
  match d:
    case Wr.Got{+r, +rest}:
      rp.fin(s, w, r, rest, inv, ok)
    case Wr.Bad{}:
      LA.pw.absurd(rp.G(s), ok)

def WaitLaws.wait_entry_reads_only_polls(w, s, other):
  rp.main(s, w, FWt.get_ready(s), rp.go(s, Wr.get_bool(s), LA.wr.bool(s)), other)
