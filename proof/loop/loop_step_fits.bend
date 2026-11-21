# eukhe: the proof of LAW loop_step_fits
#
# PROOF: the state is opened and its fits split into one fact per field
# (lsf.g*), the room into the iteration and the failed turns one more;
# then per event, along the step: a state that keeps its fields fits by
# the premise itself (lp_st_fits does not read the phase); a new state is
# built field by field (lsf.mk). The new values: a fresh loop's count
# and deadline (the deadline of a span: lf.cut_fits), its prompt
# and condition from the event, the next iteration and one more failed
# turn by the room, one automatic iteration fewer (lf.less_fits), the
# evidence of a check from the event.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/base.bend as LawsBase
import ../../laws/loop/entry.bend as LoopEntry
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LALoopEntry
import ./base/fits.bend as LALoopFits

# The fits of a state, field by field
# -----------------------------------

def lsf.R6(f: Nat, x: Lp.Last) -> Bool:
  Bool.and(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(x))

def lsf.R5(b: String, f: Nat, x: Lp.Last) -> Bool:
  Bool.and(LawsBase.wire_fits(String.length(b)), lsf.R6(f, x))

def lsf.R4(c: Lp.Cond, b: String, f: Nat, x: Lp.Last) -> Bool:
  Bool.and(LoopEntry.lp_cond_fits(c), lsf.R5(b, f, x))

def lsf.R3(d: Maybe<&2, Nat>, c: Lp.Cond, b: String, f: Nat, x: Lp.Last) -> Bool:
  Bool.and(LawsBase.wire_mfits(d), lsf.R4(c, b, f, x))

def lsf.R2(l: Maybe<&2, Nat>, d: Maybe<&2, Nat>, c: Lp.Cond, b: String, f: Nat, x: Lp.Last) -> Bool:
  Bool.and(LawsBase.wire_mfits(l), lsf.R3(d, c, b, f, x))

# a state whose every field fits fits
def lsf.mk(-p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}:
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), lsf.R2(l, d, c, b, f, x), hi, LAWireSpell.ws_and_tt(LawsBase.wire_mfits(l), lsf.R3(d, c, b, f, x), hl, LAWireSpell.ws_and_tt(LawsBase.wire_mfits(d), lsf.R4(c, b, f, x), hd, LAWireSpell.ws_and_tt(LoopEntry.lp_cond_fits(c), lsf.R5(b, f, x), hc, LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(b)), lsf.R6(f, x), hb, LAWireSpell.ws_and_tt(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(x), hf, hx))))))

def lsf.t2(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {lsf.R2(l, d, c, b, f, x) == True{} : Bool}:
  LALoopEntry.le.and_r(LawsBase.wire_fits(i), lsf.R2(l, d, c, b, f, x), h)

def lsf.t3(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {lsf.R3(d, c, b, f, x) == True{} : Bool}:
  LALoopEntry.le.and_r(LawsBase.wire_mfits(l), lsf.R3(d, c, b, f, x), lsf.t2(p, i, l, d, c, b, f, x, h))

def lsf.t4(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {lsf.R4(c, b, f, x) == True{} : Bool}:
  LALoopEntry.le.and_r(LawsBase.wire_mfits(d), lsf.R4(c, b, f, x), lsf.t3(p, i, l, d, c, b, f, x, h))

def lsf.t5(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {lsf.R5(b, f, x) == True{} : Bool}:
  LALoopEntry.le.and_r(LoopEntry.lp_cond_fits(c), lsf.R5(b, f, x), lsf.t4(p, i, l, d, c, b, f, x, h))

def lsf.t6(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {lsf.R6(f, x) == True{} : Bool}:
  LALoopEntry.le.and_r(LawsBase.wire_fits(String.length(b)), lsf.R6(f, x), lsf.t5(p, i, l, d, c, b, f, x, h))

def lsf.gi(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LawsBase.wire_fits(i) == True{} : Bool}:
  LALoopEntry.le.and_l(LawsBase.wire_fits(i), lsf.R2(l, d, c, b, f, x), h)

def lsf.gl(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LawsBase.wire_mfits(l) == True{} : Bool}:
  LALoopEntry.le.and_l(LawsBase.wire_mfits(l), lsf.R3(d, c, b, f, x), lsf.t2(p, i, l, d, c, b, f, x, h))

def lsf.gd(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LawsBase.wire_mfits(d) == True{} : Bool}:
  LALoopEntry.le.and_l(LawsBase.wire_mfits(d), lsf.R4(c, b, f, x), lsf.t3(p, i, l, d, c, b, f, x, h))

def lsf.gc(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LoopEntry.lp_cond_fits(c) == True{} : Bool}:
  LALoopEntry.le.and_l(LoopEntry.lp_cond_fits(c), lsf.R5(b, f, x), lsf.t4(p, i, l, d, c, b, f, x, h))

def lsf.gb(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LawsBase.wire_fits(String.length(b)) == True{} : Bool}:
  LALoopEntry.le.and_l(LawsBase.wire_fits(String.length(b)), lsf.R6(f, x), lsf.t5(p, i, l, d, c, b, f, x, h))

def lsf.gf(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LawsBase.wire_fits(f) == True{} : Bool}:
  LALoopEntry.le.and_l(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(x), lsf.t6(p, i, l, d, c, b, f, x, h))

def lsf.gx(-p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, h: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LoopEntry.lp_last_fits(x) == True{} : Bool}:
  LALoopEntry.le.and_r(LawsBase.wire_fits(f), LoopEntry.lp_last_fits(x), lsf.t6(p, i, l, d, c, b, f, x, h))

# the evidence of a check after iteration i fits
def lsf.check(-i: Nat, -ev: Lp.Evid, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hev: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}) -> {LoopEntry.lp_last_fits(Lp.Check{i, ev}) == True{} : Bool}:
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(i), LoopEntry.lp_evid_fits(ev), hi, hev)

# The next iteration, or the end
# ------------------------------

def lsf.adv_on(h: Maybe<&2, Lp.End>, -i: Nat, +l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.advance.on(h, i, l, d, c, b, f, x))) == True{} : Bool}:
  match h:
    case Some{why}:
      lsf.mk(Lp.Ended{why}, i, l, d, c, b, f, x, hi, hl, hd, hc, hb, hf, hx)
    case None{}:
      lsf.mk(Lp.Turn{}, 1n+i, Lp.less(l), d, c, b, f, x, hi1, LALoopFits.lf.less_fits(l, hl), hd, hc, hb, hf, hx)

def lsf.adv(-i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +now: Nat, +fu: Bool, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.advance(i, l, d, c, b, f, x, now, fu))) == True{} : Bool}:
  lsf.adv_on(Lp.halt(f, fu, l, d, now), i, l, d, c, b, f, x, hi, hi1, hl, hd, hc, hb, hf, hx)

# A settled turn
# --------------

def lsf.gate(c: Lp.Cond, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, +f: Nat, -x: Lp.Last, +now: Nat, +fu: Bool, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.gate(c, i, l, d, b, f, x, now, fu))) == True{} : Bool}:
  match c:
    case Lp.NoCond{}:
      lsf.adv(i, l, d, Lp.NoCond{}, b, f, x, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx)
    case Lp.Until{cmd}:
      lsf.mk(Lp.Judging{}, i, l, d, Lp.Until{cmd}, b, f, x, hi, hl, hd, hc, hb, hf, hx)
    case Lp.While{cmd}:
      lsf.mk(Lp.Judging{}, i, l, d, Lp.While{cmd}, b, f, x, hi, hl, hd, hc, hb, hf, hx)
    case Lp.Stated{u, t}:
      lsf.mk(Lp.Judging{}, i, l, d, Lp.Stated{u, t}, b, f, x, hi, hl, hd, hc, hb, hf, hx)

def lsf.out(o: Lp.Out, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +now: Nat, +fu: Bool, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf1: {LawsBase.wire_fits(1n+f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.settled.out(o, i, l, d, c, b, f, x, now, fu))) == True{} : Bool}:
  match o:
    case Lp.Ran{}:
      lsf.gate(c, i, l, d, b, 0n, x, now, fu, hi, hi1, hl, hd, hc, hb, {==}, hx)
    case Lp.Errored{}:
      lsf.gate(c, i, l, d, b, 1n+f, x, now, fu, hi, hi1, hl, hd, hc, hb, hf1, hx)

def lsf.smine(bl: Bool, +o: Lp.Out, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +now: Nat, +fu: Bool, hs: {LoopEntry.lp_st_fits(Lp.St{Lp.Turn{}, i, l, d, c, b, f, x}) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf1: {LawsBase.wire_fits(1n+f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.settled.mine(bl, o, i, l, d, c, b, f, x, now, fu))) == True{} : Bool}:
  match bl:
    case True{}:
      hs
    case False{}:
      lsf.out(o, i, l, d, c, b, f, x, now, fu, hi, hi1, hl, hd, hc, hb, hf1, hx)

def lsf.settled(mine: Bool, -p: Lp.Phase, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +o: Lp.Out, +bl: Bool, +now: Nat, +fu: Bool, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf1: {LawsBase.wire_fits(1n+f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.settled(mine, p, i, l, d, c, b, f, x, o, bl, now, fu))) == True{} : Bool}:
  match mine:
    case True{}:
      lsf.smine(bl, o, i, l, d, c, b, f, x, now, fu, hs, hi, hi1, hl, hd, hc, hb, hf1, hx)
    case False{}:
      hs

# A judged check
# --------------

def lsf.verdict(v: Lp.Verdict, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, -ev: Lp.Evid, +now: Nat, +fu: Bool, +hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}, hev: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.judged.verdict(v, i, l, d, c, b, f, x, ev, now, fu))) == True{} : Bool}:
  match v:
    case Lp.Confirmed{}:
      lsf.mk(Lp.Ended{Lp.Satisfied{}}, i, l, d, c, b, f, Lp.Check{i, ev}, hi, hl, hd, hc, hb, hf, lsf.check(i, ev, hi, hev))
    case Lp.Refuted{}:
      lsf.adv(i, l, d, c, b, f, Lp.Check{i, ev}, now, fu, hi, hi1, hl, hd, hc, hb, hf, lsf.check(i, ev, hi, hev))
    case Lp.Broken{}:
      lsf.mk(Lp.Ended{Lp.CheckBroke{}}, i, l, d, c, b, f, Lp.Check{i, ev}, hi, hl, hd, hc, hb, hf, lsf.check(i, ev, hi, hev))
    case Lp.Unjudged{}:
      lsf.mk(Lp.Judging{}, i, l, d, c, b, f, x, hi, hl, hd, hc, hb, hf, hx)

def lsf.jcond(c: Lp.Cond, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, -b: String, +f: Nat, -x: Lp.Last, +ev: Lp.Evid, +now: Nat, +fu: Bool, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}, hev: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.judged.cond(c, i, l, d, b, f, x, ev, now, fu))) == True{} : Bool}:
  match c:
    case Lp.NoCond{}:
      lsf.adv(i, l, d, Lp.NoCond{}, b, f, x, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx)
    case Lp.Until{cmd}:
      lsf.verdict(Lp.judge(True{}, ev), i, l, d, Lp.Until{cmd}, b, f, x, ev, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx, hev)
    case Lp.While{cmd}:
      lsf.verdict(Lp.judge(False{}, ev), i, l, d, Lp.While{cmd}, b, f, x, ev, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx, hev)
    case Lp.Stated{+u, t}:
      lsf.verdict(Lp.said(u, ev), i, l, d, Lp.Stated{u, t}, b, f, x, ev, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx, hev)

def lsf.jmine(bl: Bool, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +ev: Lp.Evid, +now: Nat, +fu: Bool, hs: {LoopEntry.lp_st_fits(Lp.St{Lp.Judging{}, i, l, d, c, b, f, x}) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}, hev: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.judged.mine(bl, i, l, d, c, b, f, x, ev, now, fu))) == True{} : Bool}:
  match bl:
    case True{}:
      hs
    case False{}:
      lsf.jcond(c, i, l, d, b, f, x, ev, now, fu, hi, hi1, hl, hd, hc, hb, hf, hx, hev)

def lsf.judged(mine: Bool, -p: Lp.Phase, -i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, -b: String, +f: Nat, -x: Lp.Last, +ev: Lp.Evid, +bl: Bool, +now: Nat, +fu: Bool, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}, hev: {LoopEntry.lp_evid_fits(ev) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.judged(mine, p, i, l, d, c, b, f, x, ev, bl, now, fu))) == True{} : Bool}:
  match mine:
    case True{}:
      lsf.jmine(bl, i, l, d, c, b, f, x, ev, now, fu, hs, hi, hi1, hl, hd, hc, hb, hf, hx, hev)
    case False{}:
      hs

# `/loop`, the stop, the interrupt, a prompt, a restart
# ------------------------------------------------------

def lsf.turns(lim: Lp.Limit, h: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}) -> {LawsBase.wire_mfits(Lp.turns(lim)) == True{} : Bool}:
  match lim:
    case Lp.NoLimit{}:
      {==}
    case Lp.Count{n}:
      h
    case Lp.Span{ms}:
      {==}

def lsf.until(lim: Lp.Limit, now: Nat) -> {LawsBase.wire_mfits(Lp.until(lim, now)) == True{} : Bool}:
  match lim:
    case Lp.NoLimit{}:
      {==}
    case Lp.Count{n}:
      {==}
    case Lp.Span{ms}:
      LALoopFits.lf.cut_fits(Nat.add(now, ms))

def lsf.start(pr: Maybe<&2, String>, +lim: Lp.Limit, -c2: Lp.Cond, +now: Nat, +hlim: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}, hc2: {LoopEntry.lp_cond_fits(c2) == True{} : Bool}, hpr: {LoopEntry.lp_mstr_fits(pr) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.start(lim, c2, pr, now))) == True{} : Bool}:
  match pr:
    case None{}:
      lsf.mk(Lp.Armed{}, 0n, Lp.turns(lim), Lp.until(lim, now), c2, "", 0n, Lp.NoCheck{}, {==}, lsf.turns(lim, hlim), lsf.until(lim, now), hc2, {==}, {==}, {==})
    case Some{t}:
      lsf.mk(Lp.Turn{}, 1n, Lp.turns(lim), Lp.until(lim, now), c2, t, 0n, Lp.NoCheck{}, {==}, lsf.turns(lim, hlim), lsf.until(lim, now), hc2, hpr, {==}, {==})

def lsf.enter(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, +lim: Lp.Limit, -c2: Lp.Cond, +pr: Maybe<&2, String>, +now: Nat, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, hlim: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}, hc2: {LoopEntry.lp_cond_fits(c2) == True{} : Bool}, hpr: {LoopEntry.lp_mstr_fits(pr) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.enter(live, i, l, d, c, b, f, x, lim, c2, pr, now))) == True{} : Bool}:
  match live:
    case True{}:
      hs
    case False{}:
      lsf.start(pr, lim, c2, now, hlim, hc2, hpr)

def lsf.stop(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.stop(live, p, i, l, d, c, b, f, x))) == True{} : Bool}:
  match live:
    case True{}:
      hs
    case False{}:
      hs

def lsf.abort(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, hi: {LawsBase.wire_fits(i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, hf: {LawsBase.wire_fits(f) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.abort(live, p, i, l, d, c, b, f, x))) == True{} : Bool}:
  match live:
    case True{}:
      lsf.mk(Lp.Paused{}, i, l, d, c, "", f, x, hi, hl, hd, hc, {==}, hf, hx)
    case False{}:
      hs

def lsf.prompt(live: Bool, -p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, -t: String, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, hi1: {LawsBase.wire_fits(1n+i) == True{} : Bool}, hl: {LawsBase.wire_mfits(l) == True{} : Bool}, hd: {LawsBase.wire_mfits(d) == True{} : Bool}, hc: {LoopEntry.lp_cond_fits(c) == True{} : Bool}, ht: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}, hx: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.prompt(live, p, i, l, d, c, b, f, x, t))) == True{} : Bool}:
  match live:
    case True{}:
      lsf.mk(Lp.Turn{}, 1n+i, l, d, c, t, 0n, x, hi1, hl, hd, hc, ht, {==}, hx)
    case False{}:
      hs

def lsf.restart(p: Lp.Phase, -i: Nat, -l: Maybe<&2, Nat>, -d: Maybe<&2, Nat>, -c: Lp.Cond, -b: String, -f: Nat, -x: Lp.Last, hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.state(Lp.restart(p, i, l, d, c, b, f, x))) == True{} : Bool}:
  match p:
    case Lp.Off{}:
      hs
    case Lp.Armed{}:
      hs
    case Lp.Turn{}:
      hs
    case Lp.Judging{}:
      hs
    case Lp.Paused{}:
      hs
    case Lp.Ended{w}:
      hs

# The step
# --------

def lsf.ev(e: Lp.Ev, +p: Lp.Phase, +i: Nat, +l: Maybe<&2, Nat>, +d: Maybe<&2, Nat>, +c: Lp.Cond, +b: String, +f: Nat, +x: Lp.Last, +hs: {LoopEntry.lp_st_fits(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, +room: {LoopEntry.lp_st_room(Lp.St{p, i, l, d, c, b, f, x}) == True{} : Bool}, +he: {LoopEntry.lp_ev_fits(e) == True{} : Bool}) -> {LoopEntry.lp_st_fits(S.next(Lp.St{p, i, l, d, c, b, f, x}, e)) == True{} : Bool}:
  match e:
    case Lp.Enter{+lim, +c2, +pr, +now}:
      +h1 = LALoopEntry.le.and_r(LoopEntry.lp_limit_fits(lim), Bool.and(LoopEntry.lp_cond_fits(c2), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now))), he)
      +h2 = LALoopEntry.le.and_r(LoopEntry.lp_cond_fits(c2), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now)), h1)
      lsf.enter(Lp.on(p), p, i, l, d, c, b, f, x, lim, c2, pr, now, hs, LALoopEntry.le.and_l(LoopEntry.lp_limit_fits(lim), Bool.and(LoopEntry.lp_cond_fits(c2), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now))), he), LALoopEntry.le.and_l(LoopEntry.lp_cond_fits(c2), Bool.and(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now)), h1), LALoopEntry.le.and_l(LoopEntry.lp_mstr_fits(pr), LawsBase.wire_fits(now), h2))
    case Lp.Stop{}:
      lsf.stop(Lp.on(p), p, i, l, d, c, b, f, x, hs)
    case Lp.Abort{}:
      lsf.abort(Lp.on(p), p, i, l, d, c, b, f, x, hs, lsf.gi(p, i, l, d, c, b, f, x, hs), lsf.gl(p, i, l, d, c, b, f, x, hs), lsf.gd(p, i, l, d, c, b, f, x, hs), lsf.gc(p, i, l, d, c, b, f, x, hs), lsf.gf(p, i, l, d, c, b, f, x, hs), lsf.gx(p, i, l, d, c, b, f, x, hs))
    case Lp.Prompt{t}:
      lsf.prompt(Lp.on(p), p, i, l, d, c, b, f, x, t, hs, LALoopEntry.le.and_l(LawsBase.wire_fits(1n+i), LawsBase.wire_fits(1n+f), room), lsf.gl(p, i, l, d, c, b, f, x, hs), lsf.gd(p, i, l, d, c, b, f, x, hs), lsf.gc(p, i, l, d, c, b, f, x, hs), he, lsf.gx(p, i, l, d, c, b, f, x, hs))
    case Lp.Settled{+k, o, bl, now, fu}:
      lsf.settled(Bool.and(Lp.in_turn(p), Nat.is_eq(k, i)), p, i, l, d, c, b, f, x, o, bl, now, fu, hs, lsf.gi(p, i, l, d, c, b, f, x, hs), LALoopEntry.le.and_l(LawsBase.wire_fits(1n+i), LawsBase.wire_fits(1n+f), room), lsf.gl(p, i, l, d, c, b, f, x, hs), lsf.gd(p, i, l, d, c, b, f, x, hs), lsf.gc(p, i, l, d, c, b, f, x, hs), lsf.gb(p, i, l, d, c, b, f, x, hs), LALoopEntry.le.and_r(LawsBase.wire_fits(1n+i), LawsBase.wire_fits(1n+f), room), lsf.gx(p, i, l, d, c, b, f, x, hs))
    case Lp.Judged{+k, +ev, bl, +now, fu}:
      +h1 = LALoopEntry.le.and_r(LawsBase.wire_fits(k), Bool.and(LoopEntry.lp_evid_fits(ev), LawsBase.wire_fits(now)), he)
      lsf.judged(Bool.and(Lp.in_judging(p), Nat.is_eq(k, i)), p, i, l, d, c, b, f, x, ev, bl, now, fu, hs, lsf.gi(p, i, l, d, c, b, f, x, hs), LALoopEntry.le.and_l(LawsBase.wire_fits(1n+i), LawsBase.wire_fits(1n+f), room), lsf.gl(p, i, l, d, c, b, f, x, hs), lsf.gd(p, i, l, d, c, b, f, x, hs), lsf.gc(p, i, l, d, c, b, f, x, hs), lsf.gb(p, i, l, d, c, b, f, x, hs), lsf.gf(p, i, l, d, c, b, f, x, hs), lsf.gx(p, i, l, d, c, b, f, x, hs), LALoopEntry.le.and_l(LoopEntry.lp_evid_fits(ev), LawsBase.wire_fits(now), h1))
    case Lp.Restart{}:
      lsf.restart(p, i, l, d, c, b, f, x, hs)

def LoopEntry.loop_step_fits(s, e, hs, room, he):
  match s:
    case Lp.St{p, i, l, d, c, b, f, x}:
      lsf.ev(e, p, i, l, d, c, b, f, x, hs, room, he)
