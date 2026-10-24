# eukhe: the proof of LAW glob_events_answer
#
# The open is the state of no hit; each event moves the state of the
# spec's ranking R of the hits sent whole as the spec says
# (base/steps.bend): a time answers Wants and keeps it, a hit whole is put
# in, the page is the spec's page and keeps it.

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/doc_glob.bend as DocGlob
import ./base/rank.bend as GR
import ./base/state.bend as GS
import ./base/steps.bend as GT

# the replies to the rest after the step r of one event
def gea.after(+t: List<&2, DocGlob.glob.Ev>, +out: String, +st: FGb.St) -> List<&2, String>:
  out <> DocGlob.glob.Steps(t, st)

# one event e before t, its step r from st
def gea.step(+e: DocGlob.glob.Ev, +t: List<&2, DocGlob.glob.Ev>, +st: FGb.St, +st2: FGb.St, +out: String, +r: {FGb.step(st, DocGlob.glob.spell_ev(e)) == (st2, out) : FGb.St & String}) -> {DocGlob.glob.Steps(e <> t, st) == out <> DocGlob.glob.Steps(t, st2) : List<&2, String>}:
  +e1 = Equal.cong(FGb.St & String, String, q => DocGlob.glob.Snd(q), FGb.step(st, DocGlob.glob.spell_ev(e)), (st2, out), r)
  +e2 = Equal.cong(FGb.St & String, FGb.St, q => DocGlob.glob.Fst(q), FGb.step(st, DocGlob.glob.spell_ev(e)), (st2, out), r)
  %Equal.sym(String, DocGlob.glob.Snd(FGb.step(st, DocGlob.glob.spell_ev(e))), out, e1) : {gea.after(t, _, DocGlob.glob.Fst(FGb.step(st, DocGlob.glob.spell_ev(e)))) == out <> DocGlob.glob.Steps(t, st2) : List<&2, String>}
  %Equal.sym(FGb.St, DocGlob.glob.Fst(FGb.step(st, DocGlob.glob.spell_ev(e))), st2, e2) : {gea.after(t, out, _) == out <> DocGlob.glob.Steps(t, st2) : List<&2, String>}
  {==}

def gea.cons(+x: String, +a: List<&2, String>, +b: List<&2, String>, e: {a == b : List<&2, String>}) -> {x <> a == x <> b : List<&2, String>}:
  Equal.cong(List<&2, String>, List<&2, String>, l => x <> l, a, b, e)

def gea.hit(+h: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Ev>, f: {Bool.and(DocGlob.glob.HitsFit([h]), DocGlob.glob.EvsFit(t)) == True{} : Bool}) -> {DocGlob.glob.HitsFit([h]) == True{} : Bool}:
  GR.gp.and_l(DocGlob.glob.HitsFit([h]), DocGlob.glob.EvsFit(t), f)

# the events from the state of the ranking R
def gea.events(es: List<&2, DocGlob.glob.Ev>, +s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +h: {DocGlob.glob.EvsFit(es) == True{} : Bool}) -> {DocGlob.glob.Steps(es, GS.gp.St(s, k, R)) == DocGlob.glob.Answers(es, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case DocGlob.glob.EMet{w}:
          match w:
            case DocGlob.glob.Hit{+m, +p}:
              +hw = GR.gp.and_l(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}), DocGlob.glob.EvsFit(t), h)
              +ht = GR.gp.and_r(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}), DocGlob.glob.EvsFit(t), h)
              +hmp = GR.gp.and_l(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}, hw)
              +hm = GR.gp.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), hmp)
              +said = {Wr.put_bool(DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, 1n+Nat.add(s, k), R), "") : String}
              Equal.trans(List<&2, String>, DocGlob.glob.Steps(DocGlob.glob.EMet{DocGlob.glob.Hit{m, p}} <> t, GS.gp.St(s, k, R)), said <> DocGlob.glob.Steps(t, GS.gp.St(s, k, R)), said <> DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R), gea.step(DocGlob.glob.EMet{DocGlob.glob.Hit{m, p}}, t, GS.gp.St(s, k, R), GS.gp.St(s, k, R), said, GT.gp.s_met(s, k, R, m, p, hm)), gea.cons(said, DocGlob.glob.Steps(t, GS.gp.St(s, k, R)), DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R), gea.events(t, s, k, R, ht)))
        case DocGlob.glob.EAdd{w}:
          match w:
            case DocGlob.glob.Hit{+m, +p}:
              +hw = GR.gp.and_l(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}), DocGlob.glob.EvsFit(t), h)
              +ht = GR.gp.and_r(Bool.and(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}), DocGlob.glob.EvsFit(t), h)
              +hmp = GR.gp.and_l(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), True{}, hw)
              +hm = GR.gp.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), hmp)
              +hp = GR.gp.and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), hmp)
              +R2 = {DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R) : List<&2, DocGlob.glob.Hit>}
              Equal.trans(List<&2, String>, DocGlob.glob.Steps(DocGlob.glob.EAdd{DocGlob.glob.Hit{m, p}} <> t, GS.gp.St(s, k, R)), "" <> DocGlob.glob.Steps(t, GS.gp.St(s, k, R2)), "" <> DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R2), gea.step(DocGlob.glob.EAdd{DocGlob.glob.Hit{m, p}}, t, GS.gp.St(s, k, R), GS.gp.St(s, k, R2), "", GT.gp.s_add(s, k, R, m, p, hm, hp)), gea.cons("", DocGlob.glob.Steps(t, GS.gp.St(s, k, R2)), DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R2), gea.events(t, s, k, R2, ht)))
        case DocGlob.glob.EShow{}:
          +page = {DocGlob.glob.spell_page(R, s, k) : String}
          Equal.trans(List<&2, String>, DocGlob.glob.Steps(DocGlob.glob.EShow{} <> t, GS.gp.St(s, k, R)), page <> DocGlob.glob.Steps(t, GS.gp.St(s, k, R)), page <> DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R), gea.step(DocGlob.glob.EShow{}, t, GS.gp.St(s, k, R), GS.gp.St(s, k, R), page, GT.gp.s_show(s, k, R)), gea.cons(page, DocGlob.glob.Steps(t, GS.gp.St(s, k, R)), DocGlob.glob.Answers(t, s, k, 1n+Nat.add(s, k), R), gea.events(t, s, k, R, h)))

def DocGlob.glob_events_answer(s, lim, es, h):
  +k = {DocGlob.glob.Size(lim) : Nat}
  +hsl = GR.gp.and_l(Bool.and(LawsBase.wire_fits(s), LawsBase.core_mfits(lim)), DocGlob.glob.EvsFit(es), h)
  +he = GR.gp.and_r(Bool.and(LawsBase.wire_fits(s), LawsBase.core_mfits(lim)), DocGlob.glob.EvsFit(es), h)
  +hs = GR.gp.and_l(LawsBase.wire_fits(s), LawsBase.core_mfits(lim), hsl)
  +hl = GR.gp.and_r(LawsBase.wire_fits(s), LawsBase.core_mfits(lim), hsl)
  +st = {GS.gp.St(s, k, Nil{}) : FGb.St}
  +e1 = Equal.cong(FGb.St & String, String, r => DocGlob.glob.Snd(r), DocGlob.glob.Open(s, lim), (st, ""), GT.gp.open(s, lim, hs, hl))
  +e2 = Equal.cong(FGb.St & String, FGb.St, r => DocGlob.glob.Fst(r), DocGlob.glob.Open(s, lim), (st, ""), GT.gp.open(s, lim, hs, hl))
  %Equal.sym(String, DocGlob.glob.Snd(DocGlob.glob.Open(s, lim)), "", e1) : {_ <> DocGlob.glob.Steps(es, DocGlob.glob.Fst(DocGlob.glob.Open(s, lim))) == "" <> DocGlob.glob.Answers(es, s, k, 1n+Nat.add(s, k), Nil{}) : List<&2, String>}
  %Equal.sym(FGb.St, DocGlob.glob.Fst(DocGlob.glob.Open(s, lim)), st, e2) : {"" <> DocGlob.glob.Steps(es, _) == "" <> DocGlob.glob.Answers(es, s, k, 1n+Nat.add(s, k), Nil{}) : List<&2, String>}
  gea.cons("", DocGlob.glob.Steps(es, st), DocGlob.glob.Answers(es, s, k, 1n+Nat.add(s, k), Nil{}), gea.events(es, s, k, Nil{}, he))
