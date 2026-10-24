# eukhe: the proof of LAW glob_walk_runs
#
# The open is the state of no hit. Along the walk the state is the state
# of the spec's ranking of every hit met (St, base/state.bend): a time is
# answered by Wants; a hit the entry wants is put in (base/steps.bend
# s_add); a hit it does not want leaves the first c of the ranking as
# they were (base/keep.bend filter), so the state is that of the ranking
# with the hit put in all the same. The page is then the spec's page.

import Base
import ../../bend/ffi_doc_glob.bend as FGb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/doc_glob.bend as DocGlob
import ./base/rank.bend as GR
import ./base/keep.bend as GK
import ./base/state.bend as GS
import ./base/steps.bend as GT

def gwr.not_f(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      GR.gp.absurd({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

# the hit at m, p after the ranking R, the entry's answer b
def gwr.b(b: Bool, +s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +m: Nat, +p: String, +t: List<&2, DocGlob.glob.Hit>, +eq: {DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, 1n+Nat.add(s, k), R) == b : Bool}, add: {FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p})) == (GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)), "") : FGb.St & String}, ih: {DocGlob.glob.Drive(t, GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) == DocGlob.glob.Trace(t, s, k, 1n+Nat.add(s, k), DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)) : List<&2, String>}) -> {List.append(&2, String, DocGlob.glob.If(List<&2, String>, DocGlob.glob.Yes(Wr.put_bool(b, "")), [Wr.put_bool(b, ""), DocGlob.glob.Snd(FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p})))], [Wr.put_bool(b, "")]), DocGlob.glob.Drive(t, DocGlob.glob.If(FGb.St, DocGlob.glob.Yes(Wr.put_bool(b, "")), DocGlob.glob.Fst(FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p}))), GS.gp.St(s, k, R)))) == DocGlob.glob.Trace(DocGlob.glob.Hit{m, p} <> t, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}:
  match b:
    case True{}:
      %Equal.sym(Bool, DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, 1n+Nat.add(s, k), R), True{}, eq) : {List.append(&2, String, ["T", DocGlob.glob.Snd(FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p})))], DocGlob.glob.Drive(t, DocGlob.glob.Fst(FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p}))))) == List.append(&2, String, DocGlob.glob.If(List<&2, String>, _, ["T", ""], ["F"]), DocGlob.glob.Trace(t, s, k, 1n+Nat.add(s, k), DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) : List<&2, String>}
      %Equal.sym(FGb.St & String, FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p})), (GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)), ""), add) : {List.append(&2, String, ["T", DocGlob.glob.Snd(_)], DocGlob.glob.Drive(t, DocGlob.glob.Fst(_))) == List.append(&2, String, ["T", ""], DocGlob.glob.Trace(t, s, k, 1n+Nat.add(s, k), DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => List.append(&2, String, ["T", ""], l), DocGlob.glob.Drive(t, GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))), DocGlob.glob.Trace(t, s, k, 1n+Nat.add(s, k), DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)), ih)
    case False{}:
      +c = {1n+Nat.add(s, k) : Nat}
      +both = gwr.not_f(Bool.and(Nat.is_le(c, DocGlob.glob.Len(DocGlob.glob.First(R, c))), Nat.is_lt(m, DocGlob.glob.Low(DocGlob.glob.First(R, c)))), eq)
      +full = GR.gp.and_l(Nat.is_le(c, DocGlob.glob.Len(DocGlob.glob.First(R, c))), Nat.is_lt(m, DocGlob.glob.Low(DocGlob.glob.First(R, c))), both)
      +old = GR.gp.and_r(Nat.is_le(c, DocGlob.glob.Len(DocGlob.glob.First(R, c))), Nat.is_lt(m, DocGlob.glob.Low(DocGlob.glob.First(R, c))), both)
      +kept = GK.gp.filter(m, p, R, c, full, old)
      +same = Equal.cong(List<&2, DocGlob.glob.Hit>, FGb.St, L => FGb.Gl{s, k, c, DocGlob.glob.Len(L), DocGlob.glob.Low(L), GR.gp.its(L)}, DocGlob.glob.First(DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R), c), DocGlob.glob.First(R, c), kept)
      %Equal.sym(Bool, DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, c, R), False{}, eq) : {List.append(&2, String, ["F"], DocGlob.glob.Drive(t, GS.gp.St(s, k, R))) == List.append(&2, String, DocGlob.glob.If(List<&2, String>, _, ["T", ""], ["F"]), DocGlob.glob.Trace(t, s, k, c, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) : List<&2, String>}
      %same : {List.append(&2, String, ["F"], DocGlob.glob.Drive(t, _)) == List.append(&2, String, ["F"], DocGlob.glob.Trace(t, s, k, c, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, l => List.append(&2, String, ["F"], l), DocGlob.glob.Drive(t, GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))), DocGlob.glob.Trace(t, s, k, c, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)), ih)

# the replies to the hit w and the rest of the walk, from the reply said
# to its time and the state met after it
def gwr.after(+w: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Hit>, +said: String, +met: FGb.St) -> List<&2, String>:
  List.append(&2, String, DocGlob.glob.If(List<&2, String>, DocGlob.glob.Yes(said), [said, DocGlob.glob.Snd(FGb.step(met, DocGlob.glob.spell_add(w)))], [said]), DocGlob.glob.Drive(t, DocGlob.glob.If(FGb.St, DocGlob.glob.Yes(said), DocGlob.glob.Fst(FGb.step(met, DocGlob.glob.spell_add(w))), met)))

def gwr.hit(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +m: Nat, +p: String, +t: List<&2, DocGlob.glob.Hit>, +hm: {LawsBase.wire_fits(m) == True{} : Bool}, hp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, ih: {DocGlob.glob.Drive(t, GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R))) == DocGlob.glob.Trace(t, s, k, 1n+Nat.add(s, k), DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)) : List<&2, String>}) -> {DocGlob.glob.Drive(DocGlob.glob.Hit{m, p} <> t, GS.gp.St(s, k, R)) == DocGlob.glob.Trace(DocGlob.glob.Hit{m, p} <> t, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}:
  +w = {DocGlob.glob.Hit{m, p} : DocGlob.glob.Hit}
  +said = {Wr.put_bool(DocGlob.glob.Wants(w, 1n+Nat.add(s, k), R), "") : String}
  +st = {GS.gp.St(s, k, R) : FGb.St}
  +e1 = Equal.cong(FGb.St & String, String, r => DocGlob.glob.Snd(r), FGb.step(st, DocGlob.glob.spell_met(w)), (st, said), GT.gp.s_met(s, k, R, m, p, hm))
  +e2 = Equal.cong(FGb.St & String, FGb.St, r => DocGlob.glob.Fst(r), FGb.step(st, DocGlob.glob.spell_met(w)), (st, said), GT.gp.s_met(s, k, R, m, p, hm))
  %Equal.sym(String, DocGlob.glob.Snd(FGb.step(st, DocGlob.glob.spell_met(w))), said, e1) : {gwr.after(w, t, _, DocGlob.glob.Fst(FGb.step(st, DocGlob.glob.spell_met(w)))) == DocGlob.glob.Trace(w <> t, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}
  %Equal.sym(FGb.St, DocGlob.glob.Fst(FGb.step(st, DocGlob.glob.spell_met(w))), st, e2) : {gwr.after(w, t, said, _) == DocGlob.glob.Trace(w <> t, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}
  gwr.b(DocGlob.glob.Wants(w, 1n+Nat.add(s, k), R), s, k, R, m, p, t, {==}, GT.gp.s_add(s, k, R, m, p, hm, hp), ih)

# the walk from the state of the ranking R
def gwr.walk(ws: List<&2, DocGlob.glob.Hit>, +s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +h: {DocGlob.glob.HitsFit(ws) == True{} : Bool}) -> {DocGlob.glob.Drive(ws, GS.gp.St(s, k, R)) == DocGlob.glob.Trace(ws, s, k, 1n+Nat.add(s, k), R) : List<&2, String>}:
  match ws:
    case Nil{}:
      %Equal.sym(FGb.St & String, FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_show()), (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)), GT.gp.s_show(s, k, R)) : {[DocGlob.glob.Snd(_)] == [DocGlob.glob.spell_page(R, s, k)] : List<&2, String>}
      {==}
    case w <> +t:
      match w:
        case DocGlob.glob.Hit{+m, +p}:
          +hw = GR.gp.and_l(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), DocGlob.glob.HitsFit(t), h)
          +ht = GR.gp.and_r(Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p))), DocGlob.glob.HitsFit(t), h)
          gwr.hit(s, k, R, m, p, t, GR.gp.and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), hw), GR.gp.and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(String.length(p)), hw), gwr.walk(t, s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R), ht))

def DocGlob.glob_walk_runs(s, lim, ws, h):
  +k = {DocGlob.glob.Size(lim) : Nat}
  +hs = GR.gp.and_l(LawsBase.wire_fits(s), Bool.and(LawsBase.core_mfits(lim), DocGlob.glob.HitsFit(ws)), h)
  +hr = GR.gp.and_r(LawsBase.wire_fits(s), Bool.and(LawsBase.core_mfits(lim), DocGlob.glob.HitsFit(ws)), h)
  +hl = GR.gp.and_l(LawsBase.core_mfits(lim), DocGlob.glob.HitsFit(ws), hr)
  +hw = GR.gp.and_r(LawsBase.core_mfits(lim), DocGlob.glob.HitsFit(ws), hr)
  +st = {GS.gp.St(s, k, Nil{}) : FGb.St}
  +e1 = Equal.cong(FGb.St & String, String, r => DocGlob.glob.Snd(r), DocGlob.glob.Open(s, lim), (st, ""), GT.gp.open(s, lim, hs, hl))
  +e2 = Equal.cong(FGb.St & String, FGb.St, r => DocGlob.glob.Fst(r), DocGlob.glob.Open(s, lim), (st, ""), GT.gp.open(s, lim, hs, hl))
  %Equal.sym(String, DocGlob.glob.Snd(DocGlob.glob.Open(s, lim)), "", e1) : {_ <> DocGlob.glob.Drive(ws, DocGlob.glob.Fst(DocGlob.glob.Open(s, lim))) == "" <> DocGlob.glob.Trace(ws, s, k, 1n+Nat.add(s, k), Nil{}) : List<&2, String>}
  %Equal.sym(FGb.St, DocGlob.glob.Fst(DocGlob.glob.Open(s, lim)), st, e2) : {"" <> DocGlob.glob.Drive(ws, _) == "" <> DocGlob.glob.Trace(ws, s, k, 1n+Nat.add(s, k), Nil{}) : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, l => "" <> l, DocGlob.glob.Drive(ws, st), DocGlob.glob.Trace(ws, s, k, 1n+Nat.add(s, k), Nil{}), gwr.walk(ws, s, k, Nil{}, hw))
