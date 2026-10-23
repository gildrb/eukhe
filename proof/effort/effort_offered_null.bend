# eukhe: the proof of LAW effort_offered_null

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_offered_null(+map: Ef.LvMap, +l: Ef.Lv, null: {Ef.entry(l, map) == Ef.Null{} : Ef.Ent}) -> {Ef.has(Ef.offered(Ef.Mdl{True{}, map}), l) == False{} : Bool}:
  +ladder = Ef.ladder()
  +nk = Equal.cong(Ef.Ent, Bool, e => Ef.keep.e(l, e), Ef.entry(l, map), Ef.Null{}, null)
  LA.pe.offer_out(map, ladder, l, LA.pe.kat(map, ladder), {==}, Ef.at(ladder, l), {==}, nk)

def Laws.effort_offered_null(map, l, null):
  pe.effort_offered_null(map, l, null)
