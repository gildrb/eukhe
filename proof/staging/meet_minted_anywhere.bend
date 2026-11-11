# eukhe: the proof of LAW meet_minted_anywhere

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

# a directory with a minted name is judged, whatever the listing
def ma.here(+t: String, +l: Staging.SpLab, +id: String, -m: Bool, -all: List<&2, Sg.Seen>, full: {String.is_empty(t) == False{} : Bool}, u: {Staging.sp_hexn(32n, id) == True{} : Bool}) -> {LA.rr.m(Sg.Seen{Sg.Utf{Staging.sp_mint(t, l, id)}, Sg.KDir{m}}, all) == Sg.MLeftover{} : Sg.Met}:
  %Equal.sym(Bool, Staging.sp_swept(Staging.sp_mint(t, l, id)), True{}, LA.rr.minted(t, l, id, full, u)) : {LA.rr.m.dir(_, m) == Sg.MLeftover{} : Sg.Met}
  {==}

def Staging.meet_minted_anywhere(pre, post, t, l, id, m, full, u):
  +x = {Sg.Seen{Sg.Utf{Staging.sp_mint(t, l, id)}, Sg.KDir{m}} : Sg.Seen}
  LA.mm.found(pre, x, post, Sg.MLeftover{}, ma.here(t, l, id, m, List.append(&2, Sg.Seen, pre, x <> post), full, u))
