# eukhe: the proof of LAW meet_orphan_anywhere

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg

# the lock file of a swept name x, where no entry has the name x: an orphan
def oa.here(+x: String, +all: List<&2, Sg.Seen>, sw: {True{} == Staging.sp_swept(x) : Bool}, gone: {LawsBase.text_has_name(x, all) == False{} : Bool}) -> {LA.rr.m(Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}}, all) == Sg.MOrphan{} : Sg.Met}:
  %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".lock", String.append(x, ".lock")), Some{x}, LStg.stg.unsuffix_app(x, ".lock")) : {LA.rr.m.file(_, all) == Sg.MOrphan{} : Sg.Met}
  %sw : {LA.rr.m.lock(_, LawsBase.text_has_name(x, all)) == Sg.MOrphan{} : Sg.Met}
  %Equal.sym(Bool, LawsBase.text_has_name(x, all), False{}, gone) : {LA.rr.m.lock(True{}, _) == Sg.MOrphan{} : Sg.Met}
  {==}

def Staging.meet_orphan_anywhere(pre, post, t, l, id, full, u, gone):
  +x = Staging.sp_mint(t, l, id)
  +lf = {Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}} : Sg.Seen}
  LA.mm.found(pre, lf, post, Sg.MOrphan{}, oa.here(x, List.append(&2, Sg.Seen, pre, lf <> post), Equal.sym(Bool, Staging.sp_swept(x), True{}, LA.rr.minted(t, l, id, full, u)), gone))
