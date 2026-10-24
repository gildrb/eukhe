# eukhe: the proof of LAW meet_minted_orphan

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./meet_exact.bend as PMeetExact

# the lock file of a swept name x, alone: an orphan
def mo.alone(+x: String, sw: {True{} == Staging.sp_swept(x) : Bool}) -> {Sg.meet([Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}}]) == [Sg.MOrphan{}] : List<&2, Sg.Met>}:
  +k = String.append(x, ".lock")
  +lf = {Sg.Seen{Sg.Utf{k}, Sg.KFile{}} : Sg.Seen}
  %Equal.sym(List<&2, Sg.Met>, Sg.meet([lf]), Staging.sp_meet([lf]), Staging.meet_exact([lf])) : {_ == [Sg.MOrphan{}] : List<&2, Sg.Met>}
  %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".lock", k), Some{x}, LStg.stg.unsuffix_app(x, ".lock")) : {[Staging.sp_met.file(_, [lf])] == [Sg.MOrphan{}] : List<&2, Sg.Met>}
  %sw : {[Staging.sp_met.lock(_, LawsBase.text_has_name(x, [lf]))] == [Sg.MOrphan{}] : List<&2, Sg.Met>}
  %Equal.sym(Bool, LawsBase.text_same(k, x), False{}, LA.rr.lock_ne(x)) : {[Staging.sp_met.lock(True{}, Bool.or(_, False{}))] == [Sg.MOrphan{}] : List<&2, Sg.Met>}
  {==}

# the lock file of a swept name x beside the directory x: kept, and the
# directory judged
def mo.beside(+x: String, +m: Bool, +sw: {True{} == Staging.sp_swept(x) : Bool}) -> {Sg.meet([Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}}, Sg.Seen{Sg.Utf{x}, Sg.KDir{m}}]) == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}:
  +k = String.append(x, ".lock")
  +lf = {Sg.Seen{Sg.Utf{k}, Sg.KFile{}} : Sg.Seen}
  +d = {Sg.Seen{Sg.Utf{x}, Sg.KDir{m}} : Sg.Seen}
  %Equal.sym(List<&2, Sg.Met>, Sg.meet([lf, d]), Staging.sp_meet([lf, d]), Staging.meet_exact([lf, d])) : {_ == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}
  %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".lock", k), Some{x}, LStg.stg.unsuffix_app(x, ".lock")) : {[Staging.sp_met.file(_, [lf, d]), Staging.sp_met.dir(Staging.sp_swept(x), m)] == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}
  %sw : {[Staging.sp_met.lock(_, LawsBase.text_has_name(x, [lf, d])), Staging.sp_met.dir(_, m)] == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}
  %Equal.sym(Bool, LawsBase.text_same(k, x), False{}, LA.rr.lock_ne(x)) : {[Staging.sp_met.lock(True{}, Bool.or(_, Bool.or(LawsBase.text_same(x, x), False{}))), Sg.MLeftover{}] == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}
  %Equal.sym(Bool, LawsBase.text_same(x, x), True{}, LStg.stg.same_refl(x)) : {[Staging.sp_met.lock(True{}, Bool.or(False{}, Bool.or(_, False{}))), Sg.MLeftover{}] == [Sg.MKeep{}, Sg.MLeftover{}] : List<&2, Sg.Met>}
  {==}

def Staging.meet_minted_orphan(t, l, id, m, full, u):
  +sw = Equal.sym(Bool, Staging.sp_swept(Staging.sp_mint(t, l, id)), True{}, LA.rr.minted(t, l, id, full, u))
  (mo.alone(Staging.sp_mint(t, l, id), sw), mo.beside(Staging.sp_mint(t, l, id), m, sw))
