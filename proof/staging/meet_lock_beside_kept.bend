# eukhe: the proof of LAW meet_lock_beside_kept

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg

def lk.lock(a: Bool) -> {LA.rr.m.lock(a, True{}) == Sg.MKeep{} : Sg.Met}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the lock file of x, where an entry has the name x: kept
def lk.here(+x: String, +all: List<&2, Sg.Seen>, there: {LawsBase.text_has_name(x, all) == True{} : Bool}) -> {LA.rr.m(Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}}, all) == Sg.MKeep{} : Sg.Met}:
  %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".lock", String.append(x, ".lock")), Some{x}, LStg.stg.unsuffix_app(x, ".lock")) : {LA.rr.m.file(_, all) == Sg.MKeep{} : Sg.Met}
  %Equal.sym(Bool, LawsBase.text_has_name(x, all), True{}, there) : {LA.rr.m.lock(Staging.sp_swept(x), _) == Sg.MKeep{} : Sg.Met}
  lk.lock(Staging.sp_swept(x))

def Staging.meet_lock_beside_kept(pre, post, t, l, id, there):
  +x = Staging.sp_mint(t, l, id)
  +lf = {Sg.Seen{Sg.Utf{String.append(x, ".lock")}, Sg.KFile{}} : Sg.Seen}
  LA.mm.found(pre, lf, post, Sg.MKeep{}, lk.here(x, List.append(&2, Sg.Seen, pre, lf <> post), there))
