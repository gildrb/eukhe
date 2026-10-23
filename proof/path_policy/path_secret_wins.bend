# eukhe: the proof of LAW path_secret_wins

import Base
import ../../bend/tools.bend as Tl
import ../../bend/path_policy.bend as Pp
import ../../LAWS.bend as Laws

# 2. The class
# ------------

def pp.secret_res(+pol: Pp.Pol, r: Pp.Res, hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(r)) == True{} : Bool}) -> {Pp.class_res(pol, r) == Pp.Secret{} : Pp.Cls}:
  match r:
    case Pp.Res{+at, looped}:
      %Equal.sym(Bool, Pp.any_under(Pp.Pol.secret(pol), at), True{}, hit) : {Pp.demote(Pp.cls.pick(_, Pp.protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))), looped) == Pp.Secret{} : Pp.Cls}
      {==}

def pp.path_secret_wins(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}) -> {Pp.class(pol, ls, segs) == Pp.Secret{} : Pp.Cls}:
  pp.secret_res(pol, Pp.real(ls, segs), hit)

def Laws.path_secret_wins(pol, ls, segs, hit):
  pp.path_secret_wins(pol, ls, segs, hit)
