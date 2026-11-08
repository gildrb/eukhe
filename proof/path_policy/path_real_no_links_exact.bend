# eukhe: the proof of LAW path_real_no_links_exact
#
# PROOF: with no link the lookup finds none, so the fuel never falls and
# the walk is the plain one (`..`: pre.up of path_real_exact).

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy.bend as PathPolicy
import ./path_real_exact.bend as PPathRealExact

def pnl.walk(segs: List<&2, Tl.Seg>, +f: Nat, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(Nil{}, segs, at) : Maybe<&2, Pp.Link>}) -> {Pp.go(1n+f, segs, Nil{}, at, False{}, look) == Pp.Res{PathPolicy.pp_walk_plain(segs, at), False{}} : Pp.Res}:
  match segs:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Tl.Name{+n}:
          %Equal.sym(Maybe<&2, Pp.Link>, look, None{}, lk) : {Pp.go(1n+f, Tl.Name{n} <> rest, Nil{}, at, False{}, _) == Pp.Res{PathPolicy.pp_walk_plain(Tl.Name{n} <> rest, at), False{}} : Pp.Res}
          pnl.walk(rest, f, n <> at, Pp.look.at(Nil{}, rest, n <> at), {==})
        case Tl.Up{}:
          %PPathRealExact.pre.up(at) : {Pp.go(1n+f, rest, Nil{}, Pp.up(at), False{}, Pp.look.at(Nil{}, rest, Pp.up(at))) == Pp.Res{PathPolicy.pp_walk_plain(rest, _), False{}} : Pp.Res}
          pnl.walk(rest, f, Pp.up(at), Pp.look.at(Nil{}, rest, Pp.up(at)), {==})
        case Tl.Here{}:
          pnl.walk(rest, f, at, Pp.look.at(Nil{}, rest, at), {==})

def PathPolicy.path_real_no_links_exact(segs):
  pnl.walk(segs, 39n, Nil{}, Pp.look.at(Nil{}, segs, Nil{}), {==})
