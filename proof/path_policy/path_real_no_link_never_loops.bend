# eukhe: the proof of LAW path_real_no_link_never_loops
#
# PROOF: with no link the lookup finds none, so the fuel never falls, no
# link is followed and the loop flag stays as it started (False), by
# induction on the segments.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy

def pnl.loop(segs: List<&2, Tl.Seg>, +f: Nat, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(Nil{}, segs, at) : Maybe<&2, Pp.Link>}) -> {Pp.Res.looped(Pp.go(1n+f, segs, Nil{}, at, False{}, look)) == False{} : Bool}:
  match segs:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Tl.Name{+n}:
          %Equal.sym(Maybe<&2, Pp.Link>, look, None{}, lk) : {Pp.Res.looped(Pp.go(1n+f, Tl.Name{n} <> rest, Nil{}, at, False{}, _)) == False{} : Bool}
          pnl.loop(rest, f, n <> at, Pp.look.at(Nil{}, rest, n <> at), {==})
        case Tl.Up{}:
          pnl.loop(rest, f, Pp.up(at), Pp.look.at(Nil{}, rest, Pp.up(at)), {==})
        case Tl.Here{}:
          pnl.loop(rest, f, at, Pp.look.at(Nil{}, rest, at), {==})

def PathPolicy.path_real_no_link_never_loops(segs):
  pnl.loop(segs, 39n, Nil{}, Pp.look.at(Nil{}, segs, Nil{}), {==})
