# eukhe: the proof of LAW path_real_names_resolve
#
# PROOF: with no link the lookup finds none, so each name enters the
# directory reached so far: from at, the names xs reach Base's reverse of xs
# onto at (List.reverse.go), by induction on xs; from `/` that is
# List.reverse of xs.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy

def pnr.names(xs: List<&2, Nat>, +f: Nat, +at: List<&2, Nat>, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(Nil{}, PathPolicy.pp_names(xs), at) : Maybe<&2, Pp.Link>}) -> {Pp.go(1n+f, PathPolicy.pp_names(xs), Nil{}, at, False{}, look) == Pp.Res{List.reverse.go(&2, Nat, xs, at), False{}} : Pp.Res}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %Equal.sym(Maybe<&2, Pp.Link>, look, None{}, lk) : {Pp.go(1n+f, Tl.Name{x} <> PathPolicy.pp_names(rest), Nil{}, at, False{}, _) == Pp.Res{List.reverse.go(&2, Nat, rest, x <> at), False{}} : Pp.Res}
      pnr.names(rest, f, x <> at, Pp.look.at(Nil{}, PathPolicy.pp_names(rest), x <> at), {==})

def PathPolicy.path_real_names_resolve(xs):
  pnr.names(xs, 39n, Nil{}, Pp.look.at(Nil{}, PathPolicy.pp_names(xs), Nil{}), {==})
