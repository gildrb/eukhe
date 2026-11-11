# eukhe: the proof of LAW roster_step_spec
# A quit's drop is the spec's (by induction on the dynamic tools, with
# the head test as a parameter); every other event computes to the same
# session.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# the head y of the dynamic tools, with test h: the drop keeps it as the
# spec does
def prs.keep(h: Bool, y: Nat, +rest: List<&2, Nat>, +t: Nat, ih: {Tl.drop(rest, t) == Tools.tr_drop(rest, t) : List<&2, Nat>}) -> {Tl.drop.go(y <> rest, t, h) == Tools.tr_keep(h, y, Tools.tr_drop(rest, t)) : List<&2, Nat>}:
  match h:
    case True{}:
      ih
    case False{}:
      %ih : {y <> Tl.drop(rest, t) == y <> _ : List<&2, Nat>}
      {==}

def prs.drop(xs: List<&2, Nat>, +t: Nat) -> {Tl.drop(xs, t) == Tools.tr_drop(xs, t) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      prs.keep(Nat.is_eq(y, t), y, rest, t, prs.drop(rest, t))

def Tools.roster_step_spec(s, e):
  match s:
    case Tl.Sess{+r, d, x}:
      match e:
        case Tl.Join{t}:
          {==}
        case Tl.Quit{+t}:
          %prs.drop(d, t) : {Tl.Sess{r, Tl.drop(d, t), x} == Tl.Sess{r, _, x} : Tl.Sess}
          {==}
        case Tl.Turn{}:
          {==}
