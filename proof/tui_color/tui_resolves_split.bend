# eukhe: the proof of LAW tui_resolves_split
# No roles: the fold's base. Roles xs then ys: induction on xs, the head
# role's test and-ed in front (rsp.assoc).

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

# a and (b and c) is (a and b) and c
def rsp.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def rsp.cat(+p: List<&2, Maybe<&2, TFile.Val>>, xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {TC.resolves(p, TuiColor.cat(Nat, xs, ys)) == Bool.and(TC.resolves(p, xs), TC.resolves(p, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +f = TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r))
      %Equal.sym(Bool, TC.resolves(p, TuiColor.cat(Nat, rest, ys)), Bool.and(TC.resolves(p, rest), TC.resolves(p, ys)), rsp.cat(p, rest, ys)) : {Bool.and(f, _) == Bool.and(Bool.and(f, TC.resolves(p, rest)), TC.resolves(p, ys)) : Bool}
      rsp.assoc(f, TC.resolves(p, rest), TC.resolves(p, ys))

def TuiColor.tui_resolves_split(p, xs, ys):
  ({==}, rsp.cat(p, xs, ys))
