# eukhe: the proof of LAW call_lift_rename_moves
#
# PROOF: some argument is named from (x: cll.has_at), none is named to (the premise, through has == not lacks: cll.has_is), so the op renames; the code's rename renames x in place and keeps every other argument (cll.rename_at, induction on pre: an argument before x is named otherwise, the premise).

import Base
import ../../bend/call_lift.bend as Cl
import ../../laws/call_lift.bend as CallLift
import ./base/args.bend as LCallLiftArgs

def CallLift.call_lift_rename_moves(pre, x, post, from, to, rs, named, before, free):
  +nm = named
  %Equal.sym(Bool, Cl.has(List.append(&2, Cl.Arg, pre, x <> post), from), True{}, LCallLiftArgs.cll.has_at(pre, x, post, from, nm)) : {Cl.apply_op.rename(_, Cl.has(List.append(&2, Cl.Arg, pre, x <> post), to), from, to, List.append(&2, Cl.Arg, pre, x <> post), rs) == Cl.St{List.append(&2, Cl.Arg, pre, CallLift.renamed(x, to) <> post), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} : Cl.St}
  %Equal.sym(Bool, Cl.has(List.append(&2, Cl.Arg, pre, x <> post), to), False{}, LCallLiftArgs.cll.has_is(List.append(&2, Cl.Arg, pre, x <> post), to, True{}, free)) : {Cl.apply_op.rename(True{}, _, from, to, List.append(&2, Cl.Arg, pre, x <> post), rs) == Cl.St{List.append(&2, Cl.Arg, pre, CallLift.renamed(x, to) <> post), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} : Cl.St}
  %Equal.sym(List<&2, Cl.Arg>, Cl.rename(List.append(&2, Cl.Arg, pre, x <> post), from, to), List.append(&2, Cl.Arg, pre, CallLift.renamed(x, to) <> post), LCallLiftArgs.cll.rename_at(pre, x, post, from, to, nm, before)) : {Cl.St{_, List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} == Cl.St{List.append(&2, Cl.Arg, pre, CallLift.renamed(x, to) <> post), List.append(&2, Cl.Receipt, rs, [Cl.Renamed{from, to}])} : Cl.St}
  {==}
