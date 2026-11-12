# eukhe: the proof of LAW launcher_commit_stops_closed
#
# Every gate of `la_closed` is closed (induction), so the commit stops;
# the runs it counts (`busy_count`) are the runs of bs that the filter
# keeps (induction on bs).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lcs.closed(bs: List<&2, Bool>) -> {La.all_closed(Launcher.la_closed(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> t:
      lcs.closed(t)

def lcs.busy(bs: List<&2, Bool>) -> {La.busy_count(Launcher.la_closed(bs)) == List.length(&2, Bool, List.filter(~Bool, ~Launcher.la_id, bs)) : Nat}:
  match bs:
    case Nil{}:
      {==}
    case b <> t:
      match b:
        case True{}:
          Equal.cong(Nat, Nat, n => 1n+n, La.busy_count(Launcher.la_closed(t)), List.length(&2, Bool, List.filter(~Bool, ~Launcher.la_id, t)), lcs.busy(t))
        case False{}:
          lcs.busy(t)

def Launcher.launcher_commit_stops_closed(bs, a):
  %Equal.sym(Bool, La.all_closed(Launcher.la_closed(bs)), True{}, lcs.closed(bs)) : {La.commit.put(_, Launcher.la_closed(bs), a) == La.St{Launcher.la_closed(bs), Nat.add(List.length(&2, Bool, List.filter(~Bool, ~Launcher.la_id, bs)), a), True{}} : La.St}
  Equal.cong(Nat, La.St, n => La.St{Launcher.la_closed(bs), Nat.add(n, a), True{}}, La.busy_count(Launcher.la_closed(bs)), List.length(&2, Bool, List.filter(~Bool, ~Launcher.la_id, bs)), lcs.busy(bs))
