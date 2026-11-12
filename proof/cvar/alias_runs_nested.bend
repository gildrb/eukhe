# eukhe: the proof of LAW alias_runs_nested
# The laws' lookup of a and b is the model's body of each (LE.ex.body_of);
# the table holds an alias, so the run of a leaves a level for the run of
# b. The sets of a's body go onto the accumulator (LE.ex.go_app), b's body
# expands to itself (PRB.pv.flat), and fin puts both in order (rev twice).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as CvarEntry
import ./alias_runs_body.bend as PRB
import ./base/expand.bend as LE

def nx.go(+x: Cv.Alias, +t: List<&2, Cv.Alias>, +a: Nat, +b: Nat, +ps: List<&2, Cv.Cmd>, +qs: List<&2, Cv.Cmd>, fp: {CvarEntry.spec_sets_only(ps) == True{} : Bool}, fq: {CvarEntry.spec_sets_only(qs) == True{} : Bool}, ea: {Cv.body(x <> t, a) == List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}]) : List<&2, Cv.Cmd>}, eb: {Cv.body(x <> t, b) == qs : List<&2, Cv.Cmd>}) -> {Cv.expand([Cv.CRun{a}], x <> t) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}:
  +tb = {x <> t : List<&2, Cv.Alias>}
  +e = List.length(&2, Cv.Alias, t)
  +o = Cv.rev(ps, Nil{})
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(tb, a), List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}]), ea) : {Cv.fin(Cv.expand.go(1n+e, _, tb, Cv.Flat{Nil{}})) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(1n+e, List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}]), tb, Cv.Flat{Nil{}}), Cv.expand.go(1n+e, [Cv.CRun{b}], tb, Cv.Flat{o}), LE.ex.go_app(ps, 1n+e, [Cv.CRun{b}], tb, Nil{}, fp)) : {Cv.fin(_) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}
  %Equal.sym(List<&2, Cv.Cmd>, Cv.body(tb, b), qs, eb) : {Cv.fin(Cv.expand.go(e, _, tb, Cv.Flat{o})) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}
  %Equal.sym(Cv.Exp, Cv.expand.go(e, qs, tb, Cv.Flat{o}), Cv.Flat{Cv.rev(qs, o)}, PRB.pv.flat(qs, e, tb, o, LE.ex.plain(qs, fq))) : {Cv.fin(_) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}
  Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(Cv.rev(qs, o), Nil{}), List.append(&2, Cv.Cmd, ps, qs), Equal.trans(List<&2, Cv.Cmd>, Cv.rev(Cv.rev(qs, o), Nil{}), Cv.rev(o, List.append(&2, Cv.Cmd, qs, Nil{})), List.append(&2, Cv.Cmd, ps, qs), PRB.pv.rev_rev(qs, o, Nil{}), Equal.trans(List<&2, Cv.Cmd>, Cv.rev(o, List.append(&2, Cv.Cmd, qs, Nil{})), List.append(&2, Cv.Cmd, ps, List.append(&2, Cv.Cmd, qs, Nil{})), List.append(&2, Cv.Cmd, ps, qs), PRB.pv.rev_rev(ps, Nil{}, List.append(&2, Cv.Cmd, qs, Nil{})), Equal.cong(List<&2, Cv.Cmd>, List<&2, Cv.Cmd>, z => List.append(&2, Cv.Cmd, ps, z), List.append(&2, Cv.Cmd, qs, Nil{}), qs, PRB.pv.app_nil(qs)))))

def CvarEntry.alias_runs_nested(as, a, b, ps, qs, fp, fq, ha, hb):
  match as:
    case Nil{}:
      LE.ex.none_some(List<&2, Cv.Cmd>, List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}]), {Cv.expand([Cv.CRun{a}], Nil{}) == Cv.Flat{List.append(&2, Cv.Cmd, ps, qs)} : Cv.Exp}, ha)
    case +x <> +t:
      nx.go(x, t, a, b, ps, qs, fp, fq, LE.ex.body_of(x <> t, a, List.append(&2, Cv.Cmd, ps, [Cv.CRun{b}]), ha), LE.ex.body_of(x <> t, b, qs, hb))
