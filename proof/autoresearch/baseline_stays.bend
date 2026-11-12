# eukhe: the proof of LAW baseline_stays: an accepted step other than a
# flag only appends rows (LAW rows_kept), and rows appended after a kept
# one leave the first kept metric

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../laws/autoresearch/model.bend as ArM
import ../../laws/autoresearch/history.bend as AutoresearchHistory
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/events.bend as AE
import ./rows_kept.bend as PRowsKept

def bst.base(s: ArS.St) -> {ArS.St.baseline(s) == ArS.first(ArM.ar_runs(s), ArM.ar_seg(s)) : Maybe<&2, ArD.Dec>}:
  match s:
    case ArS.St{c, seg, mode, runs, pend}:
      {==}

def bst.at(k: Maybe<&2, ArD.Dec>, +f1: Maybe<&2, ArD.Dec>, -f2: Maybe<&2, ArD.Dec>, +x: ArD.Dec, h: {ArS.first.at(k, f1) == Some{x} : Maybe<&2, ArD.Dec>}, ih: {f1 == Some{x} : Maybe<&2, ArD.Dec>} -> {f2 == Some{x} : Maybe<&2, ArD.Dec>}) -> {ArS.first.at(k, f2) == Some{x} : Maybe<&2, ArD.Dec>}:
  match k:
    case None{}:
      ih(h)
    case Some{y}:
      h

# rows appended after a kept one leave the first kept metric
def bst.app(rs: List<&2, ArS.Row>, +ys: List<&2, ArS.Row>, +seg: Nat, +x: ArD.Dec, h: {ArS.first(rs, seg) == Some{x} : Maybe<&2, ArD.Dec>}) -> {ArS.first(List.append(&2, ArS.Row, rs, ys), seg) == Some{x} : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      AE.ev.none_some(ArD.Dec, {ArS.first(ys, seg) == Some{x} : Maybe<&2, ArD.Dec>}, x, h)
    case +r <> +t:
      bst.at(ArS.kept(r, seg), ArS.first(t, seg), ArS.first(List.append(&2, ArS.Row, t, ys), seg), x, h, hh => bst.app(t, ys, seg, x, hh))

def bst.of(+s: ArS.St, +s2: ArS.St, +x: ArD.Dec, same: {ArM.ar_seg(s2) == ArM.ar_seg(s) : Nat}, was: {ArS.St.baseline(s) == Some{x} : Maybe<&2, ArD.Dec>}, k: PRowsKept.rk.R(s, s2)) -> {ArS.St.baseline(s2) == Some{x} : Maybe<&2, ArD.Dec>}:
  (ys, hr) = k
  +h0 = Equal.trans(Maybe<&2, ArD.Dec>, ArS.first(ArM.ar_runs(s), ArM.ar_seg(s)), ArS.St.baseline(s), Some{x}, Equal.sym(Maybe<&2, ArD.Dec>, ArS.St.baseline(s), ArS.first(ArM.ar_runs(s), ArM.ar_seg(s)), bst.base(s)), was)
  +h1 = bst.app(ArM.ar_runs(s), ys, ArM.ar_seg(s), x, h0)
  +e1 = Equal.cong(List<&2, ArS.Row>, Maybe<&2, ArD.Dec>, rs => ArS.first(rs, ArM.ar_seg(s2)), ArM.ar_runs(s2), List.append(&2, ArS.Row, ArM.ar_runs(s), ys), hr)
  +e2 = Equal.cong(Nat, Maybe<&2, ArD.Dec>, g => ArS.first(List.append(&2, ArS.Row, ArM.ar_runs(s), ys), g), ArM.ar_seg(s2), ArM.ar_seg(s), same)
  Equal.trans(Maybe<&2, ArD.Dec>, ArS.St.baseline(s2), ArS.first(ArM.ar_runs(s2), ArM.ar_seg(s2)), Some{x}, bst.base(s2), Equal.trans(Maybe<&2, ArD.Dec>, ArS.first(ArM.ar_runs(s2), ArM.ar_seg(s2)), ArS.first(List.append(&2, ArS.Row, ArM.ar_runs(s), ys), ArM.ar_seg(s2)), Some{x}, e1, Equal.trans(Maybe<&2, ArD.Dec>, ArS.first(List.append(&2, ArS.Row, ArM.ar_runs(s), ys), ArM.ar_seg(s2)), ArS.first(List.append(&2, ArS.Row, ArM.ar_runs(s), ys), ArM.ar_seg(s)), Some{x}, e2, h1)))

def AutoresearchHistory.baseline_stays(s, e, s2, eff, stop, x, ok, nf, same, was):
  bst.of(s, s2, x, same, was, AutoresearchEvents.rows_kept(s, e, s2, eff, stop, ok, nf))
