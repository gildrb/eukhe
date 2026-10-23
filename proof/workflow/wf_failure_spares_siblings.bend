# eukhe: the proof of LAW wf_failure_spares_siblings

import Base
import ../../bend/workflow.bend as W
import ../../LAWS.bend as Laws

def pw.spares(xs: List<&2, W.Out>, +ys: List<&2, W.Out>) -> {W.results(W.cat(xs, W.Failed{} <> ys)) == W.rcat(W.results(xs), None{} <> W.results(ys)) : List<&2, Maybe<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pw.spares(rest, ys) : {W.result(x) <> W.results(W.cat(rest, W.Failed{} <> ys)) == W.result(x) <> _ : List<&2, Maybe<&2, Nat>>}
      {==}

def Laws.wf_failure_spares_siblings(xs, ys):
  pw.spares(xs, ys)
