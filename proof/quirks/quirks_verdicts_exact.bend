# eukhe: the proof of LAW quirks_verdicts_exact
# By induction on the rules: each verdict's known test and first later
# clash are the spec's (proof/quirks/base.bend qp.mem, qp.dir, qp.partner).

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def qv.verdict(k: Bool, c: Maybe<&2, Nat>) -> {If.verdict(k, c) == Quirks.qs_verdict(k, c) : If.Verdict}:
  match k:
    case False{}:
      {==}
    case True{}:
      match c:
        case None{}:
          {==}
        case Some{j}:
          {==}

def qv.go(rs: List<&2, If.Rule>, +known: List<&2, Nat>, +i: Nat) -> {If.verdicts.go(rs, known, i) == Quirks.qs_verdicts(rs, known, i) : List<&2, If.Verdict>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %qv.go(rest, known, 1n+i) : {If.verdicts.go(r <> rest, known, i) == Quirks.qs_verdict(Quirks.qs_mem(known, Quirks.qs_dir(r)), Quirks.qs_partner(rest, r, 1n+i)) <> _ : List<&2, If.Verdict>}
      %QP.qp.partner(rest, r, 1n+i) : {If.verdicts.go(r <> rest, known, i) == Quirks.qs_verdict(Quirks.qs_mem(known, Quirks.qs_dir(r)), _) <> If.verdicts.go(rest, known, 1n+i) : List<&2, If.Verdict>}
      %QP.qp.dir(r) : {If.verdicts.go(r <> rest, known, i) == Quirks.qs_verdict(Quirks.qs_mem(known, _), If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) <> If.verdicts.go(rest, known, 1n+i) : List<&2, If.Verdict>}
      %QP.qp.mem(known, If.Rule.dir(r)) : {If.verdicts.go(r <> rest, known, i) == Quirks.qs_verdict(_, If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) <> If.verdicts.go(rest, known, 1n+i) : List<&2, If.Verdict>}
      %qv.verdict(If.elem(known, If.Rule.dir(r)), If.clash.go(rest, r, 1n+i, If.clash.head(r, rest))) : {If.verdicts.go(r <> rest, known, i) == _ <> If.verdicts.go(rest, known, 1n+i) : List<&2, If.Verdict>}
      {==}

def Quirks.quirks_verdicts_exact(known, rs):
  qv.go(rs, known, 0n)
