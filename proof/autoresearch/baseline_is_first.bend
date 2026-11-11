# eukhe: the proof of LAW baseline_is_first

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../spec/autoresearch/segment.bend as SG
import ../../laws/autoresearch/history.bend as AutoresearchHistory

# a row that is not flagged: the code keeps its metric exactly when the
# spec does
def BaselineIsFirst.kst(b: Bool, st: Maybe<&2, ArS.Status>, -m: Maybe<&2, ArD.Dec>) -> {ArS.kept.of(Bool.and(b, Bool.and(ArS.kept.st(st), True{})), m) == SG.kept.st(b, st, m) : Maybe<&2, ArD.Dec>}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Keep{}:
              {==}
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}

# a flagged row: the code keeps nothing
def BaselineIsFirst.kfl(b: Bool, st: Maybe<&2, ArS.Status>, -m: Maybe<&2, ArD.Dec>) -> {ArS.kept.of(Bool.and(b, Bool.and(ArS.kept.st(st), False{})), m) == None{} : Maybe<&2, ArD.Dec>}:
  match b:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Keep{}:
              {==}
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}

# the code's kept metric of a row is the spec's
def BaselineIsFirst.kept(r: ArS.Row, +seg: Nat) -> {ArS.kept(r, seg) == SG.kept(r, seg) : Maybe<&2, ArD.Dec>}:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      match fl:
        case True{}:
          BaselineIsFirst.kfl(Nat.is_eq(sg, seg), st, m)
        case False{}:
          BaselineIsFirst.kst(Nat.is_eq(sg, seg), st, m)

# the code's pick of the first metric is the spec's
def BaselineIsFirst.or(k: Maybe<&2, ArD.Dec>, -f: Maybe<&2, ArD.Dec>) -> {ArS.first.at(k, f) == SG.first_kept.or(k, f) : Maybe<&2, ArD.Dec>}:
  match k:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the code's first kept metric of a segment is the spec's
def BaselineIsFirst.go(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArS.first(rs, seg) == SG.first_kept(rs, seg) : Maybe<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      %BaselineIsFirst.kept(r, seg) : {ArS.first.at(ArS.kept(r, seg), ArS.first(t, seg)) == SG.first_kept.or(_, SG.first_kept(t, seg)) : Maybe<&2, ArD.Dec>}
      %BaselineIsFirst.go(t, seg) : {ArS.first.at(ArS.kept(r, seg), ArS.first(t, seg)) == SG.first_kept.or(ArS.kept(r, seg), _) : Maybe<&2, ArD.Dec>}
      BaselineIsFirst.or(ArS.kept(r, seg), ArS.first(t, seg))

def AutoresearchHistory.baseline_is_first(s):
  match s:
    case ArS.St{c, +seg, mode, runs, pend}:
      BaselineIsFirst.go(runs, seg)
