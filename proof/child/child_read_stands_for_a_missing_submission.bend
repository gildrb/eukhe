# eukhe: the proof of LAW child_read_stands_for_a_missing_submission
# No submission: the read one stands alone. A newest submission of
# another id (the premise): the read one stands before it.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun

def prs.go(inbox: List<&2, Ch.Sub>, +cfg: Ch.Cfg, +k: Ch.Report, +n: Nat, +cut: Maybe<&2, Bool>, +open: Bool, missing: {ChildRun.chr_newest_is(inbox, n) == False{} : Bool}) -> {ChildRun.chr_on(cfg, Ch.Owing{k, n}, cut, open, inbox, Ch.Collect{}) == Ch.Sub{n, Ch.Read{}} <> inbox : List<&2, Ch.Sub>}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Ch.Sub{+i, +f}:
          %Equal.sym(Bool, Nat.is_eq(i, n), False{}, missing) : {Ch.read.at(_, n, Ch.Sub{i, f}, rest) == Ch.Sub{n, Ch.Read{}} <> Ch.Sub{i, f} <> rest : List<&2, Ch.Sub>}
          {==}

def ChildRun.child_read_stands_for_a_missing_submission(cfg, k, n, cut, open, inbox, missing):
  prs.go(inbox, cfg, k, n, cut, open, missing)
