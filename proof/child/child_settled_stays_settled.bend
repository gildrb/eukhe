# eukhe: the proof of LAW child_settled_stays_settled
# Fate by fate: a withdrawn, a placed and a read submission compute; a
# queued one is not settled, against the premise.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/run.bend as ChildRun
import ../base/logic/logic.bend as LLogicLogic

# the law's claim for the fate f
def pst.Claim(+cfg: Ch.Cfg, +ph: Ch.Ph, +cut: Maybe<&2, Bool>, +open: Bool, +i: Nat, +f: Ch.Fate, +m: Nat) -> Type:
  {ChildRun.chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Deliver{m}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} & ({ChildRun.chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Withdraw{m}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} & ({ChildRun.chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Abort{}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>} & {ChildRun.chr_on(cfg, ph, cut, open, [Ch.Sub{i, f}], Ch.Shut{}) == [Ch.Sub{i, f}] : List<&2, Ch.Sub>}))

def pst.go(f: Ch.Fate, +cfg: Ch.Cfg, +ph: Ch.Ph, +cut: Maybe<&2, Bool>, +open: Bool, +i: Nat, +m: Nat, settled: {ChildRun.chr_settled(f) == True{} : Bool}) -> pst.Claim(cfg, ph, cut, open, i, f, m):
  match f:
    case Ch.Queued{}:
      LLogicLogic.child.pc.absurd(pst.Claim(cfg, ph, cut, open, i, Ch.Queued{}, m), settled)
    case Ch.Withdrawn{}:
      ({==}, ({==}, ({==}, {==})))
    case Ch.Placed{}:
      ({==}, ({==}, ({==}, {==})))
    case Ch.Read{}:
      ({==}, ({==}, ({==}, {==})))

def ChildRun.child_settled_stays_settled(cfg, ph, cut, open, i, f, m, settled):
  pst.go(f, cfg, ph, cut, open, i, m, settled)
