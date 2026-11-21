# eukhe: the proof of LAW rec_redirect_row_starts_at_one
#
# PROOF: by cases on the note: after any note but a redirect note the redirects in a row are 0, below a cap of 1 + rd, and the calls are not fresh (the premise), so they get redirect note 1; a redirect note contradicts the premise.

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../laws/run/recover.bend as RunRecover
import ../stop/base/recover.bend as LR

# calls that are not fresh, under the redirect cap with no redirect note before, get redirect note 1
def rr.ran_redo(fresh: Bool, kept: Bool, +m: Nat, +h: Nat, +same: Nat, +last: Nat, r: RnRecovery.Rec, e: {fresh == False{} : Bool}) -> {RnRecovery.rec.ran(fresh, True{}, kept, m, h, 0n, same, last, r) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n, same, last}} : RnRecovery.Dec}:
  match fresh:
    case True{}:
      LR.str.absurd_t({RnRecovery.rec.ran(True{}, True{}, kept, m, h, 0n, same, last, r) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n, same, last}} : RnRecovery.Dec}, e)
    case False{}:
      {==}

def RunRecover.rec_redirect_row_starts_at_one(lg, lk, rd, rp, h, kept, k, row, same, last, rep, other):
  match k:
    case RnRecovery.Free{}:
      rr.ran_redo(RnRecovery.below(RnRecovery.again(same, last, h), rp), kept, RnRecovery.again(same, last, h), h, same, last, RnRecovery.Rec{RnRecovery.Free{}, row, same, last}, rep)
    case RnRecovery.Longs{}:
      rr.ran_redo(RnRecovery.below(RnRecovery.again(same, last, h), rp), kept, RnRecovery.again(same, last, h), h, same, last, RnRecovery.Rec{RnRecovery.Longs{}, row, same, last}, rep)
    case RnRecovery.Leaks{}:
      rr.ran_redo(RnRecovery.below(RnRecovery.again(same, last, h), rp), kept, RnRecovery.again(same, last, h), h, same, last, RnRecovery.Rec{RnRecovery.Leaks{}, row, same, last}, rep)
    case RnRecovery.Loops{}:
      LR.str.absurd_t({RnRecovery.Rec.step(RnRecovery.RCfg{lg, lk, 1n+rd, rp}, RnRecovery.Ran{h, kept}, RnRecovery.Rec{RnRecovery.Loops{}, row, same, last}) == RnRecovery.Dec{RnRecovery.Redo{}, RnRecovery.Rec{RnRecovery.Loops{}, 1n, same, last}} : RnRecovery.Dec}, other)
    case RnRecovery.Empties{}:
      rr.ran_redo(RnRecovery.below(RnRecovery.again(same, last, h), rp), kept, RnRecovery.again(same, last, h), h, same, last, RnRecovery.Rec{RnRecovery.Empties{}, row, same, last}, rep)
