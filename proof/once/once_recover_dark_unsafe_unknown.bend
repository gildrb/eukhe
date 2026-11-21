# eukhe: the proof of LAW once_recover_dark_unsafe_unknown
#
# PROOF: by the policy: `never`, and a keyed effect whose target has no
# declaration, compute to an interrupt; `safe` is repeat-safe (the
# premise is refuted); a keyed effect whose target declares lasting, sent
# again cap times or more, is journaled unknown (LA.ob.keyed_stop).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_recover_dark_unsafe_unknown(again, p, unsafe):
  match p:
    case O.Never{}:
      {==}
    case O.Safe{}:
      LA.ob.true_false({O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Safe{}) == O.Interrupt{} : O.Verdict}, unsafe)
    case O.Keyed{d, cap}:
      match d:
        case O.Undeclared{}:
          {==}
        case O.Lasting{}:
          LA.ob.keyed_stop(cap, again, unsafe)
