# eukhe: the proof of LAW once_recover_dark_repeats_safe
#
# PROOF: by the policy: `never`, and a keyed effect whose target has no
# declaration, are not repeat-safe (the premise is refuted); `safe`
# computes to a launch; a keyed effect whose target declares lasting is
# sent again while fewer than cap (LA.ob.keyed_launch).

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ./base.bend as LA

def Once.once_recover_dark_repeats_safe(again, p, safe):
  match p:
    case O.Never{}:
      LA.ob.false_true({O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Never{}) == O.Launch{} : O.Verdict}, safe)
    case O.Safe{}:
      {==}
    case O.Keyed{d, cap}:
      match d:
        case O.Undeclared{}:
          LA.ob.false_true({O.recover(O.Running{again}, O.Dark{}, O.Resume{}, O.Keyed{O.Undeclared{}, cap}) == O.Launch{} : O.Verdict}, safe)
        case O.Lasting{}:
          LA.ob.keyed_launch(cap, again, safe)
