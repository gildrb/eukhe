# eukhe: the proof of LAW stop_cut_unknown_window_never_kept
#
# PROOF: the entry's window test reads an unknown window (0) as spent before it reads the catalog cap or the tokens, so each claim computes once the text and the compaction fact are split (stu.kept).

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../laws/stop/cut.bend as StopCut

# at an unknown window, no pick keeps the reply: with no text LengthStop
# continues, with text it continues or drops
def stu.kept(t: Bool, -b: Bool, -p: Bool, -ca: Nat, -pr: Nat, -o: Nat, cu: Bool) -> {StopCut.kept(S.walk(FS.facts(True{}, t, b, p, 0n, ca, pr, o, cu))) == False{} : Bool}:
  match t:
    case True{}:
      match cu:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def StopCut.stop_cut_unknown_window_never_kept(t, b, p, ca, pr, o, cu):
  (stu.kept(t, b, p, ca, pr, o, cu), ({==}, {==}))
