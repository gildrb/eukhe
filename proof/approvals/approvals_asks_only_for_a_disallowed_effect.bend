# eukhe: the proof of LAW approvals_asks_only_for_a_disallowed_effect
# PROOF: a step within the auto set is Unasked, never Routed; a step not
# within it has an effect the auto set does not run unasked: the first
# effect whose test fails (LG.gd.some, by induction on the effects).

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/approvals/route.bend as Approvals
import ./base/gate.bend as LG

# routed or not
def pq.routed(g: Am.Gated) -> Bool:
  match g:
    case Am.Unasked{}:
      False{}
    case Am.Routed{o, f}:
      True{}

def pq.main(+auto: List<&2, Nat>, +es: List<&2, Nat>, +ds: List<&2, Am.Desk>, +o: Am.Out, +f: Am.Fate, w: Bool, ew: {Tl.within(es, auto) == w : Bool}, asked: {Am.gate.by(w, es, ds) == Am.Routed{o, f} : Am.Gated}) -> Approvals.gt_has_disallowed(auto, es):
  match w:
    case True{}:
      LG.gd.absurd(Approvals.gt_has_disallowed(auto, es), Equal.cong(Am.Gated, Bool, g => pq.routed(g), Am.Unasked{}, Am.Routed{o, f}, asked))
    case False{}:
      LG.gd.some(es, auto, ew)

def Approvals.approvals_asks_only_for_a_disallowed_effect(auto, es, ds, o, f, asked):
  pq.main(auto, es, ds, o, f, Tl.within(es, auto), {==}, asked)
