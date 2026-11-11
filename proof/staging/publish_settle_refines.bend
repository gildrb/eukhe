# eukhe: the proof of LAW publish_settle_refines

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

# the verdict of a rename is the model's publish, for either answer of the
# kernel
def pr.go(+s: Nat, +t: Nat, +es: List<&2, Sg.Entry>, b: Bool) -> {Staging.sp_moved(Sg.settle(b)) == Sg.Pub.ok(Sg.publish.go(s, t, b, es)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def Staging.publish_settle_refines(s, t, es):
  pr.go(s, t, es, Sg.has(t, es))
