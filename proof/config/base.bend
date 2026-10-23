# eukhe: lemmas the proofs of area config share

import Base
import ../../bend/config.bend as Cf
import ../base/bool/misc.bend as LBoolMisc

# ---- config ----

# proof_config: lemmas for LAWS.bend section config over bend/config.bend (and
# bend/default_model.bend, proved in PROOF.bend section default_model).
#
# Writes. A broken read writes nothing by definition. A set puts the new
# entry first and drops the old entries of its key; a delete drops them.
# Neither changes the first entry of another key (`pcf.del_keeps`, an
# induction on the document).
#
# Leaves. Each leaf adds its path to the applied list when it is good,
# and to the reported list when it is not; the proofs follow the skill
# loading proofs of PROOF.bend section progress_report, whose logic lemmas
# they reuse.
#
# Trust and entries. An untrusted project adds only its preferences; a
# key no preference names is looked up past them in the global document
# (an induction on the items). A merged map puts the project entries
# first, so a name the project has is found there, and another name is
# found in the global map (an induction on the project entries).
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

# Writes
# ------

# a false pick is the later value
def pcf.pick_false(b: Bool, v: Nat, +later: Maybe<&2, Nat>, h: {b == False{} : Bool}) -> {Cf.pick(b, v, later) == later : Maybe<&2, Nat>}:
  match b:
    case True{}:
      LBoolMisc.ppr.absurd({Cf.pick(True{}, v, later) == later : Maybe<&2, Nat>}, h)
    case False{}:
      {==}
