# eukhe: a lemma the start laws of area autoresearch share: after any
# history, the code's count of started runs is the number of starts the
# history had accepted (from the proof of run_conservation)

import Base
import ../../../bend/autoresearch/state.bend as ArS
import ../../../laws/autoresearch/model.bend as ArM
import ../../../laws/autoresearch/history.bend as ArH
import ./step.bend as AS
import ../run_conservation.bend as PRC

def st.k(+evs: List<&2, ArS.Ev>) -> {ArS.St.started(ArM.ar_run(evs)) == ArH.ar_starts(evs) : Nat}:
  Equal.trans(Nat, ArS.St.started(ArM.ar_run(evs)), Nat.add(ArH.ar_starts(evs), 0n), ArH.ar_starts(evs), PRC.ah.g_k(evs, ArS.St.empty(), PRC.ah.rc_go(evs, ArS.St.empty(), {==})), AS.as.add_zero(ArH.ar_starts(evs)))
