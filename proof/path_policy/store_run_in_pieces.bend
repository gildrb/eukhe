# eukhe: the proof of LAW store_run_in_pieces
#
# PROOF: by induction on the first history: its first write steps the
# store, then both sides run the rest from that store.

import Base
import ../../bend/path_policy.bend as Pp
import ../../laws/path_policy/gate.bend as PathPolicyGate

def psp.pieces(es: List<&2, Pp.Put>, +fs: List<&2, Pp.Put>, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +cs: List<&2, Pp.Cell>) -> {Pp.run(List.append(&2, Pp.Put, es, fs), pol, ls, auto, cs) == Pp.run(fs, pol, ls, auto, Pp.run(es, pol, ls, auto, cs)) : List<&2, Pp.Cell>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      psp.pieces(rest, fs, pol, ls, auto, Pp.step(pol, ls, auto, cs, e))

def PathPolicyGate.store_run_in_pieces(es, fs, pol, ls, auto, cs):
  psp.pieces(es, fs, pol, ls, auto, cs)
