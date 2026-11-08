# eukhe: the proof of LAW seen_entry_malformed_unless_seen
#
# PROOF: the seen runs' decoder reads only spelled runs that fit, the rest
# after them untouched (exact.bend); when it reads none the entry answers
# the seen runs' error, which the premise excludes.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../bend/wire.bend as Wr
import ../../laws/doc_seen.bend as DocSeen
import ../wire/base/spell.bend as LAWireSpell
import ./seen_entry_reads_only_requests/exact.bend as Fsx

def smus_Ex(s: String) -> Type:
  &ivs: List<&2, Ds.Iv> -> &t: String -> ({s == DocSeen.seen.spell_seen(ivs, t) : String} & {DocSeen.seen.SeenFits(ivs) == True{} : Bool})

def smus_main(-s: String, d: Wr.Dec<List<&2, Ds.Iv>>, pd: Fsx.fsx_pivs(s, d),
  other: {String.eq(Fds.run.seen(d), Wr.err("doc_seen: malformed seen runs")) == False{} : Bool}) -> smus_Ex(s):
  match d:
    case Wr.Got{+ivs, +t}:
      (ivs, (t, pd))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(smus_Ex(s), other)

def DocSeen.seen_entry_malformed_unless_seen(s, other):
  smus_main(s, Wr.get_list(~Ds.Iv, ~Fds.get_iv, s), Fsx.fsx_ivs(s), other)
