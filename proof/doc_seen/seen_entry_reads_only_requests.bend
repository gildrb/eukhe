# eukhe: the proof of LAW seen_entry_reads_only_requests
#
# PROOF: follow the entry's decoders on s: each one that reads saw exactly
# the laws' spelling of what it read, which fits (exact.bend); a decoder
# that reads nothing, or input left over, answers the error form, which the
# premise excludes.

import Base
import ../../bend/doc_seen.bend as Ds
import ../../bend/ffi_doc_seen.bend as Fds
import ../../bend/wire.bend as Wr
import ../../laws/doc_seen.bend as DocSeen
import ../../laws/base.bend as LawsBase
import ../wire/base/spell.bend as LAWireSpell
import ./seen_entry_reads_only_requests/exact.bend as Fsx

# the law's claim on s: s spells a request whose numbers fit
def sro_Ex(s: String) -> Type:
  &ivs: List<&2, Ds.Iv> -> &ats: List<&2, Ds.At> -> ({s == DocSeen.seen.spell_req(ivs, ats, "") : String} & {DocSeen.seen.WireFits(ivs, ats) == True{} : Bool})

# nothing is left after the anchors
def sro_done(+r: String, -s: String, +ivs: List<&2, Ds.Iv>, -t: String,
  es: {s == DocSeen.seen.spell_seen(ivs, t) : String}, fs: {DocSeen.seen.SeenFits(ivs) == True{} : Bool},
  +ats: List<&2, Ds.At>, ea: {t == DocSeen.seen.spell_ats(ats, r) : String}, fa: {DocSeen.seen.AnchorsFit(ats) == True{} : Bool},
  h: {LawsBase.wire_opens_err(Fds.run.done(ivs, ats, Wr.end(r))) == False{} : Bool}) -> sro_Ex(s):
  match r:
    case SNil{}:
      (ivs, (ats, (Equal.trans(String, s, DocSeen.seen.spell_seen(ivs, t), DocSeen.seen.spell_seen(ivs, DocSeen.seen.spell_ats(ats, "")), es,
          Equal.cong(String, String, z => DocSeen.seen.spell_seen(ivs, z), t, DocSeen.seen.spell_ats(ats, ""), ea)),
        LAWireSpell.ws_and_tt(DocSeen.seen.SeenFits(ivs), DocSeen.seen.AnchorsFit(ats), fs, fa))))
    case SCon{c, u}:
      LAWireSpell.ws_absurd(sro_Ex(s), h)

# the anchors after the seen runs
def sro_ats(-s: String, +ivs: List<&2, Ds.Iv>, -t: String, es: {s == DocSeen.seen.spell_seen(ivs, t) : String},
  fs: {DocSeen.seen.SeenFits(ivs) == True{} : Bool}, d: Wr.Dec<List<&2, Ds.At>>, pd: Fsx.fsx_pats(t, d),
  h: {LawsBase.wire_opens_err(Fds.run.ats(ivs, d)) == False{} : Bool}) -> sro_Ex(s):
  match d:
    case Wr.Got{+ats, +r}:
      (ea, fa) = pd
      sro_done(r, s, ivs, t, es, fs, ats, ea, fa, h)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(sro_Ex(s), h)

# the seen runs first
def sro_seen(+s: String, d: Wr.Dec<List<&2, Ds.Iv>>, pd: Fsx.fsx_pivs(s, d),
  h: {LawsBase.wire_opens_err(Fds.run.seen(d)) == False{} : Bool}) -> sro_Ex(s):
  match d:
    case Wr.Got{+ivs, +t}:
      (es, fs) = pd
      sro_ats(s, ivs, t, es, fs, Wr.get_list(~Ds.At, ~Fds.get_at, t), Fsx.fsx_ats(t), h)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(sro_Ex(s), h)

def DocSeen.seen_entry_reads_only_requests(s, ok):
  sro_seen(s, Wr.get_list(~Ds.Iv, ~Fds.get_iv, s), Fsx.fsx_ivs(s), ok)
