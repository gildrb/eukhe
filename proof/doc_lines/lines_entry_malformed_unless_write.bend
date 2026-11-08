# eukhe: the proof of LAW lines_entry_malformed_unless_write
#
# PROOF: `W` is no plan (its runs do not read), so the entry reads two
# projections, and the projection's decoder reads only a spelled
# projection that fits (fdx_proj); when either reads none the entry answers
# the projection's error, which the premise excludes.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../base/ffi_doc_lines/exact.bend as Fdx

def lmw_Ex(t: String) -> Type:
  &p: Dl.Proj -> &q: Dl.Proj -> &rest: String -> ({t == LawsBase.proj_spell(p, LawsBase.proj_spell(q, rest)) : String} & {Bool.and(LawsBase.proj_fits(p), LawsBase.proj_fits(q)) == True{} : Bool})

# the second projection
def lmw_next(-t: String, +p: Dl.Proj, -s2: String, ep: {t == LawsBase.proj_spell(p, s2) : String},
  fp: {LawsBase.proj_fits(p) == True{} : Bool}, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(s2, d),
  other: {String.eq(Fdl.write.next(p, d), Wr.err("doc_lines: malformed projection")) == False{} : Bool}) -> lmw_Ex(t):
  match d:
    case Wr.Got{+q, +r}:
      (eq, fq) = pd
      (p, (q, (r, (Equal.trans(String, t, LawsBase.proj_spell(p, s2), LawsBase.proj_spell(p, LawsBase.proj_spell(q, r)), ep,
          Equal.cong(String, String, z => LawsBase.proj_spell(p, z), s2, LawsBase.proj_spell(q, r), eq)),
        Fdx.fdx_and(LawsBase.proj_fits(p), LawsBase.proj_fits(q), fp, fq)))))
    case Wr.Bad{}:
      Fdx.fdx_absurd(lmw_Ex(t), other)

# the first projection
def lmw_main(-t: String, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(t, d),
  other: {String.eq(Fdl.write.run(d), Wr.err("doc_lines: malformed projection")) == False{} : Bool}) -> lmw_Ex(t):
  match d:
    case Wr.Got{+p, +s2}:
      (ep, fp) = pd
      lmw_next(t, p, s2, ep, fp, Fdl.get_proj(s2), Fdx.fdx_proj(s2), other)
    case Wr.Bad{}:
      Fdx.fdx_absurd(lmw_Ex(t), other)

def DocLines.lines_entry_malformed_unless_write(t, other):
  lmw_main(t, Fdl.get_proj(t), Fdx.fdx_proj(t), other)
