# eukhe: the proof of LAW lines_entry_malformed_unless_load
#
# PROOF: `L` is no plan (its runs do not read), so the entry reads a
# projection, and the projection's decoder reads only a spelled projection
# that fits (fdx_proj); when it reads none the entry answers the
# projection's error, which the premise excludes.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../base/ffi_doc_lines/exact.bend as Fdx

def lml_Ex(t: String) -> Type:
  &p: Dl.Proj -> &rest: String -> ({t == LawsBase.proj_spell(p, rest) : String} & {LawsBase.proj_fits(p) == True{} : Bool})

def lml_main(-t: String, d: Wr.Dec<Dl.Proj>, pd: Fdx.fdx_pp(t, d),
  other: {String.eq(Fdl.load.run(d), Wr.err("doc_lines: malformed projection")) == False{} : Bool}) -> lml_Ex(t):
  match d:
    case Wr.Got{+p, +r}:
      (p, (r, pd))
    case Wr.Bad{}:
      Fdx.fdx_absurd(lml_Ex(t), other)

def DocLines.lines_entry_malformed_unless_load(t, other):
  lml_main(t, Fdl.get_proj(t), Fdx.fdx_proj(t), other)
