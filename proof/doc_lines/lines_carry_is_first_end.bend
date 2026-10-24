# eukhe: the proof of LAW lines_carry_is_first_end: the carry is the write's kept ending
# of the same file, the first ending scanned byte by byte (the lemmas of
# proof/doc_lines/lines_write_keeps.bend)

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./lines_write_keeps.bend as LWK

def lcfe.orlf(m: Maybe<&2, Dl.End>) -> {Dl.or_lf(m) == DocLines.lines.OrLf(m) : Dl.End}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

def DocLines.lines_carry_is_first_end(bom, bs):
  %LWK.lwk.first(bs, False{}) : {Dl.carry(Dl.proj(Dl.Doc{bom, bs})) == DocLines.lines.OrLf(_) : Dl.End}
  lcfe.orlf(LWK.lwk.at(False{}, Dl.split(bs)))
