# eukhe: the proof of LAW lines_carry_is_first

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines

# the carry of projected lines is their first ending
def lcf.carry(ls: Dl.Lines) -> {Dl.or_lf(Dl.first_end(Dl.proj.lines(Dl.pieces(ls)))) == Dl.first(ls) : Dl.End}:
  match ls:
    case Dl.More{t, e, r}:
      {==}
    case Dl.Last{t}:
      {==}

def DocLines.lines_carry_is_first(bom, bs):
  lcf.carry(Dl.split(bs))
