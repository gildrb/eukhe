# eukhe: the proof of LAW load_holds_first_end: load holds the first
# ending of the split, which is the carry the entry decides (LAW
# lines_carry_is_first), which is the first ending scanned byte by byte
# (LAW lines_carry_is_first_end)

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./lines_carry_is_first.bend as PLinesCarryIsFirst
import ./lines_carry_is_first_end.bend as PLinesCarryIsFirstEnd

def DocLines.load_holds_first_end(bom, bs):
  +e = Equal.trans(Dl.End, Dl.first(Dl.split(bs)), Dl.carry(Dl.proj(Dl.Doc{bom, bs})), DocLines.lines.OrLf(DocLines.lines.FirstEnd(bs, False{})), Equal.sym(Dl.End, Dl.carry(Dl.proj(Dl.Doc{bom, bs})), Dl.first(Dl.split(bs)), DocLines.lines_carry_is_first(bom, bs)), DocLines.lines_carry_is_first_end(bom, bs))
  Equal.cong(Dl.End, Bool & Dl.End, x => (bom, x), Dl.first(Dl.split(bs)), DocLines.lines.OrLf(DocLines.lines.FirstEnd(bs, False{})), e)
