# eukhe: the proof of LAW persist_writes_with_carry: persist is start from
# the held carry, and start weaves the carry rule (LAW persist_weaves_carry)

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./persist_weaves_carry.bend as PPersistWeavesCarry

def DocLines.persist_writes_with_carry(b, c, ps):
  Equal.cong(List<&2, Dl.B>, Dl.Doc, x => Dl.Doc{b, x}, Dl.start(ps, c), DocLines.lines.Weave(ps, DocLines.lines.Carry(DocLines.lines.Owns(ps), c)), DocLines.persist_weaves_carry(ps, c))
