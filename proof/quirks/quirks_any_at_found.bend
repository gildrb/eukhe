# eukhe: the proof of LAW quirks_any_at_found
# Induction on the rules and the index (QA.qa.found): at the rule, the
# model's applies, directive and rank are the tables' (qa.applies,
# qp.dir, qa.rank), so its test holds; past it, any_at's or keeps the
# rest's yes.

import Base
import ../../laws/quirks.bend as Quirks
import ./base/any_at.bend as QA

def Quirks.quirks_any_at_found(rs, q, d, k, i, r, at, hit, dir, high):
  QA.qa.found(rs, q, d, k, i, r, at, hit, dir, high)
