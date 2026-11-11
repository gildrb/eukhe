# eukhe: the proof of LAW quirks_any_at_witness
# any_at is the head's test or any_at of the rest (QA.qa.unf); walking the
# rules (QA.qa.wit), the first whose test holds is the witness, its test
# read back through the tables (qa.applies, qp.dir, qa.rank).

import Base
import ../../bend/infer.bend as If
import ../../laws/quirks.bend as Quirks
import ./base/any_at.bend as QA

def Quirks.quirks_any_at_witness(rs, q, d, k, yes):
  QA.qa.wit(rs, q, d, k, QA.qa.hd_of(rs, q, d, k), {==}, Equal.trans(Bool, QA.qa.rest_or(QA.qa.hd_of(rs, q, d, k), rs, q, d, k), If.any_at(rs, q, d, k), True{}, Equal.sym(Bool, If.any_at(rs, q, d, k), QA.qa.rest_or(QA.qa.hd_of(rs, q, d, k), rs, q, d, k), QA.qa.unf(rs, q, d, k)), yes))
