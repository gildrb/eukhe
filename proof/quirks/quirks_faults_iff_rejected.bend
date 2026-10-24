# eukhe: the proof of LAW quirks_faults_iff_rejected
# By induction on the rules (proof/quirks/base.bend qp.all_fine): a rule
# is fine when its directive is known and it clashes with no later rule,
# the two halves of the model's `compiles`.

import Base
import ../../bend/ffi_quirks.bend as FQ
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/quirks.bend as Quirks
import ./base.bend as QP

def Quirks.quirks_faults_iff_rejected(known, rs):
  QP.qp.all_fine(rs, known)
