# eukhe: the proof of LAW budget_entry_malformed_exact
#
# PROOF: every answer opens with a Nat, never 'E' (wire_nat_not_err; be.answer_ok); so an answer that opens with 'E' is the one error form (be.refuse).

import Base
import ../../laws/budget.bend as Budget
import ../../bend/budget.bend as B
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ../../spec/budget/ledger.bend as S
import ./base/entry.bend as BE

def Budget.budget_entry_malformed_exact(s, bad):
  BE.be.refuse(FBg.get_req(s), bad)
