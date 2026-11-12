# eukhe: the proof of LAW budget_entry_example
#
# PROOF: each side computes to the same list of strings.

import Base
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ../../laws/budget.bend as Budget

def Budget.budget_entry_example():
  ({==}, ({==}, {==}))
