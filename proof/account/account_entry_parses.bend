# eukhe: the proof of LAW account_entry_parses
#
# PROOF: the clock, the wait limit and the waits are the first three Nats;
# the Nats of the marks read back as those marks (LA.acb.marks_back, by
# induction on the marks).

import Base
import ../../bend/account.bend as Ac
import ../../bend/ffi_account.bend as FAc
import ../../laws/account.bend as Account
import ./base.bend as LA

def Account.account_entry_parses(x):
  match x:
    case Ac.In{+now, +cap, +waits, +ms}:
      %Equal.sym(Maybe<&2, List<&2, Ac.Mark>>, FAc.marks(Account.ac_marks_nats(ms)), Some{ms}, LA.acb.marks_back(ms)) : {FAc.parse.marks(now, cap, waits, _) == Some{Ac.In{now, cap, waits, ms}} : Maybe<&2, Ac.In>}
      {==}
