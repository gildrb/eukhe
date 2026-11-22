# eukhe: the proof of LAW account_hands_on_past_wait
#
# PROOF: as for account_waits_for_earliest, the earliest limit is the one
# until e and no account is usable (LA.acb.limited_at); the premise says
# the run may not wait, so it hands the run on with that account and e.

import Base
import ../../bend/account.bend as Ac
import ../../laws/account.bend as Account
import ./base.bend as LA

def Account.account_hands_on_past_wait(now, cap, waits, p, e, rest, he, hp, hr, hw):
  %LA.acb.limited_at(now, cap, waits, p, e, rest, he, hp, hr) : {_ == Ac.Quota{List.length(&2, Ac.Mark, p), e} : Ac.Choice}
  %Equal.sym(Bool, Account.ac_may_wait(now, cap, waits, e), False{}, hw) : {Ac.limited.of(_, List.length(&2, Ac.Mark, p), e) == Ac.Quota{List.length(&2, Ac.Mark, p), e} : Ac.Choice}
  {==}
