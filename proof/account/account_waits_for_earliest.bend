# eukhe: the proof of LAW account_waits_for_earliest
#
# PROOF: no account is usable, as every one is dead or limited until e or
# later and e is past now (LA.acb.first_none_at); the earliest limit is
# the one until e, after limits past e and before ones until e or later
# (LA.acb.soonest_at); the model's wait is the spec's (LA.acb.waits_may),
# which the premise says holds, so the run waits for it
# (LA.acb.limited_at).

import Base
import ../../bend/account.bend as Ac
import ../../laws/account.bend as Account
import ./base.bend as LA

def Account.account_waits_for_earliest(now, cap, waits, p, e, rest, he, hp, hr, hw):
  %LA.acb.limited_at(now, cap, waits, p, e, rest, he, hp, hr) : {_ == Ac.Hold{List.length(&2, Ac.Mark, p), e} : Ac.Choice}
  %Equal.sym(Bool, Account.ac_may_wait(now, cap, waits, e), True{}, hw) : {Ac.limited.of(_, List.length(&2, Ac.Mark, p), e) == Ac.Hold{List.length(&2, Ac.Mark, p), e} : Ac.Choice}
  {==}
