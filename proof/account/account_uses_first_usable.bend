# eukhe: the proof of LAW account_uses_first_usable
#
# PROOF: the run goes on with the first usable account when there is one
# (Ac.choose.of); no account of p is usable and m is (the model's
# usability is the spec's: LA.acb.usable, LA.acb.unusable), so the first
# usable one is m, at the length of p (LA.acb.first_at, by induction on
# p).

import Base
import ../../bend/account.bend as Ac
import ../../laws/account.bend as Account
import ./base.bend as LA

def Account.account_uses_first_usable(now, cap, waits, p, m, rest, hp, hm):
  %Equal.sym(Maybe<&2, Nat>, Ac.first(now, List.append(&2, Ac.Mark, p, m <> rest)), Some{List.length(&2, Ac.Mark, p)}, LA.acb.first_at(now, p, m, rest, hp, hm)) : {Ac.choose.of(now, cap, waits, List.append(&2, Ac.Mark, p, m <> rest), _) == Ac.Use{List.length(&2, Ac.Mark, p)} : Ac.Choice}
  {==}
