# eukhe: the proof of LAW account_login_when_all_dead
#
# PROOF: with every login dead no account is usable (LA.acb.dead_first)
# and none is limited (LA.acb.dead_soonest), so no login is left
# (LA.acb.login).

import Base
import ../../laws/account.bend as Account
import ./base.bend as LA

def Account.account_login_when_all_dead(now, cap, waits, ms, h):
  LA.acb.login(now, cap, waits, ms, h)
