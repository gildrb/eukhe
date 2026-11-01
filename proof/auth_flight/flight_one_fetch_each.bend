# eukhe: the proof of LAW flight_one_fetch_each
# A caller that fetches leads (AD.ad.fetch_le), and every run keeps at
# most one leader per provider (POL.pol.run, flight_one_leader).

import Base
import ../../bend/auth_flight.bend as F
import ../../laws/auth_flight/entry.bend as S
import ../../laws/auth_flight/safety.bend as SS
import ../../laws/auth_flight/safety.bend as AuthFlightSafety
import ./base/logic.bend as AL
import ./base/callers.bend as AC
import ./base/flights.bend as AF
import ./flight_one_leader.bend as POL

def AuthFlightSafety.flight_one_fetch_each(evs, p):
  AL.ad.le_trans(SS.af_fetchers(p, S.af_cs(SS.af_run(evs))), SS.af_leaders(p, S.af_cs(SS.af_run(evs))), 1n, AF.ad.fetch_le(p, S.af_cs(SS.af_run(evs))), POL.pol.run(evs, F.Desk{Nil{}, 0n}, q => {==})(p))
