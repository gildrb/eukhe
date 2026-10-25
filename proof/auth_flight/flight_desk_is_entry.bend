# eukhe: the proof of LAW flight_desk_is_entry
# The desk equals the laws' desk function by function (LAE.ae.desk).

import Base
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE

def AuthFlightEntry.flight_desk_is_entry(d, e):
  LAE.ae.desk(d, e)
