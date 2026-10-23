# eukhe: the proof of LAW limit_malformed_fails_closed

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base.bend as L

# Admission limits
# ----------------

def pcf.malformed_cap(m: Maybe<&2, Cf.Val>, h: {Cf.malformed_val(m) == True{} : Bool}) -> {Cf.slot_limit(m) == Cf.Cap{1n} : Cf.Lim}:
  match m:
    case None{}:
      L.ppr.absurdF({Cf.slot_limit(None{}) == Cf.Cap{1n} : Cf.Lim}, h)
    case Some{v}:
      match v:
        case Cf.Num{n}:
          L.ppr.absurdF({Cf.slot_limit(Some{Cf.Num{n}}) == Cf.Cap{1n} : Cf.Lim}, h)
        case Cf.Malformed{}:
          {==}

# LAW limit_malformed_fails_closed
def pcf.limit_malformed_fails_closed(s: Cf.InFlight, +p: Nat, h: {Cf.malformed_at(s, p) == True{} : Bool}) -> {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}:
  match s:
    case Cf.Unset{}:
      L.ppr.absurdF({Cf.limit(Cf.Unset{}, p) == Cf.Cap{1n} : Cf.Lim}, h)
    case Cf.Entries{es}:
      pcf.malformed_cap(Cf.slot(es, p), h)
    case Cf.NotMap{}:
      {==}

def Config.limit_malformed_fails_closed(s, p, h):
  pcf.limit_malformed_fails_closed(s, p, h)
