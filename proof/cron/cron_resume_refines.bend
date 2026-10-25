# eukhe: the proof of LAW cron_resume_refines
# A case split on the schedule and the status. A one-shot, a finished and
# a cancelled job stay as they are on both sides; an active or paused
# repeating job runs again at the clock plus its interval, which the spec
# adds in units (c * u + (1 + n) * u) and the model scales whole
# ((c + 1 + n) * u): LSc.crsc.dist.

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron
import ./base/scale.bend as LSc

def crs.every(+v: Nat, +c: Nat, +n: Nat, +cl: Maybe<&2, Cr.Claim>) -> {(Cr.Active{}, (CS.NAt{Nat.add(Nat.mul(c, 1n+v), Nat.mul(1n+n, 1n+v))}, (0n, Cron.scale_claim(cl, 1n+v)))) == (Cr.Active{}, (CS.NAt{Nat.mul(Nat.add(c, 1n+n), 1n+v)}, (0n, Cron.scale_claim(cl, 1n+v)))) : Cron.View()}:
  %LSc.crsc.dist(c, 1n+n, 1n+v) : {(Cr.Active{}, (CS.NAt{_}, (0n, Cron.scale_claim(cl, 1n+v)))) == (Cr.Active{}, (CS.NAt{Nat.mul(Nat.add(c, 1n+n), 1n+v)}, (0n, Cron.scale_claim(cl, 1n+v)))) : Cron.View()}
  {==}

def Cron.cron_resume_refines(v, c, j):
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      match s:
        case Cr.Once{d}:
          match st:
            case Cr.Active{}:
              {==}
            case Cr.Paused{}:
              {==}
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}
        case Cr.Every{n}:
          match st:
            case Cr.Active{}:
              crs.every(v, c, n, cl)
            case Cr.Paused{}:
              crs.every(v, c, n, cl)
            case Cr.Finished{}:
              {==}
            case Cr.Cancelled{}:
              {==}
