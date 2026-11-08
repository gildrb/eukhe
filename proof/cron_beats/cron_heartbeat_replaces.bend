# eukhe: the proof of LAW cron_heartbeat_replaces

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_beats.bend as CB
import ../../laws/cron.bend as Cron
import ../../laws/cron_beats.bend as CronBeats
import ../cron/base/logic.bend as LALogic
import ../cron/base/nat.bend as LANat

# A new heartbeat of s stops every earlier heartbeat of s first, so no
# record after the new one is a live heartbeat of s; the new one is.

# a record of s that stopped when it was a heartbeat is no live heartbeat
def rp.dead_h(b: Bool, hb: Bool, f: CS.Fact) -> {Bool.and(b, Bool.and(hb, Cron.live_fact_spec(CB.stop_if(Bool.and(b, hb), f)))) == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      match hb:
        case False{}:
          {==}
        case True{}:
          match f:
            case CS.Fact{st, p, nx, k}:
              match st:
                case Cr.Active{}:
                  {==}
                case Cr.Paused{}:
                  {==}
                case Cr.Finished{}:
                  {==}
                case Cr.Cancelled{}:
                  {==}

def rp.dead(+s: Nat, r: CB.Row) -> {Cron.beat_spec(s, CB.stop_row(s, r)) == False{} : Bool}:
  match r:
    case CB.Row{s2, fl, hb, f}:
      rp.dead_h(Nat.is_eq(s2, s), hb, f)

def rp.drop(b: Bool, -r: CB.Row, -rest: List<&2, CB.Row>, e: {b == False{} : Bool}, h: {rest == Nil{} : List<&2, CB.Row>}) -> {CronBeats.keep_spec(b, r, rest) == Nil{} : List<&2, CB.Row>}:
  match b:
    case True{}:
      LALogic.cron.pc.absurd({CronBeats.keep_spec(True{}, r, rest) == Nil{} : List<&2, CB.Row>}, e)
    case False{}:
      h

# after every heartbeat of s stops, s has no live heartbeat
def rp.none(+s: Nat, rs: List<&2, CB.Row>) -> {CronBeats.beats_spec(s, CB.stop_beats(s, rs)) == Nil{} : List<&2, CB.Row>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> t:
      rp.drop(Cron.beat_spec(s, CB.stop_row(s, r)), CB.stop_row(s, r), CronBeats.beats_spec(s, CB.stop_beats(s, t)), rp.dead(s, r), rp.none(s, t))

# CronBeats

def CronBeats.cron_heartbeat_replaces(s, file, p, at, rs):
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, LANat.cron.pc.eq_refl(s)) : {CronBeats.keep_spec(Bool.and(_, True{}), CB.Row{s, file, True{}, CS.Fact{Cr.Active{}, p, Some{at}, 0n}}, CronBeats.beats_spec(s, CB.stop_beats(s, rs))) == [CB.Row{s, file, True{}, CS.Fact{Cr.Active{}, p, Some{at}, 0n}}] : List<&2, CB.Row>}
  %Equal.sym(List<&2, CB.Row>, CronBeats.beats_spec(s, CB.stop_beats(s, rs)), Nil{}, rp.none(s, rs)) : {CB.Row{s, file, True{}, CS.Fact{Cr.Active{}, p, Some{at}, 0n}} <> _ == [CB.Row{s, file, True{}, CS.Fact{Cr.Active{}, p, Some{at}, 0n}}] : List<&2, CB.Row>}
  {==}
