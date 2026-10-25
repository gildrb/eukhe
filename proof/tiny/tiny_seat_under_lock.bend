# eukhe: the proof of LAW tiny_seat_under_lock
#
# PROOF: a seat run is Locking without the lock, Seating with it, or
# Over. Locking answers the lock with a ping and goes to Seating holding
# the lock; any other outcome answers nothing and the lock stays unheld
# (ts.locking). Seating answers a ping with a seat under the lock and
# ends; any other outcome answers nothing (ts.seating). Over answers
# nothing to every outcome (ts.over).

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/run.bend as TinyRun

def ts.over(ss: List<&2, Tn.Seen>, +m: String, +h: Bool) -> {TinyRun.tr_seat(ss, Tn.Run{m, Tn.Over{}}, h) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> rest:
      ts.over(rest, m, Bool.or(h, TinyRun.tr_is_lock(s)))

def ts.seating(ss: List<&2, Tn.Seen>, +m: String) -> {TinyRun.tr_seat(ss, Tn.Run{m, Tn.Seating{}}, True{}) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Tn.Pinged{p}:
          match p:
            case Tn.Missing{}:
              ts.over(rest, m, True{})
            case Tn.Unreachable{}:
              ts.over(rest, m, True{})
            case Tn.Pong{t}:
              ts.over(rest, m, True{})
            case Tn.Odd{}:
              ts.over(rest, m, True{})
            case Tn.Garbled{}:
              ts.over(rest, m, True{})
            case Tn.Hung{}:
              ts.over(rest, m, True{})
        case Tn.ShutHeard{hd}:
          ts.seating(rest, m)
        case Tn.Came{l}:
          ts.seating(rest, m)
        case Tn.NoSpawn{}:
          ts.seating(rest, m)
        case Tn.Locked{}:
          ts.seating(rest, m)

def ts.locking(ss: List<&2, Tn.Seen>, +m: String) -> {TinyRun.tr_seat(ss, Tn.Run{m, Tn.Locking{}}, False{}) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Tn.Pinged{p}:
          ts.locking(rest, m)
        case Tn.ShutHeard{hd}:
          ts.locking(rest, m)
        case Tn.Came{l}:
          ts.locking(rest, m)
        case Tn.NoSpawn{}:
          ts.locking(rest, m)
        case Tn.Locked{}:
          ts.seating(rest, m)

def TinyRun.tiny_seat_under_lock(ss):
  ts.locking(ss, "")
