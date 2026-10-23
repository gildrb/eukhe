# eukhe: the proof of LAW rewind_stops_orphans

import Base
import ../../bend/job.bend as Jb
import ../../laws/job.bend as Job
import ./base.bend as LA

def pj.ok_run(h: Bool, +i: Nat, r: Bool) -> {True{} == Bool.or(Bool.not(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r}))), h) : Bool}:
  match h:
    case True{}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def pj.stops(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Jb.Slot{+i, +r}:
          +h = Jb.elem(keep, i)
          %LA.pj.id_stop(h, i, r) : {Bool.and(Bool.or(Bool.not(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r}))), Jb.elem(keep, _)), Jb.running_in(Jb.rewind(rest, keep), keep)) == True{} : Bool}
          %pj.ok_run(h, i, r) : {Bool.and(_, Jb.running_in(Jb.rewind(rest, keep), keep)) == True{} : Bool}
          pj.stops(rest, keep)

def pj.rewind_stops_orphans(+js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}:
  pj.stops(js, keep)

def Job.rewind_stops_orphans(js, keep):
  pj.rewind_stops_orphans(js, keep)
