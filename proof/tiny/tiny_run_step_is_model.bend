# eukhe: the proof of LAW tiny_run_step_is_model
#
# PROOF: a case per phase and outcome. An outcome the phase does not
# wait for computes to nothing on both sides. The awaited one decides by
# the code's choice (elect, shut, launched, confirm, bind), which is the
# spec's (tiny_elect_spec, tiny_shut_spec, tiny_launched_spec,
# tiny_confirm_spec, tiny_bind_spec); each choice then makes the same
# phase and reply on both sides (tr.by_*, a case per choice).

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/elect.bend as TinyElect
import ../../laws/tiny/run.bend as TinyRun
import ./tiny_elect_spec.bend as PTinyElectSpec
import ./tiny_shut_spec.bend as PTinyShutSpec
import ./tiny_launched_spec.bend as PTinyLaunchedSpec
import ./tiny_confirm_spec.bend as PTinyConfirmSpec
import ./tiny_bind_spec.bend as PTinyBindSpec

def tr.by_elect(+m: String, a: Tn.Act) -> {Tn.run.elect(m, a) == TinyRun.sp_by_elect(m, a) : Tn.Run & Tn.Do}:
  match a:
    case Tn.Join{}:
      {==}
    case Tn.Replace{}:
      {==}
    case Tn.Start{}:
      {==}
    case Tn.Broken{}:
      {==}

def tr.by_shut(+m: String, x: Tn.Shut) -> {Tn.run.shut(m, x) == TinyRun.sp_by_shut(m, x) : Tn.Run & Tn.Do}:
  match x:
    case Tn.Down{}:
      {==}
    case Tn.Spoke{}:
      {==}
    case Tn.Cut{}:
      {==}

def tr.by_check(+m: String, +g: Tn.Got, c: Tn.Check) -> {Tn.run.check(m, g, c) == TinyRun.sp_by_check(m, g, c) : Tn.Run & Tn.Do}:
  match c:
    case Tn.Serving{}:
      {==}
    case Tn.Mistagged{}:
      {==}
    case Tn.Vacant{}:
      {==}
    case Tn.Faulty{}:
      {==}

def tr.by_seat(+m: String, x: Tn.Seat) -> {Tn.run.seat(m, x) == TinyRun.sp_by_seat(m, x) : Tn.Run & Tn.Do}:
  match x:
    case Tn.Adopt{}:
      {==}
    case Tn.Take{}:
      {==}
    case Tn.Fault{}:
      {==}

def tr.probing(+m: String, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Probing{}}, s) == TinyRun.sp_step(m, Tn.Probing{}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{+p}:
      %TinyElect.tiny_elect_spec(p, m) : {Tn.run.elect(m, Tn.elect(p, m)) == TinyRun.sp_by_elect(m, _) : Tn.Run & Tn.Do}
      tr.by_elect(m, Tn.elect(p, m))
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.shutting(+m: String, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, s) == TinyRun.sp_step(m, Tn.Shutting{}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{+h}:
      %TinyElect.tiny_shut_spec(h) : {Tn.run.shut(m, Tn.shut(h)) == TinyRun.sp_by_shut(m, _) : Tn.Run & Tn.Do}
      tr.by_shut(m, Tn.shut(h))
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.launching(+m: String, +f: Tn.Fresh, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Launching{f}}, s) == TinyRun.sp_step(m, Tn.Launching{f}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{+l}:
      %TinyElect.tiny_launched_spec(f, l) : {(Tn.Run{m, Tn.Checking{Tn.launched(f, l)}}, Tn.DoPing{}) == (Tn.Run{m, Tn.Checking{_}}, Tn.DoPing{}) : Tn.Run & Tn.Do}
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.checking(+m: String, +g: Tn.Got, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, s) == TinyRun.sp_step(m, Tn.Checking{g}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{+p}:
      %TinyElect.tiny_confirm_spec(p, m) : {Tn.run.check(m, g, Tn.confirm(p, m)) == TinyRun.sp_by_check(m, g, _) : Tn.Run & Tn.Do}
      tr.by_check(m, g, Tn.confirm(p, m))
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.seating(+m: String, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Seating{}}, s) == TinyRun.sp_step(m, Tn.Seating{}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{+p}:
      %TinyElect.tiny_bind_spec(p) : {Tn.run.seat(m, Tn.bind(p)) == TinyRun.sp_by_seat(m, _) : Tn.Run & Tn.Do}
      tr.by_seat(m, Tn.bind(p))
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.locking(+m: String, s: Tn.Seen) -> {Tn.step_run(Tn.Run{m, Tn.Locking{}}, s) == TinyRun.sp_step(m, Tn.Locking{}, s) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def TinyRun.tiny_run_step_is_model(m, ph, s):
  match ph:
    case Tn.Probing{}:
      tr.probing(m, s)
    case Tn.Shutting{}:
      tr.shutting(m, s)
    case Tn.Launching{f}:
      tr.launching(m, f, s)
    case Tn.Checking{g}:
      tr.checking(m, g, s)
    case Tn.Locking{}:
      tr.locking(m, s)
    case Tn.Seating{}:
      tr.seating(m, s)
    case Tn.Over{}:
      {==}
