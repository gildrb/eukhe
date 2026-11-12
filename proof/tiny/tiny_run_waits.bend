# eukhe: the proof of LAW tiny_run_waits
#
# PROOF: a case per phase and outcome. The outcome the phase waits for
# makes the premise True == False; every other one computes to the run
# kept and nothing to do. An ended run computes so on every outcome.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA

def trw.probing(+m: String, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Probing{}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Probing{}}, s) == (Tn.Run{m, Tn.Probing{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Probing{}}, Tn.Pinged{p}) == (Tn.Run{m, Tn.Probing{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def trw.shutting(+m: String, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Shutting{}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Shutting{}}, s) == (Tn.Run{m, Tn.Shutting{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Shutting{}}, Tn.ShutHeard{h}) == (Tn.Run{m, Tn.Shutting{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def trw.launching(+m: String, +f: Tn.Fresh, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Launching{f}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Launching{f}}, s) == (Tn.Run{m, Tn.Launching{f}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Launching{f}}, Tn.Came{l}) == (Tn.Run{m, Tn.Launching{f}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.NoSpawn{}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Launching{f}}, Tn.NoSpawn{}) == (Tn.Run{m, Tn.Launching{f}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.Locked{}:
      {==}

def trw.checking(+m: String, +g: Tn.Got, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Checking{g}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Checking{g}}, s) == (Tn.Run{m, Tn.Checking{g}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Checking{g}}, Tn.Pinged{p}) == (Tn.Run{m, Tn.Checking{g}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def trw.locking(+m: String, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Locking{}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Locking{}}, s) == (Tn.Run{m, Tn.Locking{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
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
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Locking{}}, Tn.Locked{}) == (Tn.Run{m, Tn.Locking{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)

def trw.seating(+m: String, s: Tn.Seen, idle: {TinyRun.tr_awaits(Tn.Seating{}, s) == False{} : Bool}) -> {Tn.step_run(Tn.Run{m, Tn.Seating{}}, s) == (Tn.Run{m, Tn.Seating{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}:
  match s:
    case Tn.Pinged{p}:
      LA.te.tf({Tn.step_run(Tn.Run{m, Tn.Seating{}}, Tn.Pinged{p}) == (Tn.Run{m, Tn.Seating{}}, Tn.DoNothing{}) : Tn.Run & Tn.Do}, idle)
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def TinyRun.tiny_run_waits(m, ph, s, idle):
  match ph:
    case Tn.Probing{}:
      trw.probing(m, s, idle)
    case Tn.Shutting{}:
      trw.shutting(m, s, idle)
    case Tn.Launching{f}:
      trw.launching(m, f, s, idle)
    case Tn.Checking{g}:
      trw.checking(m, g, s, idle)
    case Tn.Locking{}:
      trw.locking(m, s, idle)
    case Tn.Seating{}:
      trw.seating(m, s, idle)
    case Tn.Over{}:
      {==}
