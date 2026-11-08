# eukhe: the proof of LAW log_stepper_open_exact
#
# The entry and the spec read fsync with the same wire primitive; both
# plans of an open compute; every other path is the same error form and
# the shut state on both sides.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_log.bend as FLg
import ../../laws/log.bend as Log

def lso.end(b: Bool, fsync: Bool) -> {FLg.open.end(b, fsync) == Log.log_open_entry.end(b, fsync) : FLg.St & String}:
  match b:
    case True{}:
      match fsync:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def lso.go(r: Wr.Dec<Bool>) -> {FLg.open.go(r) == Log.log_open_entry.go(r) : FLg.St & String}:
  match r:
    case Wr.Got{b, s}:
      lso.end(Wr.end(s), b)
    case Wr.Bad{}:
      {==}

def Log.log_stepper_open_exact(s):
  lso.go(Wr.get_bool(s))
