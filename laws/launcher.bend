# eukhe: the laws of area launcher

import Base
import ../bend/launcher.bend as La

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW: an idle shutdown never aborts a run, in any order of prompts, run
# ends, quiesces, releases and commits on any workers
law idle_shutdown_never_aborts:
  for +bs: List<&2, Bool>
  for +ops: List<&2, La.Op>
  {La.St.aborted(La.run(bs, ops)) == 0n : Nat}

# LAW: a supervisor adopts a worker only when the worker reports the
# supervisor's build
law adopt_same_build:
  for +sup: Nat
  for +w: Maybe<&2, Nat>
  for adopted: {La.adoption(sup, w) == La.Adopt{} : La.Adoption}
  {w == Some{sup} : Maybe<&2, Nat>}
