# eukhe: the proof of LAW default_unkeyed_never_moves

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel

# LAW default_unkeyed_never_moves: a saved default whose provider has no
# credentials opens the session with no model; no other provider runs
def pdm.default_unkeyed_never_moves(m: Nat, out: Bool, next: Dm.Next) -> {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}:
  {==}

def pcf.default_unkeyed_never_moves(m: Nat, out: Bool, next: Dm.Next) -> {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}:
  pdm.default_unkeyed_never_moves(m, out, next)

def DefaultModel.default_unkeyed_never_moves(m, out, next):
  pcf.default_unkeyed_never_moves(m, out, next)
