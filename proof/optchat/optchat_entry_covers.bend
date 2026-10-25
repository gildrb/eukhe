# eukhe: the proof of LAW optchat_entry_covers
# A spelled open opens the laws' open (LAO.oo.opened), whose views tile
# the chat when the loaded view does (LAO.oo.covers). Each input keeps
# that: garbage keeps the chat, a refused stepper holds none, and a whole
# request moves the chat as the model does (LAF.oe.serve), by a model
# event, which keeps both views tiling (LAS.cover.step), by a wait, which
# moves only the busy calls, or not at all (ec.next); so does every list
# of inputs (ec.feed).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/queue.bend as OQueue
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF
import ./base/open.bend as LAO
import ./base/step.bend as LAS

# a wait moves only the busy calls
def ec.wait(s: OState.St, inv: LAS.cover.Inv(s)) -> LAS.cover.Inv(OQueue.St.wait(s)):
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      inv

# the model's move on a request keeps both views tiling
def ec.next(+cfg: OState.Cfg, +s: OState.St, q: FOc.Q, inv: LAS.cover.Inv(s)) -> LAS.cover.Inv(Optchat.oc_next(cfg, s, q)):
  match q:
    case FOc.QMsg{}:
      LAS.cover.step(cfg, s, OState.Msg{}, inv)
    case FOc.QBuilt{+l, +k, +z}:
      LAS.cover.step(cfg, s, OState.Build{Optchat.oc_node(l, k), z}, inv)
    case FOc.QStart{+l, +k}:
      LAS.cover.step(cfg, s, OState.Start{Optchat.oc_node(l, k)}, inv)
    case FOc.QFree{+l, +k}:
      LAS.cover.step(cfg, s, OState.Free{Optchat.oc_node(l, k)}, inv)
    case FOc.QWait{}:
      ec.wait(s, inv)
    case FOc.QCands{}:
      inv
    case FOc.QNeed{}:
      inv
    case FOc.QCtx{l, k}:
      inv
    case FOc.QBusy{}:
      inv

def ec.serve(+cfg: OState.Cfg, +s: OState.St, +q: FOc.Q, inv: LAS.cover.Inv(s)) -> Optchat.oc_covers(Optchat.oc_state(FOc.serve(cfg, s, q))):
  %Equal.sym(FOc.St & String, FOc.serve(cfg, s, q), (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)), LAF.oe.serve(cfg, s, q)) : Optchat.oc_covers(Optchat.oc_state(_))
  ec.next(cfg, s, q, inv)

def ec.end(done: Bool, +cfg: OState.Cfg, +s: OState.St, +q: FOc.Q, inv: LAS.cover.Inv(s)) -> Optchat.oc_covers(Optchat.oc_state(FOc.step.end(done, cfg, s, q))):
  match done:
    case True{}:
      ec.serve(cfg, s, q, inv)
    case False{}:
      inv

def ec.ev(+cfg: OState.Cfg, +s: OState.St, d: Wr.Dec<FOc.Q>, inv: LAS.cover.Inv(s)) -> Optchat.oc_covers(Optchat.oc_state(FOc.step.ev(cfg, s, d))):
  match d:
    case Wr.Got{+q, rest}:
      ec.end(Wr.end(rest), cfg, s, q, inv)
    case Wr.Bad{}:
      inv

# any input keeps both views tiling
def ec.step(st: FOc.St, +x: String, inv: Optchat.oc_covers(st)) -> Optchat.oc_covers(Optchat.oc_state(FOc.step(st, x))):
  match st:
    case FOc.Live{+cfg, +s}:
      ec.ev(cfg, s, FOc.get_ev(x), inv)
    case FOc.Refused{}:
      Unit{}

# and so does any list of inputs
def ec.feed(xs: List<&2, String>, +st: FOc.St, inv: Optchat.oc_covers(st)) -> Optchat.oc_covers(Optchat.oc_feed(xs, st)):
  match xs:
    case Nil{}:
      inv
    case +x <> rest:
      ec.feed(rest, Optchat.oc_state(FOc.step(st, x)), ec.step(st, x, inv))

def ec.main(+o: FOc.Open, +xs: List<&2, String>, fits: {Optchat.oc_open_fits(o) == True{} : Bool}, tiles: {Optchat.oc_tiles(Optchat.oc_view(o), 0n, Optchat.oc_t(o)) == True{} : Bool}) -> Optchat.oc_covers(Optchat.oc_feed(xs, Optchat.oc_state(FOc.open(Optchat.oc_spell_open(o))))):
  %Equal.sym(FOc.St & String, FOc.open(Optchat.oc_spell_open(o)), Optchat.oc_open_model(o), LAO.oo.opened(o, fits)) : Optchat.oc_covers(Optchat.oc_feed(xs, Optchat.oc_state(_)))
  ec.feed(xs, Optchat.oc_state(Optchat.oc_open_model(o)), LAO.oo.covers(o, tiles))

def Optchat.optchat_entry_covers(o, xs, fits, tiles):
  ec.main(o, xs, fits, tiles)
