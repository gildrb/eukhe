# eukhe: the proof of LAW output_frame

import Base
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/events.bend as AutoresearchEvents
import ./base/step.bend as AS

def of.got(m: Maybe<&2, ArL.Kv>, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +id: Nat, kvs: List<&2, ArL.Kv>) -> AutoresearchEvents.ar_line_ok(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, None{}}}}, ArP.line.got(m, cfg, seg, mode, runs, id, kvs)):
  match m:
    case None{}:
      ({==}, ({==}, ({==}, {==})))
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          ({==}, ({==}, ({==}, {==})))

def AutoresearchEvents.output_frame(s, t, run):
  match s:
    case ArS.St{cfg, seg, mode, runs, pend}:
      match pend:
        case None{}:
          AS.as.absurd(AutoresearchEvents.ar_line_ok(ArS.St{cfg, seg, mode, runs, None{}}, ArP.step(ArS.St{cfg, seg, mode, runs, None{}}, ArS.Line{t})), run)
        case Some{p}:
          match p:
            case ArS.Pend{id, kvs, fin}:
              match fin:
                case Some{b}:
                  AS.as.absurd(AutoresearchEvents.ar_line_ok(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{b}}}}, ArP.step(ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{id, kvs, Some{b}}}}, ArS.Line{t})), run)
                case None{}:
                  of.got(ArL.metric(t), cfg, seg, mode, runs, id, kvs)
