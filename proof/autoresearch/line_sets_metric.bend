# eukhe: the proof of LAW line_sets_metric

import Base
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../laws/autoresearch/model.bend as Autoresearch

# the line read, a metric or not
def lsm.got(m: Maybe<&2, ArL.Kv>, c: Maybe<&2, ArS.Cfg>, seg: Nat, mode: ArS.Mode, runs: List<&2, ArS.Row>, id: Nat, kvs: List<&2, ArL.Kv>)
  -> {ArP.line.got(m, c, seg, mode, runs, id, kvs) == ArS.Took{ArS.St{c, seg, mode, runs, Some{ArS.Pend{id, Autoresearch.ar_put(kvs, m), None{}}}}, ArS.Nothing{}, False{}} : ArS.Res}:
  match m:
    case None{}:
      {==}
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          {==}

def Autoresearch.line_sets_metric(c, seg, mode, runs, id, kvs, t):
  lsm.got(ArL.metric(t), c, seg, mode, runs, id, kvs)
