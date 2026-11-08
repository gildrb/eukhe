# eukhe: the proof of LAW metric_print_round_trip

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./metric_print_round_trip/parse.bend as AdParse

def Autoresearch.metric_print_round_trip(name, d, okn, c, fit):
  match d:
    case ArD.Dec{+neg, +ds, +scale}:
      +v = ArD.show(ArD.Dec{neg, ds, scale})
      %Equal.sym(Maybe<&2, ArL.Parts>, ArL.parse(String.append("METRIC ", String.append(name, SCon{'=', v}))), ArL.pl.sign(" ", name, v), AdParse.ad.head(name, v, okn)) : {ArL.metric.of(_) == Some{ArL.Kv{name, ArD.Dec{neg, ds, scale}}} : Maybe<&2, ArL.Kv>}
      AdParse.ad.value(name, ds, neg, scale, c, fit)
