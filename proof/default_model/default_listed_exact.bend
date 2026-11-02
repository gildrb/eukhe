# eukhe: the proof of LAW default_listed_exact

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LADefaultModel

def DefaultModel.default_listed_exact(ks, k):
  LADefaultModel.pdm.listed_spec(ks, k)
