# eukhe: the proof of LAW default_on_saved_exact

import Base
import ../../bend/default_model.bend as Dm
import ../../laws/default_model.bend as DefaultModel
import ./base.bend as LADefaultModel

def DefaultModel.default_on_saved_exact(r):
  LADefaultModel.pdm.on_saved_spec(r)
