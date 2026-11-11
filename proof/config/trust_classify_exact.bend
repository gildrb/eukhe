# eukhe: the proof of LAW trust_classify_exact
# The model's table is the laws' (a closed computation), and the model's
# search is the laws' over any table (an induction on the rules).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def Config.trust_classify_exact(p):
  LA.pcf.classify(p)
