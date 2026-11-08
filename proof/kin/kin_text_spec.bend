# eukhe: the proof of LAW kin_text_spec
#
# PROOF: case analysis on the refusal; each text is the spec's text.

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_text_spec(f):
  match f:
    case K.SelfMessage{}:
      {==}
    case K.NotKin{}:
      {==}
