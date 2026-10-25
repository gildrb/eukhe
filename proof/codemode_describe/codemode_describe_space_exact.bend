# eukhe: the proof of LAW codemode_describe_space_exact

import Base
import ../../bend/codemode_describe.bend as Dsc
import ../../laws/codemode_describe.bend as CodemodeDescribe
import ./base.bend as LACd

# PROOF of LAW codemode_describe_space_exact: the model's single pass is the first longest of the spec's hits (cd.space).

def CodemodeDescribe.codemode_describe_space_exact(name, ps):
  LACd.cd.space(name, ps)
