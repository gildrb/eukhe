# eukhe: the proof of LAW theme_entry_invalid

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme

def Theme.theme_entry_invalid(vars, k, t, j, why, h):
  %Equal.sym(TChase.Got, TChase.chase(vars, j), TChase.Miss{why}, h) : {TReader.entry.got(k, t, _) == TReader.Bad{TFile.InColor{k, why}} : TReader.EntR}
  {==}
