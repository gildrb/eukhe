# eukhe: the proof of LAW theme_entry_color

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme

def Theme.theme_entry_color(vars, k, t, j, v, h):
  %Equal.sym(TChase.Got, TChase.chase(vars, j), TChase.Hit{v}, h) : {TReader.entry.got(k, t, _) == TReader.Good{TFile.Ent{t, v}} : TReader.EntR}
  {==}
