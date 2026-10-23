# eukhe: the proof of LAW theme_read_page

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_page(nm, vars, cols, j, cd, io, why, ok, all, bad):
  +gs = Theme.th.goods(vars, cols)
  +want = {TReader.Failed{TFile.InExport{TFile.OnPage{}, why}} : TReader.Read}
  %Equal.sym(TReader.Read, TReader.read(TFile.RFile{nm, vars, cols, Some{j}, cd, io}), TReader.read.end(nm, gs, TReader.surf(TChase.index(vars), TFile.OnPage{}, Some{j}), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, Some{j}, cd, io, ok, all)) : {_ == want : TReader.Read}
  %Equal.sym(TChase.Got, TChase.chase(vars, j), TChase.Miss{why}, bad) : {TReader.read.end(nm, gs, TReader.surf.got(TFile.OnPage{}, _), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) == want : TReader.Read}
  {==}
