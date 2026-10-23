# eukhe: the proof of LAW theme_read_info

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_info(nm, vars, cols, pg, cd, j, why, ok, all, fine1, fine2, bad):
  +gs = Theme.th.goods(vars, cols)
  +want = {TReader.Failed{TFile.InExport{TFile.OnInfo{}, why}} : TReader.Read}
  %Equal.sym(TReader.Read, TReader.read(TFile.RFile{nm, vars, cols, pg, cd, Some{j}}), TReader.read.end(nm, gs, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, Some{j})), LA.pt.read_end(nm, vars, cols, pg, cd, Some{j}, ok, all)) : {_ == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.BgOk{Theme.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, TFile.OnPage{}, pg, fine1)) : {TReader.read.end(nm, gs, _, TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, Some{j})) == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.BgOk{Theme.th.bgv(vars, cd)}, LA.pt.surf_fine(vars, TFile.OnCard{}, cd, fine2)) : {TReader.read.end(nm, gs, TReader.BgOk{Theme.th.bgv(vars, pg)}, _, TReader.surf(TChase.index(vars), TFile.OnInfo{}, Some{j})) == want : TReader.Read}
  %Equal.sym(TChase.Got, TChase.chase(vars, j), TChase.Miss{why}, bad) : {TReader.read.end(nm, gs, TReader.BgOk{Theme.th.bgv(vars, pg)}, TReader.BgOk{Theme.th.bgv(vars, cd)}, TReader.surf.got(TFile.OnInfo{}, _)) == want : TReader.Read}
  {==}
