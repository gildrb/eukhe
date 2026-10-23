# eukhe: the proof of LAW theme_read_loaded

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def Theme.theme_read_loaded(nm, vars, cols, pg, cd, io, ok, all, fine1, fine2, fine3):
  +gs = Theme.th.goods(vars, cols)
  +want = {TReader.Loaded{TFile.Th{nm, gs, Theme.th.bgv(vars, pg), Theme.th.bgv(vars, cd), Theme.th.bgv(vars, io)}} : TReader.Read}
  %Equal.sym(TReader.Read, TReader.read(TFile.RFile{nm, vars, cols, pg, cd, io}), TReader.read.end(nm, gs, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, pg, cd, io, ok, all)) : {_ == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.BgOk{Theme.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, TFile.OnPage{}, pg, fine1)) : {TReader.read.end(nm, gs, _, TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnCard{}, cd), TReader.BgOk{Theme.th.bgv(vars, cd)}, LA.pt.surf_fine(vars, TFile.OnCard{}, cd, fine2)) : {TReader.read.end(nm, gs, TReader.BgOk{Theme.th.bgv(vars, pg)}, _, TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnInfo{}, io), TReader.BgOk{Theme.th.bgv(vars, io)}, LA.pt.surf_fine(vars, TFile.OnInfo{}, io, fine3)) : {TReader.read.end(nm, gs, TReader.BgOk{Theme.th.bgv(vars, pg)}, TReader.BgOk{Theme.th.bgv(vars, cd)}, _) == want : TReader.Read}
  {==}
