# eukhe: the proof of LAW theme_read_card

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.read(+nm: String, +vars: List<&2, TFile.Var>, +cols: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, +j: TFile.Json, +io: Maybe<&2, TFile.Json>, +why: TFile.Why, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}, +all: {Theme.th.absent(Theme.th.goods(vars, cols)) == [] : List<&2, U32>}, +fine: {Theme.th.fine(vars, pg) == True{} : Bool}, +bad: {TChase.chase(vars, j) == TChase.Miss{why} : TChase.Got})
  -> {TReader.read(TFile.RFile{nm, vars, cols, pg, Some{j}, io}) == TReader.Failed{TFile.InExport{TFile.OnCard{}, why}} : TReader.Read}:
  +gs = Theme.th.goods(vars, cols)
  +want = {TReader.Failed{TFile.InExport{TFile.OnCard{}, why}} : TReader.Read}
  %Equal.sym(TReader.Read, TReader.read(TFile.RFile{nm, vars, cols, pg, Some{j}, io}), TReader.read.end(nm, gs, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.surf(TChase.index(vars), TFile.OnCard{}, Some{j}), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)), LA.pt.read_end(nm, vars, cols, pg, Some{j}, io, ok, all)) : {_ == want : TReader.Read}
  %Equal.sym(TReader.Bg, TReader.surf(TChase.index(vars), TFile.OnPage{}, pg), TReader.BgOk{Theme.th.bgv(vars, pg)}, LA.pt.surf_fine(vars, TFile.OnPage{}, pg, fine)) : {TReader.read.end(nm, gs, _, TReader.surf(TChase.index(vars), TFile.OnCard{}, Some{j}), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) == want : TReader.Read}
  %Equal.sym(TChase.Got, TChase.chase(vars, j), TChase.Miss{why}, bad) : {TReader.read.end(nm, gs, TReader.BgOk{Theme.th.bgv(vars, pg)}, TReader.surf.got(TFile.OnCard{}, _), TReader.surf(TChase.index(vars), TFile.OnInfo{}, io)) == want : TReader.Read}
  {==}

def Theme.theme_read_card(nm, vars, cols, pg, j, io, why, ok, all, fine, bad):
  LA.pt.parse_failed(TFile.RFile{nm, vars, cols, pg, Some{j}, io}, TFile.InExport{TFile.OnCard{}, why}, pt.read(nm, vars, cols, pg, j, io, why, ok, all, fine, bad))
