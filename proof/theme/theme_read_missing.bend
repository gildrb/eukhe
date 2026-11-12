# eukhe: the proof of LAW theme_read_missing

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.read(+nm: String, +vars: List<&2, TFile.Var>, +cols: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, +io: Maybe<&2, TFile.Json>, +t: U32, +ts: List<&2, U32>, +ok: {Theme.th.clean(vars, cols) == True{} : Bool}, +miss: {Theme.th.absent(Theme.th.goods(vars, cols)) == t <> ts : List<&2, U32>})
  -> {TReader.read(TFile.RFile{nm, vars, cols, pg, cd, io}) == TReader.Failed{TFile.Missing{t <> ts}} : TReader.Read}:
  +gs = Theme.th.goods(vars, cols)
  +mt = Equal.trans(List<&2, U32>, TReader.missing(gs), Theme.th.absent(gs), t <> ts, LA.pt.missing_absent(gs), miss)
  %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), cols), TReader.All{gs}, LA.pt.ents_all(vars, cols, ok)) : {TReader.read.cols(nm, TChase.index(vars), _, pg, cd, io) == TReader.Failed{TFile.Missing{t <> ts}} : TReader.Read}
  %Equal.sym(List<&2, U32>, TReader.missing(gs), t <> ts, mt) : {TReader.read.full(nm, TChase.index(vars), gs, _, pg, cd, io) == TReader.Failed{TFile.Missing{t <> ts}} : TReader.Read}
  {==}

def Theme.theme_read_missing(nm, vars, cols, pg, cd, io, t, ts, ok, miss):
  LA.pt.parse_failed(TFile.RFile{nm, vars, cols, pg, cd, io}, TFile.Missing{t <> ts}, pt.read(nm, vars, cols, pg, cd, io, t, ts, ok, miss))
