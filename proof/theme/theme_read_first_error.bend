# eukhe: the proof of LAW theme_read_first_error

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.cons_stuck(r: TReader.EntR, -f: TFile.Fault, hg: {Theme.th.good(r) == True{} : Bool}) -> {TReader.ents.cons(r, TReader.Stuck{f}) == TReader.Stuck{f} : TReader.Ents}:
  match r:
    case TReader.Good{e}:
      {==}
    case TReader.Bad{x}:
      LA.themes.pt.absurdF({TReader.ents.cons(TReader.Bad{x}, TReader.Stuck{f}) == TReader.Stuck{f} : TReader.Ents}, hg)

def pt.ents_first(+vars: List<&2, TFile.Var>, +pre: List<&2, TFile.REnt>, +e: TFile.REnt, +post: List<&2, TFile.REnt>, +f: TFile.Fault, +ok: {Theme.th.clean(vars, pre) == True{} : Bool}, +bad: {TReader.entry(vars, e) == TReader.Bad{f} : TReader.EntR})
  -> {TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, pre, e <> post)) == TReader.Stuck{f} : TReader.Ents}:
  match pre:
    case Nil{}:
      %Equal.sym(TReader.EntR, TReader.entry(vars, e), TReader.Bad{f}, bad) : {TReader.ents.cons(_, TReader.ents(TChase.index(vars), post)) == TReader.Stuck{f} : TReader.Ents}
      {==}
    case Con{+x, rest}:
      +hg = LA.themes.pt.and_l(Theme.th.good(TReader.entry(vars, x)), Theme.th.clean(vars, rest), ok)
      +ih = pt.ents_first(vars, rest, e, post, f, LA.themes.pt.and_r(Theme.th.good(TReader.entry(vars, x)), Theme.th.clean(vars, rest), ok), bad)
      %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, rest, e <> post)), TReader.Stuck{f}, ih) : {TReader.ents.cons(TReader.entry(vars, x), _) == TReader.Stuck{f} : TReader.Ents}
      pt.cons_stuck(TReader.entry(vars, x), f, hg)

def Theme.theme_read_first_error(nm, vars, pre, e, post, pg, cd, io, f, ok, bad):
  %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, pre, e <> post)), TReader.Stuck{f}, pt.ents_first(vars, pre, e, post, f, ok, bad)) : {TReader.read.cols(nm, TChase.index(vars), _, pg, cd, io) == TReader.Failed{f} : TReader.Read}
  {==}
