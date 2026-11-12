# eukhe: the proof of LAW theme_read_first_error
# The entries before e read, so the reader's fold carries on to e, whose
# fault (the reader's entry is the laws' fault: LA.pt.entry_bad) stops it
# whatever follows; a file that reads to a fault is rejected with it.

import Base
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.cons_stuck(+vars: List<&2, TFile.Var>, x: TFile.REnt, -f: TFile.Fault, hg: {Theme.th.none(Theme.th.fault(vars, x)) == True{} : Bool}) -> {TReader.ents.cons(TReader.entry(vars, x), TReader.Stuck{f}) == TReader.Stuck{f} : TReader.Ents}:
  %Equal.sym(TReader.EntR, TReader.entry(vars, x), TReader.Good{Theme.th.ent(vars, x)}, LA.pt.entry_good(vars, x, hg)) : {TReader.ents.cons(_, TReader.Stuck{f}) == TReader.Stuck{f} : TReader.Ents}
  {==}

def pt.ents_first(+vars: List<&2, TFile.Var>, +pre: List<&2, TFile.REnt>, +e: TFile.REnt, +post: List<&2, TFile.REnt>, +f: TFile.Fault, +ok: {Theme.th.clean(vars, pre) == True{} : Bool}, +bad: {Theme.th.fault(vars, e) == Some{f} : Maybe<&2, TFile.Fault>})
  -> {TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, pre, e <> post)) == TReader.Stuck{f} : TReader.Ents}:
  match pre:
    case Nil{}:
      %Equal.sym(TReader.EntR, TReader.entry(vars, e), TReader.Bad{f}, LA.pt.entry_bad(vars, e, f, bad)) : {TReader.ents.cons(_, TReader.ents(TChase.index(vars), post)) == TReader.Stuck{f} : TReader.Ents}
      {==}
    case Con{+x, rest}:
      +hg = LA.themes.pt.and_l(Theme.th.none(Theme.th.fault(vars, x)), Theme.th.clean(vars, rest), ok)
      +ih = pt.ents_first(vars, rest, e, post, f, LA.themes.pt.and_r(Theme.th.none(Theme.th.fault(vars, x)), Theme.th.clean(vars, rest), ok), bad)
      %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, rest, e <> post)), TReader.Stuck{f}, ih) : {TReader.ents.cons(TReader.entry(vars, x), _) == TReader.Stuck{f} : TReader.Ents}
      pt.cons_stuck(vars, x, f, hg)

def pt.read(+nm: String, +vars: List<&2, TFile.Var>, +pre: List<&2, TFile.REnt>, +e: TFile.REnt, +post: List<&2, TFile.REnt>, +pg: Maybe<&2, TFile.Json>, +cd: Maybe<&2, TFile.Json>, +io: Maybe<&2, TFile.Json>, +f: TFile.Fault, +ok: {Theme.th.clean(vars, pre) == True{} : Bool}, +bad: {Theme.th.fault(vars, e) == Some{f} : Maybe<&2, TFile.Fault>})
  -> {TReader.read(TFile.RFile{nm, vars, List.append(&2, TFile.REnt, pre, e <> post), pg, cd, io}) == TReader.Failed{f} : TReader.Read}:
  %Equal.sym(TReader.Ents, TReader.ents(TChase.index(vars), List.append(&2, TFile.REnt, pre, e <> post)), TReader.Stuck{f}, pt.ents_first(vars, pre, e, post, f, ok, bad)) : {TReader.read.cols(nm, TChase.index(vars), _, pg, cd, io) == TReader.Failed{f} : TReader.Read}
  {==}

def Theme.theme_read_first_error(nm, vars, pre, e, post, pg, cd, io, f, ok, bad):
  LA.pt.parse_failed(TFile.RFile{nm, vars, List.append(&2, TFile.REnt, pre, e <> post), pg, cd, io}, f, pt.read(nm, vars, pre, e, post, pg, cd, io, f, ok, bad))
