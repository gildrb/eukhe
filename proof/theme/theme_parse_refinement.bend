# eukhe: the proof of LAW theme_parse_refinement: an unset refinement
# token fills from the table of the background's mode (PP.pp.mode), and
# the parse's mode is that background's

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def pr.r14(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {TToken.get(cols, 14) == None{} : Maybe<&2, TFile.Val>})
  -> {Theme.th.tok(TPalette.parse(f), 14n) == Theme.th.builtin.val(Theme.th.light(TPalette.parse(f)), 14n) : Maybe<&2, TFile.Val>}:
  +b = TPalette.background(cols, pg)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 14n) == Theme.th.builtin.val(Theme.th.light(_), 14n) : Maybe<&2, TFile.Val>}
  %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, 14), None{}, u) : {Some{TPalette.or_else(TFile.Val, Some{TPalette.or_else(TFile.Val, _, TFile.Hex{TPalette.at(TPalette.defaults(Co.light(b)), 14n)})}, TFile.Dflt{})} == Theme.th.builtin.val(Co.light(b), 14n) : Maybe<&2, TFile.Val>}
  PP.pp.mode(Co.light(b), 14n, {==}, {==})

def pr.r15(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {TToken.get(cols, 15) == None{} : Maybe<&2, TFile.Val>})
  -> {Theme.th.tok(TPalette.parse(f), 15n) == Theme.th.builtin.val(Theme.th.light(TPalette.parse(f)), 15n) : Maybe<&2, TFile.Val>}:
  +b = TPalette.background(cols, pg)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 15n) == Theme.th.builtin.val(Theme.th.light(_), 15n) : Maybe<&2, TFile.Val>}
  %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, 15), None{}, u) : {Some{TPalette.or_else(TFile.Val, Some{TPalette.or_else(TFile.Val, _, TFile.Hex{TPalette.at(TPalette.defaults(Co.light(b)), 15n)})}, TFile.Dflt{})} == Theme.th.builtin.val(Co.light(b), 15n) : Maybe<&2, TFile.Val>}
  PP.pp.mode(Co.light(b), 15n, {==}, {==})

def Theme.theme_parse_refinement(f, nm, cols, pg, cd, io, h):
  +e = PP.pp.painted(f, nm, cols, pg, cd, io, h)
  (u => pr.r14(f, cols, pg, cd, io, e, u), u => pr.r15(f, cols, pg, cd, io, e, u))
