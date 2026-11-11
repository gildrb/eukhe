# eukhe: the proof of LAW theme_parse_foreground: the foreground fills
# from the color its written value paints (PP.pp.conc), else from the
# table of the background's mode (PP.pp.mode)

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def pf.own(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, +c: Co.Rgb, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {Theme.th.paints(TToken.get(cols, 58)) == Some{c} : Maybe<&2, Co.Rgb>})
  -> {Theme.th.tok(TPalette.parse(f), 58n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}:
  +b = TPalette.background(cols, pg)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 58n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}
  %PP.pp.conc(TToken.get(cols, 58), Some{c}, u) : {Some{TPalette.or_else(TFile.Val, Some{TFile.Hex{TPalette.or_else(Co.Rgb, _, TPalette.at(TPalette.defaults(Co.light(b)), 58n))}}, TFile.Dflt{})} == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}
  {==}

def pf.dflt(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {Theme.th.paints(TToken.get(cols, 58)) == None{} : Maybe<&2, Co.Rgb>})
  -> {Theme.th.tok(TPalette.parse(f), 58n) == Theme.th.builtin.val(Theme.th.light(TPalette.parse(f)), 58n) : Maybe<&2, TFile.Val>}:
  +b = TPalette.background(cols, pg)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 58n) == Theme.th.builtin.val(Theme.th.light(_), 58n) : Maybe<&2, TFile.Val>}
  %PP.pp.conc(TToken.get(cols, 58), None{}, u) : {Some{TPalette.or_else(TFile.Val, Some{TFile.Hex{TPalette.or_else(Co.Rgb, _, TPalette.at(TPalette.defaults(Co.light(b)), 58n))}}, TFile.Dflt{})} == Theme.th.builtin.val(Co.light(b), 58n) : Maybe<&2, TFile.Val>}
  PP.pp.mode(Co.light(b), 58n, {==}, {==})

def Theme.theme_parse_foreground(f, nm, cols, pg, cd, io, c, h):
  +e = PP.pp.painted(f, nm, cols, pg, cd, io, h)
  (u => pf.own(f, cols, pg, cd, io, c, e, u), u => pf.dflt(f, cols, pg, cd, io, e, u))
