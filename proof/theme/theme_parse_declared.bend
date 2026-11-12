# eukhe: the proof of LAW theme_parse_declared: the parse reports the
# file's background entry when it is #rrggbb, and the export backgrounds
# as read

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base.bend as LA
import ./base/parse.bend as PP

def pd.hex(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, +c: Co.Rgb, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {TToken.get(cols, 57) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>})
  -> {Theme.th.declared(TPalette.parse(f)) == Some{c} : Maybe<&2, Co.Rgb>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.declared(_) == Some{c} : Maybe<&2, Co.Rgb>}
  %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, 57), Some{TFile.Hex{c}}, u) : {TPalette.declared.of(_) == Some{c} : Maybe<&2, Co.Rgb>}
  {==}

def pd.of(m: Maybe<&2, TFile.Val>, h: {Theme.th.hexed(m) == False{} : Bool}) -> {TPalette.declared.of(m) == None{} : Maybe<&2, Co.Rgb>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          {==}
        case TFile.Idx{i}:
          {==}
        case TFile.Hex{x}:
          LA.themes.pt.absurdT({TPalette.declared.of(Some{TFile.Hex{x}}) == None{} : Maybe<&2, Co.Rgb>}, h)

def pd.none(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, u: {Theme.th.hexed(TToken.get(cols, 57)) == False{} : Bool})
  -> {Theme.th.declared(TPalette.parse(f)) == None{} : Maybe<&2, Co.Rgb>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.declared(_) == None{} : Maybe<&2, Co.Rgb>}
  pd.of(TToken.get(cols, 57), u)

def pd.exports(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed})
  -> {Theme.th.exports(TPalette.parse(f)) == [pg, cd, io] : List<&2, Maybe<&2, Co.Rgb>>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.exports(_) == [pg, cd, io] : List<&2, Maybe<&2, Co.Rgb>>}
  {==}

def Theme.theme_parse_declared(f, nm, cols, pg, cd, io, c, h):
  +e = PP.pp.painted(f, nm, cols, pg, cd, io, h)
  (u => pd.hex(f, cols, pg, cd, io, c, e, u), (u => pd.none(f, cols, pg, cd, io, e, u), pd.exports(f, cols, pg, cd, io, e)))
