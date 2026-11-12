# eukhe: the proof of LAW theme_parse_md: mdBody unset fills from text's
# entry, which is text's own value

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def pm.md(+f: TFile.RFile, +nm: String, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}, u: {TToken.get(cols, 18) == None{} : Maybe<&2, TFile.Val>})
  -> {Theme.th.tok(TPalette.parse(f), 18n) == Theme.th.tok(TPalette.parse(f), 9n) : Maybe<&2, TFile.Val>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), PP.pp.painted(f, nm, cols, pg, cd, io, h)) : {Theme.th.tok(_, 18n) == Theme.th.tok(_, 9n) : Maybe<&2, TFile.Val>}
  %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(cols, 18), None{}, u) : {Some{TPalette.or_else(TFile.Val, TPalette.or(TFile.Val, _, TToken.get(cols, 9)), TFile.Dflt{})} == Some{TPalette.or_else(TFile.Val, TToken.get(cols, 9), TFile.Dflt{})} : Maybe<&2, TFile.Val>}
  {==}

def Theme.theme_parse_md(f, nm, cols, pg, cd, io, h, u):
  pm.md(f, nm, cols, pg, cd, io, h, u)
