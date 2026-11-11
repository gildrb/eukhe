# eukhe: the proof of LAW theme_parse_mode: the background token of the
# parse paints the background the file completes to, and the parse's mode
# is that background's

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def pmo.unhex(m: Maybe<&2, TFile.Val>) -> Co.Rgb:
  match m:
    case None{}:
      Co.Rgb{0, 0, 0}
    case Some{v}:
      match v:
        case TFile.Hex{x}:
          x
        case TFile.Dflt{}:
          Co.Rgb{0, 0, 0}
        case TFile.Idx{i}:
          Co.Rgb{0, 0, 0}

def pmo.mode(+f: TFile.RFile, +nm: String, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, +c: Co.Rgb, h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}, hb: {Theme.th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>})
  -> {Theme.th.light(TPalette.parse(f)) == Co.light(c) : Bool}:
  +p = PP.pp.parsed(cols, pg, cd, io)
  +e = PP.pp.painted(f, nm, cols, pg, cd, io, h)
  +x = Equal.cong(TPalette.Parsed, Maybe<&2, TFile.Val>, q => Theme.th.tok(q, 57n), TPalette.parse(f), p, e)
  +hp = Equal.trans(Maybe<&2, TFile.Val>, Theme.th.tok(p, 57n), Theme.th.tok(TPalette.parse(f), 57n), Some{TFile.Hex{c}}, Equal.sym(Maybe<&2, TFile.Val>, Theme.th.tok(TPalette.parse(f), 57n), Theme.th.tok(p, 57n), x), hb)
  +bc = Equal.cong(Maybe<&2, TFile.Val>, Co.Rgb, m => pmo.unhex(m), Theme.th.tok(p, 57n), Some{TFile.Hex{c}}, hp)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), p, e) : {Theme.th.light(_) == Co.light(c) : Bool}
  Equal.cong(Co.Rgb, Bool, y => Co.light(y), pmo.unhex(Theme.th.tok(p, 57n)), c, bc)

def Theme.theme_parse_mode(f, nm, cols, pg, cd, io, c, h, b):
  pmo.mode(f, nm, cols, pg, cd, io, c, h, b)
