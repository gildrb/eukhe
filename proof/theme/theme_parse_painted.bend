# eukhe: the proof of LAW theme_parse_painted

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme

def pt.own(m: Maybe<&2, TFile.Val>) -> {TPalette.declared.of(m) == Theme.th.own(m) : Maybe<&2, Co.Rgb>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          {==}
        case TFile.Idx{i}:
          {==}
        case TFile.Hex{c}:
          {==}

def Theme.theme_parse_painted(f, nm, cols, pg, cd, io, h):
  +rhs = {TPalette.Painted{TPalette.vals(TPalette.palette(TFile.Th{nm, cols, pg, cd, io})), TPalette.light(TFile.Th{nm, cols, pg, cd, io}), Theme.th.own(TToken.get(cols, 57)), pg, cd, io} : TPalette.Parsed}
  %Equal.sym(TReader.Read, TReader.read(f), TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}}, h) : {TPalette.parse.of(_) == rhs : TPalette.Parsed}
  %Equal.sym(Maybe<&2, Co.Rgb>, TPalette.declared.of(TToken.get(cols, 57)), Theme.th.own(TToken.get(cols, 57)), pt.own(TToken.get(cols, 57))) : {TPalette.Painted{TPalette.vals(TPalette.palette.go(cols, pg)), Co.light(TPalette.background(cols, pg)), _, pg, cd, io} == rhs : TPalette.Parsed}
  {==}
