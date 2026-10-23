# eukhe: the proof of LAW theme_parse_painted

import Base
import ../../bend/color.bend as Co
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme

def pt.own(m: Maybe<&2, T.Val>) -> {T.declared.of(m) == Theme.th.own(m) : Maybe<&2, Co.Rgb>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case T.Dflt{}:
          {==}
        case T.Idx{i}:
          {==}
        case T.Hex{c}:
          {==}

def Theme.theme_parse_painted(f, nm, cols, pg, cd, io, h):
  +rhs = {T.Painted{T.vals(T.palette(T.Th{nm, cols, pg, cd, io})), T.light(T.Th{nm, cols, pg, cd, io}), Theme.th.own(T.get(cols, 57)), pg, cd, io} : T.Parsed}
  %Equal.sym(T.Read, T.read(f), T.Loaded{T.Th{nm, cols, pg, cd, io}}, h) : {T.parse.of(_) == rhs : T.Parsed}
  %Equal.sym(Maybe<&2, Co.Rgb>, T.declared.of(T.get(cols, 57)), Theme.th.own(T.get(cols, 57)), pt.own(T.get(cols, 57))) : {T.Painted{T.vals(T.palette.go(cols, pg)), Co.light(T.background(cols, pg)), _, pg, cd, io} == rhs : T.Parsed}
  {==}
