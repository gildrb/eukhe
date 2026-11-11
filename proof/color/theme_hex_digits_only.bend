# eukhe: the proof of LAW theme_hex_digits_only: the first of the six chars
# that reads as no digit leaves its channel, and so the color, unread

import Base
import ../../bend/color.bend as Co
import ../../laws/color/text.bend as Color

def thd.If(m: Maybe<&2, Co.Rgb>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# no color is not a color
def thd.none_some(-G: Type, -c: Co.Rgb, e: {None{} == Some{c} : Maybe<&2, Co.Rgb>}) -> G:
  %e : thd.If(_, G)
  Unit{}

def thd.go(m1: Maybe<&2, U32>, m2: Maybe<&2, U32>, m3: Maybe<&2, U32>, m4: Maybe<&2, U32>, m5: Maybe<&2, U32>, m6: Maybe<&2, U32>, -c: Co.Rgb, h: {Co.hex.rgb(Co.join(16, m1, m2), Co.join(16, m3, m4), Co.join(16, m5, m6)) == Some{c} : Maybe<&2, Co.Rgb>}) -> {Color.th.all_some([m1, m2, m3, m4, m5, m6]) == True{} : Bool}:
  match m1:
    case None{}:
      thd.none_some({Color.th.all_some([None{}, m2, m3, m4, m5, m6]) == True{} : Bool}, c, h)
    case Some{x1}:
      match m2:
        case None{}:
          thd.none_some({Color.th.all_some([Some{x1}, None{}, m3, m4, m5, m6]) == True{} : Bool}, c, h)
        case Some{x2}:
          match m3:
            case None{}:
              thd.none_some({Color.th.all_some([Some{x1}, Some{x2}, None{}, m4, m5, m6]) == True{} : Bool}, c, h)
            case Some{x3}:
              match m4:
                case None{}:
                  thd.none_some({Color.th.all_some([Some{x1}, Some{x2}, Some{x3}, None{}, m5, m6]) == True{} : Bool}, c, h)
                case Some{x4}:
                  match m5:
                    case None{}:
                      thd.none_some({Color.th.all_some([Some{x1}, Some{x2}, Some{x3}, Some{x4}, None{}, m6]) == True{} : Bool}, c, h)
                    case Some{x5}:
                      match m6:
                        case None{}:
                          thd.none_some({Color.th.all_some([Some{x1}, Some{x2}, Some{x3}, Some{x4}, Some{x5}, None{}]) == True{} : Bool}, c, h)
                        case Some{x6}:
                          {==}

def Color.theme_hex_digits_only(a1, a2, a3, a4, a5, a6, c, h):
  thd.go(Co.hexd(a1), Co.hexd(a2), Co.hexd(a3), Co.hexd(a4), Co.hexd(a5), Co.hexd(a6), c, h)
