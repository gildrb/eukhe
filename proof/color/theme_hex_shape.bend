# eukhe: the proof of LAW theme_hex_shape

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ../base/logic/logic.bend as LLogicLogic

def pt.sharp_some(+b: Bool, +m: Maybe<&2, Co.Rgb>, -c: Co.Rgb, h: {Co.hex.sharp(b, m) == Some{c} : Maybe<&2, Co.Rgb>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)

def Color.theme_hex_shape(s, c, h):
  match s:
    case SNil{}:
      LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
    case SCon{h0, s1}:
      match s1:
        case SNil{}:
          LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
        case SCon{a1, s2}:
          match s2:
            case SNil{}:
              LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
            case SCon{a2, s3}:
              match s3:
                case SNil{}:
                  LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
                case SCon{a3, s4}:
                  match s4:
                    case SNil{}:
                      LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
                    case SCon{a4, s5}:
                      match s5:
                        case SNil{}:
                          LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
                        case SCon{a5, s6}:
                          match s6:
                            case SNil{}:
                              LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
                            case SCon{a6, s7}:
                              match s7:
                                case SNil{}:
                                  pt.sharp_some(Char.is_eq(h0, '#'), Co.hex.rgb(Co.join(16, Co.hexd(a1), Co.hexd(a2)), Co.join(16, Co.hexd(a3), Co.hexd(a4)), Co.join(16, Co.hexd(a5), Co.hexd(a6))), c, h)
                                case SCon{a7, s8}:
                                  LLogicLogic.themes.pt.none_some({False{} == True{} : Bool}, Co.Rgb, c, h)
