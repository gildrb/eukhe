# eukhe: the proof of LAW theme_fill_required

import Base
import ../../bend/theme.bend as T
import ../../bend/color.bend as Co
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pt.fill_req(k: T.Role, +cols: List<&2, T.Ent>, +bg: Co.Rgb, +t: U32, h: {T.required.k(k) == True{} : Bool}) -> {T.fill.k(k, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}:
  match k:
    case T.Req{}:
      {==}
    case T.MdBody{}:
      LA.themes.pt.absurdF({T.fill.k(T.MdBody{}, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}, h)
    case T.RefHeader{}:
      LA.themes.pt.absurdF({T.fill.k(T.RefHeader{}, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}, h)
    case T.RefSummary{}:
      LA.themes.pt.absurdF({T.fill.k(T.RefSummary{}, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}, h)
    case T.Background{}:
      LA.themes.pt.absurdF({T.fill.k(T.Background{}, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}, h)
    case T.Foreground{}:
      LA.themes.pt.absurdF({T.fill.k(T.Foreground{}, cols, bg, t) == T.get(cols, t) : Maybe<&2, T.Val>}, h)

def Laws.theme_fill_required(cols, bg, t, r):
  pt.fill_req(T.kind(t), cols, bg, t, r)
