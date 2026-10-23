# eukhe: the proof of LAW theme_fill_required

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base.bend as LA

def pt.fill_req(k: TToken.Role, +cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +t: U32, h: {TReader.required.k(k) == True{} : Bool}) -> {TPalette.fill.k(k, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}:
  match k:
    case TToken.Req{}:
      {==}
    case TToken.MdBody{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.MdBody{}, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}, h)
    case TToken.RefHeader{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.RefHeader{}, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}, h)
    case TToken.RefSummary{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.RefSummary{}, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}, h)
    case TToken.Background{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.Background{}, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}, h)
    case TToken.Foreground{}:
      LA.themes.pt.absurdF({TPalette.fill.k(TToken.Foreground{}, cols, bg, t) == TToken.get(cols, t) : Maybe<&2, TFile.Val>}, h)

def Theme.theme_fill_required(cols, bg, t, r):
  pt.fill_req(TToken.kind(t), cols, bg, t, r)
