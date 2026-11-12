# eukhe: the proof of LAW theme_parse_background: the background token
# paints the background the file completes to, whose fallbacks are
# PP.pp.bg_own, pp.bg_page, pp.bg_user, pp.bg_dflt

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

# the background token of the parse is the background, as a color
def pb.at(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, -c: Co.Rgb, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, hc: {TPalette.background(cols, pg) == c : Co.Rgb})
  -> {Theme.th.tok(TPalette.parse(f), 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 57n) == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}
  %Equal.sym(Co.Rgb, TPalette.background(cols, pg), c, hc) : {Some{TFile.Hex{_}} == Some{TFile.Hex{c}} : Maybe<&2, TFile.Val>}
  {==}

def pb.dflt(+f: TFile.RFile, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, e: {TPalette.parse(f) == PP.pp.parsed(cols, pg, cd, io) : TPalette.Parsed}, h1: {Theme.th.paints(TToken.get(cols, 57)) == None{} : Maybe<&2, Co.Rgb>}, h2: {pg == None{} : Maybe<&2, Co.Rgb>}, h3: {Theme.th.paints(TToken.get(cols, 49)) == None{} : Maybe<&2, Co.Rgb>})
  -> {Theme.th.tok(TPalette.parse(f), 57n) == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}:
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), e) : {Theme.th.tok(_, 57n) == Theme.th.builtin.val(False{}, 57n) : Maybe<&2, TFile.Val>}
  PP.pp.bg_dflt(cols, pg, h1, h2, h3)

def Theme.theme_parse_background(f, nm, cols, pg, cd, io, c, h):
  +e = PP.pp.painted(f, nm, cols, pg, cd, io, h)
  (h1 => pb.at(f, cols, pg, cd, io, c, e, PP.pp.bg_own(cols, pg, c, h1)), (h1 => h2 => pb.at(f, cols, pg, cd, io, c, e, PP.pp.bg_page(cols, pg, c, h1, h2)), (h1 => h2 => h3 => pb.at(f, cols, pg, cd, io, c, e, PP.pp.bg_user(cols, pg, c, h1, h2, h3)), h1 => h2 => h3 => pb.dflt(f, cols, pg, cd, io, e, h1, h2, h3))))
