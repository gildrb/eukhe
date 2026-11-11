# eukhe: the proof of LAW theme_parse_written
# Place i of the palette is token i's value (PP.pp.get over the tokens
# 0..58); token i below 57 has an ink role (a finite check, PP.pp.inks57),
# and a token of an ink role keeps the value the file writes.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/token.bend as TToken
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def pw.written(+f: TFile.RFile, +nm: String, +cols: List<&2, TFile.Ent>, +pg: Maybe<&2, Co.Rgb>, +cd: Maybe<&2, Co.Rgb>, +io: Maybe<&2, Co.Rgb>, +i: Nat, +v: TFile.Val, h: {TReader.read(f) == TReader.Loaded{TFile.Th{nm, cols, pg, cd, io}} : TReader.Read}, +lt: {Nat.is_lt(i, 57n) == True{} : Bool}, w: {TToken.get(cols, U32.from_nat(i)) == Some{v} : Maybe<&2, TFile.Val>})
  -> {Theme.th.tok(TPalette.parse(f), i) == Some{v} : Maybe<&2, TFile.Val>}:
  +b = TPalette.background(cols, pg)
  +t = U32.from_nat(i)
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), PP.pp.painted(f, nm, cols, pg, cd, io, h)) : {Theme.th.tok(_, i) == Some{v} : Maybe<&2, TFile.Val>}
  %Equal.sym(List<&2, U32>, TToken.toks(), PP.pp.upto(59n, 0n), PP.pp.toks()) : {List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, b, _)), i) == Some{v} : Maybe<&2, TFile.Val>}
  +lt59 = PP.pp.lt_succ(i, 58n, PP.pp.lt_succ(i, 57n, lt))
  %Equal.sym(Maybe<&2, TFile.Val>, List.get(&2, TFile.Val, TPalette.vals(TPalette.fill.map(cols, b, PP.pp.upto(59n, 0n))), i), Some{TPalette.or_else(TFile.Val, TPalette.fill(cols, b, t), TFile.Dflt{})}, PP.pp.get(cols, b, 59n, 0n, i, lt59)) : {_ == Some{v} : Maybe<&2, TFile.Val>}
  +hr = PP.pp.ink_at(57n, 0n, i, PP.pp.inks57(), lt)
  %Equal.sym(Maybe<&2, TFile.Val>, TPalette.fill.k(TToken.kind(t), cols, b, t), Some{v}, PP.pp.fill_ink(TToken.kind(t), cols, b, t, v, hr, w)) : {Some{TPalette.or_else(TFile.Val, _, TFile.Dflt{})} == Some{v} : Maybe<&2, TFile.Val>}
  {==}

def Theme.theme_parse_written(f, nm, cols, pg, cd, io, i, v, h, lt, w):
  pw.written(f, nm, cols, pg, cd, io, i, v, h, lt, w)
