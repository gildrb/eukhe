# eukhe: the proof of LAW theme_tok_get_one: the key test decides the pick

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tgo.hit(+k: U32, +v: TFile.Val, +t: U32, e: {U32.is_eq(k, t) == True{} : Bool}) -> {TToken.get([TFile.Ent{k, v}], t) == Some{v} : Maybe<&2, TFile.Val>}:
  %Equal.sym(Bool, U32.is_eq(k, t), True{}, e) : {TToken.get.pick(_, v, None{}) == Some{v} : Maybe<&2, TFile.Val>}
  {==}

def tgo.miss(+k: U32, +v: TFile.Val, +t: U32, e: {U32.is_eq(k, t) == False{} : Bool}) -> {TToken.get([TFile.Ent{k, v}], t) == None{} : Maybe<&2, TFile.Val>}:
  %Equal.sym(Bool, U32.is_eq(k, t), False{}, e) : {TToken.get.pick(_, v, None{}) == None{} : Maybe<&2, TFile.Val>}
  {==}

def ThemeModel.theme_tok_get_one(k, v, t):
  +w = v
  (e => tgo.hit(k, w, t, e), e => tgo.miss(k, w, t, e))
