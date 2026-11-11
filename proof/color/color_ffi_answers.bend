# eukhe: the proof of LAW color_ffi_answers
# The colors of a request read back one by one (LCo.ce.list_rt: the
# wire's round trips, each channel within 255), and the reply writers
# write what the laws spell (LCo.ce.idxs, LCo.ce.lights_w, cp.table).
# The palette: the entry writes it from its parts (FCo.put_table: the 16
# ANSI colors, the cube one red plane at a time, the grays); the law
# spells it index by index over Co.ansi256. The spelling of a + b indices
# is that of a, then that of b from where a stops (cp.join, by induction
# on a), so the two agree part by part, each part its own closed check
# (the whole palette as one closed check runs --verdict out of fuel).

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/color/entry.bend as Color
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LCo

# The palette
# -----------

# the index k steps after i
def cp.skip(k: Nat, +i: U32) -> U32:
  match k:
    case 0n:
      i
    case 1n+m:
      cp.skip(m, (i + 1 : U32))

# the spelling of a indices, then of b from where they stop, is the
# spelling of a + b indices
def cp.split(a: Nat, -b: Nat, +i: U32, -rest: String) -> {Color.co_spell_table(a, i, Color.co_spell_table(b, cp.skip(a, i), rest)) == Color.co_spell_table(Nat.add(a, b), i, rest) : String}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %cp.split(p, b, (i + 1 : U32), rest) : {Color.co_spell_rgb(Co.ansi256(i), Color.co_spell_table(p, (i + 1 : U32), Color.co_spell_table(b, cp.skip(p, (i + 1 : U32)), rest))) == Color.co_spell_rgb(Co.ansi256(i), _) : String}
      {==}

# the same, with the sum n and the index j named
def cp.join(+a: Nat, +b: Nat, +n: Nat, +i: U32, +j: U32, -rest: String, hn: {Nat.add(a, b) == n : Nat}, hj: {cp.skip(a, i) == j : U32}) -> {Color.co_spell_table(a, i, Color.co_spell_table(b, j, rest)) == Color.co_spell_table(n, i, rest) : String}:
  %hn : {Color.co_spell_table(a, i, Color.co_spell_table(b, j, rest)) == Color.co_spell_table(_, i, rest) : String}
  %hj : {Color.co_spell_table(a, i, Color.co_spell_table(b, _, rest)) == Color.co_spell_table(Nat.add(a, b), i, rest) : String}
  cp.split(a, b, i, rest)

# the parts, each a closed check: indices 0-15, the cube's six red planes
# (16-51, 52-87, 88-123, 124-159, 160-195, 196-231), the grays (232-255)
def cp.lo(rest: String) -> {FCo.put_rgbs(Co.ansi16(), rest) == Color.co_spell_table(16n, 0, rest) : String}:
  {==}

def cp.c0(rest: String) -> {FCo.put_cube.g(0, Co.levels(), rest) == Color.co_spell_table(36n, 16, rest) : String}:
  {==}

def cp.c1(rest: String) -> {FCo.put_cube.g(95, Co.levels(), rest) == Color.co_spell_table(36n, 52, rest) : String}:
  {==}

def cp.c2(rest: String) -> {FCo.put_cube.g(135, Co.levels(), rest) == Color.co_spell_table(36n, 88, rest) : String}:
  {==}

def cp.c3(rest: String) -> {FCo.put_cube.g(175, Co.levels(), rest) == Color.co_spell_table(36n, 124, rest) : String}:
  {==}

def cp.c4(rest: String) -> {FCo.put_cube.g(215, Co.levels(), rest) == Color.co_spell_table(36n, 160, rest) : String}:
  {==}

def cp.c5(rest: String) -> {FCo.put_cube.g(255, Co.levels(), rest) == Color.co_spell_table(36n, 196, rest) : String}:
  {==}

def cp.gr(rest: String) -> {FCo.put_grays(Co.grays(), rest) == Color.co_spell_table(24n, 232, rest) : String}:
  {==}

# the entry's palette is the law's: the spelling split at the parts'
# bounds, then each part replaced by the entry's writer of it
def cp.table(+rest: String) -> {FCo.put_table(rest) == Color.co_spell_table(256n, 0, rest) : String}:
  +g = FCo.put_grays(Co.grays(), rest)
  +c5 = FCo.put_cube.g(255, Co.levels(), g)
  +c4 = FCo.put_cube.g(215, Co.levels(), c5)
  +c3 = FCo.put_cube.g(175, Co.levels(), c4)
  +c2 = FCo.put_cube.g(135, Co.levels(), c3)
  +c1 = FCo.put_cube.g(95, Co.levels(), c2)
  +c0 = FCo.put_cube.g(0, Co.levels(), c1)
  %cp.join(16n, 240n, 256n, 0, 16, rest, {==}, {==}) : {FCo.put_table(rest) == _ : String}
  %cp.join(36n, 204n, 240n, 16, 52, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, _) : String}
  %cp.join(36n, 168n, 204n, 52, 88, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, _)) : String}
  %cp.join(36n, 132n, 168n, 88, 124, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, _))) : String}
  %cp.join(36n, 96n, 132n, 124, 160, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, _)))) : String}
  %cp.join(36n, 60n, 96n, 160, 196, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, Color.co_spell_table(36n, 124, _))))) : String}
  %cp.join(36n, 24n, 60n, 196, 232, rest, {==}, {==}) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, Color.co_spell_table(36n, 124, Color.co_spell_table(36n, 160, _)))))) : String}
  %cp.gr(rest) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, Color.co_spell_table(36n, 124, Color.co_spell_table(36n, 160, Color.co_spell_table(36n, 196, _))))))) : String}
  %cp.c5(g) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, Color.co_spell_table(36n, 124, Color.co_spell_table(36n, 160, _)))))) : String}
  %cp.c4(c5) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, Color.co_spell_table(36n, 124, _))))) : String}
  %cp.c3(c4) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, Color.co_spell_table(36n, 88, _)))) : String}
  %cp.c2(c3) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, Color.co_spell_table(36n, 52, _))) : String}
  %cp.c1(c2) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, Color.co_spell_table(36n, 16, _)) : String}
  %cp.c0(c1) : {FCo.put_table(rest) == Color.co_spell_table(16n, 0, _) : String}
  %cp.lo(c0) : {FCo.put_table(rest) == _ : String}
  {==}

def ca.quantize(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Quantize{cs}) == True{} : Bool}) -> {FCo.ffi(Color.co_spell_req(FCo.Quantize{cs}, "")) == Color.co_spell_answer(FCo.Quantize{cs}) : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, "", hl, hr) : {FCo.run(FCo.get_quantize(_)) == Color.co_spell_answer(FCo.Quantize{cs}) : String}
  %LCo.ce.idxs(cs, "") : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_idxs.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
  {==}

def ca.lights(+cs: List<&2, Co.Rgb>, +fits: {Color.co_fits(FCo.Lights{cs}) == True{} : Bool}) -> {FCo.ffi(Color.co_spell_req(FCo.Lights{cs}, "")) == Color.co_spell_answer(FCo.Lights{cs}) : String}:
  +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  +hr = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)), Color.co_fits_rgbs(cs), fits)
  %LCo.ce.list_rt(cs, "", hl, hr) : {FCo.run(FCo.get_lights(_)) == Color.co_spell_answer(FCo.Lights{cs}) : String}
  %LCo.ce.lights_w(cs, "") : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_lights.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
  {==}

def ca.table() -> {FCo.ffi(Color.co_spell_req(FCo.Table{}, "")) == Color.co_spell_answer(FCo.Table{}) : String}:
  %cp.table("") : {Wr.put_nat(256n, FCo.put_table("")) == Wr.put_nat(256n, _) : String}
  {==}

def Color.color_ffi_answers(r, fits):
  match r:
    case FCo.Quantize{cs}:
      ca.quantize(cs, fits)
    case FCo.Lights{cs}:
      ca.lights(cs, fits)
    case FCo.Table{}:
      ca.table()
