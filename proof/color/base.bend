# eukhe: lemmas the proofs of area color share: the entry's reader answers
# what the laws' reader answers on every input (one lemma per stage, each a
# case split on the stage's input), the entry reads back what the laws'
# spellers write, and its reply writers write what the laws' spellers
# write.

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/color.bend as Color
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/wire.bend as LWire
import ../wire/wire_u32_round_trip.bend as PWireU32RoundTrip

# Logic
# -----

def ce.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def ce.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : ce.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def ce.ch_in(ok: Bool, x: U32, s: String) -> {Color.co_read_ch.in(ok, x, s) == FCo.get_ch.in(ok, x, s) : Wr.Dec<U32>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def ce.ch(r: Wr.Dec<U32>) -> {Color.co_read_ch(r) == FCo.get_ch(r) : Wr.Dec<U32>}:
  match r:
    case Wr.Got{+x, s}:
      ce.ch_in(U32.is_le(x, 255), x, s)
    case Wr.Bad{}:
      {==}

def ce.rgb_b(r: U32, g: U32, d: Wr.Dec<U32>) -> {Color.co_read_rgb.b(r, g, d) == FCo.get_rgb.b(r, g, d) : Wr.Dec<Co.Rgb>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ce.rgb_g(+r: U32, d: Wr.Dec<U32>) -> {Color.co_read_rgb.g(r, d) == FCo.get_rgb.g(r, d) : Wr.Dec<Co.Rgb>}:
  match d:
    case Wr.Got{+g, +s}:
      %ce.ch(Wr.get_u32(s)) : {Color.co_read_rgb.b(r, g, Color.co_read_ch(Wr.get_u32(s))) == FCo.get_rgb.b(r, g, _) : Wr.Dec<Co.Rgb>}
      ce.rgb_b(r, g, Color.co_read_ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      {==}

def ce.rgb_r(d: Wr.Dec<U32>) -> {Color.co_read_rgb.r(d) == FCo.get_rgb.r(d) : Wr.Dec<Co.Rgb>}:
  match d:
    case Wr.Got{+r, +s}:
      %ce.ch(Wr.get_u32(s)) : {Color.co_read_rgb.g(r, Color.co_read_ch(Wr.get_u32(s))) == FCo.get_rgb.g(r, _) : Wr.Dec<Co.Rgb>}
      ce.rgb_g(r, Color.co_read_ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      {==}

def ce.rgb(+s: String) -> {Color.co_read_rgb(s) == FCo.get_rgb(s) : Wr.Dec<Co.Rgb>}:
  %ce.ch(Wr.get_u32(s)) : {Color.co_read_rgb.r(Color.co_read_ch(Wr.get_u32(s))) == FCo.get_rgb.r(_) : Wr.Dec<Co.Rgb>}
  ce.rgb_r(Color.co_read_ch(Wr.get_u32(s)))

def ce.rgbs_cons(c: Co.Rgb, r: Wr.Dec<List<&2, Co.Rgb>>) -> {Color.co_read_rgbs.cons(c, r) == FCo.get_rgbs.cons(c, r) : Wr.Dec<List<&2, Co.Rgb>>}:
  match r:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ce.rgbs_go(n: Nat, cur: Wr.Dec<Co.Rgb>) -> {Color.co_read_rgbs.go(n, cur) == FCo.get_rgbs.go(n, cur) : Wr.Dec<List<&2, Co.Rgb>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{c, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+c, +s}:
          %ce.rgb(s) : {Color.co_read_rgbs.cons(c, Color.co_read_rgbs.go(m, Color.co_read_rgb(s))) == FCo.get_rgbs.cons(c, FCo.get_rgbs.go(m, _)) : Wr.Dec<List<&2, Co.Rgb>>}
          %ce.rgbs_go(m, Color.co_read_rgb(s)) : {Color.co_read_rgbs.cons(c, Color.co_read_rgbs.go(m, Color.co_read_rgb(s))) == FCo.get_rgbs.cons(c, _) : Wr.Dec<List<&2, Co.Rgb>>}
          ce.rgbs_cons(c, Color.co_read_rgbs.go(m, Color.co_read_rgb(s)))
        case Wr.Bad{}:
          {==}

def ce.rgbs(r: Wr.Dec<Nat>) -> {Color.co_read_rgbs(r) == FCo.get_rgbs(r) : Wr.Dec<List<&2, Co.Rgb>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %ce.rgb(s) : {Color.co_read_rgbs.go(m, Color.co_read_rgb(s)) == FCo.get_rgbs.go(m, _) : Wr.Dec<List<&2, Co.Rgb>>}
          ce.rgbs_go(m, Color.co_read_rgb(s))
    case Wr.Bad{}:
      {==}

def ce.quantize(r: Wr.Dec<List<&2, Co.Rgb>>) -> {Color.co_read_quantize(r) == FCo.get_quantize(r) : Wr.Dec<FCo.Req>}:
  match r:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ce.lights(r: Wr.Dec<List<&2, Co.Rgb>>) -> {Color.co_read_lights(r) == FCo.get_lights(r) : Wr.Dec<FCo.Req>}:
  match r:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ce.req_tag(t: Nat, +s: String) -> {Color.co_read_req.tag(t, s) == FCo.get_req.tag(t, s) : Wr.Dec<FCo.Req>}:
  match t:
    case 0n:
      %ce.rgbs(Wr.get_nat(s)) : {Color.co_read_quantize(Color.co_read_rgbs(Wr.get_nat(s))) == FCo.get_quantize(_) : Wr.Dec<FCo.Req>}
      ce.quantize(Color.co_read_rgbs(Wr.get_nat(s)))
    case 1n:
      %ce.rgbs(Wr.get_nat(s)) : {Color.co_read_lights(Color.co_read_rgbs(Wr.get_nat(s))) == FCo.get_lights(_) : Wr.Dec<FCo.Req>}
      ce.lights(Color.co_read_rgbs(Wr.get_nat(s)))
    case 2n:
      {==}
    case 3n+p:
      {==}

# the entry reads every input as the laws' reader does
def ce.req(r: Wr.Dec<Nat>) -> {Color.co_read_req.go(r) == FCo.get_req.go(r) : Wr.Dec<FCo.Req>}:
  match r:
    case Wr.Got{t, s}:
      ce.req_tag(t, s)
    case Wr.Bad{}:
      {==}

# Round trips
# -----------

# a channel of at most 255 reads back, whatever follows it
def ce.ch_rt(+x: U32, +rest: String, h: {U32.is_le(x, 255) == True{} : Bool}) -> {Wr.Got{x, rest} == FCo.get_ch(Wr.get_u32(Wr.put_u32(x, rest))) : Wr.Dec<U32>}:
  %Equal.sym(Wr.Dec<U32>, Wr.get_u32(Wr.put_u32(x, rest)), Wr.Got{x, rest}, Wire.wire_u32_round_trip(x, rest)) : {Wr.Got{x, rest} == FCo.get_ch(_) : Wr.Dec<U32>}
  %Equal.sym(Bool, U32.is_le(x, 255), True{}, h) : {Wr.Got{x, rest} == FCo.get_ch.in(_, x, rest) : Wr.Dec<U32>}
  {==}

# a color the laws spell reads back, whatever follows it
def ce.rgb_rt(c: Co.Rgb, +rest: String, +h: {Color.co_fits_rgb(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FCo.get_rgb(Color.co_spell_rgb(c, rest)) : Wr.Dec<Co.Rgb>}:
  match c:
    case Co.Rgb{+r, +g, +b}:
      +hr = LLogicBool.wr_and_l(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), U32.is_le(b, 255)), h)
      +hgb = LLogicBool.wr_and_r(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), U32.is_le(b, 255)), h)
      +hg = LLogicBool.wr_and_l(U32.is_le(g, 255), U32.is_le(b, 255), hgb)
      +hb = LLogicBool.wr_and_r(U32.is_le(g, 255), U32.is_le(b, 255), hgb)
      %ce.ch_rt(r, Wr.put_u32(g, Wr.put_u32(b, rest)), hr) : {Wr.Got{Co.Rgb{r, g, b}, rest} == FCo.get_rgb.r(_) : Wr.Dec<Co.Rgb>}
      %ce.ch_rt(g, Wr.put_u32(b, rest), hg) : {Wr.Got{Co.Rgb{r, g, b}, rest} == FCo.get_rgb.g(r, _) : Wr.Dec<Co.Rgb>}
      %ce.ch_rt(b, rest, hb) : {Wr.Got{Co.Rgb{r, g, b}, rest} == FCo.get_rgb.b(r, g, _) : Wr.Dec<Co.Rgb>}
      {==}

# the colors after the first read back, the first one being c
def ce.rgbs_rt(t: List<&2, Co.Rgb>, +c: Co.Rgb, +rest: String, +h: {Color.co_fits_rgbs(c <> t) == True{} : Bool}) -> {Wr.Got{c <> t, rest} == FCo.get_rgbs.go(List.length(&2, Co.Rgb, t), FCo.get_rgb(Color.co_spell_rgb(c, Color.co_spell_rgbs.items(t, rest)))) : Wr.Dec<List<&2, Co.Rgb>>}:
  match t:
    case Nil{}:
      +hc = LLogicBool.wr_and_l(Color.co_fits_rgb(c), True{}, h)
      %ce.rgb_rt(c, rest, hc) : {Wr.Got{[c], rest} == FCo.get_rgbs.go(0n, _) : Wr.Dec<List<&2, Co.Rgb>>}
      {==}
    case +x <> +u:
      +hc = LLogicBool.wr_and_l(Color.co_fits_rgb(c), Color.co_fits_rgbs(x <> u), h)
      +ht = LLogicBool.wr_and_r(Color.co_fits_rgb(c), Color.co_fits_rgbs(x <> u), h)
      %ce.rgb_rt(c, Color.co_spell_rgb(x, Color.co_spell_rgbs.items(u, rest)), hc) : {Wr.Got{c <> x <> u, rest} == FCo.get_rgbs.go(1n+List.length(&2, Co.Rgb, u), _) : Wr.Dec<List<&2, Co.Rgb>>}
      %ce.rgbs_rt(u, x, rest, ht) : {Wr.Got{c <> x <> u, rest} == FCo.get_rgbs.cons(c, _) : Wr.Dec<List<&2, Co.Rgb>>}
      {==}

# a list of colors the laws spell reads back, whatever follows it
def ce.list_rt(cs: List<&2, Co.Rgb>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Co.Rgb, cs)) == True{} : Bool}, h: {Color.co_fits_rgbs(cs) == True{} : Bool}) -> {Wr.Got{cs, rest} == FCo.get_rgbs(Wr.get_nat(Color.co_spell_rgbs(cs, rest))) : Wr.Dec<List<&2, Co.Rgb>>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %LWire.pc.nat(1n+List.length(&2, Co.Rgb, t), Color.co_spell_rgb(c, Color.co_spell_rgbs.items(t, rest)), hl) : {Wr.Got{c <> t, rest} == FCo.get_rgbs(_) : Wr.Dec<List<&2, Co.Rgb>>}
      ce.rgbs_rt(t, c, rest, h)

# Writers
# -------

def ce.idxs(cs: List<&2, Co.Rgb>, -rest: String) -> {FCo.put_idxs.items(cs, rest) == Color.co_spell_idxs(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      %ce.idxs(t, rest) : {Wr.put_u32(Co.to256(c), FCo.put_idxs.items(t, rest)) == Wr.put_u32(Co.to256(c), _) : String}
      {==}

def ce.lights_w(cs: List<&2, Co.Rgb>, -rest: String) -> {FCo.put_lights.items(cs, rest) == Color.co_spell_lights(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      %ce.lights_w(t, rest) : {Wr.put_bool(Co.light(c), FCo.put_lights.items(t, rest)) == Wr.put_bool(Co.light(c), _) : String}
      {==}

def ce.rgb_w(c: Co.Rgb, rest: String) -> {FCo.put_rgb(c, rest) == Color.co_spell_rgb(c, rest) : String}:
  match c:
    case Co.Rgb{r, g, b}:
      {==}

def ce.table(k: Nat, +i: U32, +rest: String) -> {FCo.put_table(k, i, rest) == Color.co_spell_table(k, i, rest) : String}:
  match k:
    case 0n:
      {==}
    case 1n++m:
      %ce.table(m, (i + 1 : U32), rest) : {FCo.put_rgb(Co.ansi256(i), FCo.put_table(m, (i + 1 : U32), rest)) == Color.co_spell_rgb(Co.ansi256(i), _) : String}
      ce.rgb_w(Co.ansi256(i), FCo.put_table(m, (i + 1 : U32), rest))
