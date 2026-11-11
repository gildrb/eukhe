# eukhe: the proof of LAW color_ffi_spec
# The entry reads every input as the laws' reader does (LCo.ce.req), and
# every color that reader reads has channels of at most 255 (cfs.req, one
# lemma per stage). On such colors the entry's index is th.to256
# (color_to256_spec); for every color its light test is the spec's
# luminance above one half (color_light_spec, color_lin_spec) and its
# palette color th.ansi_any (color_ansi256_spec).

import Base
import ../../bend/color.bend as Co
import ../../bend/ffi_color.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/color/entry.bend as Color
import ../../laws/color/math.bend as ColorMath
import ../../laws/color/spec.bend as ColorSpec
import ../../spec/theme/color.bend as Cm
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LCo
import ./color_to256_spec.bend as PTo256Spec
import ./color_light_spec.bend as PLightSpec
import ./color_lin_spec.bend as PLinSpec
import ./color_ansi256_spec.bend as PAnsi256Spec
import ./color_ffi_answers.bend as PFfiAnswers

# Logic
# -----

def cfs.if_true(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def cfs.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : cfs.if_true(_, G)
  Unit{}

def cfs.and(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      cfs.absurd({Bool.and(False{}, b) == True{} : Bool}, ea)

# The reader reads only channels of at most 255
# ---------------------------------------------

def cfs.ch_ok(d: Wr.Dec<U32>) -> Bool:
  match d:
    case Wr.Got{x, s}:
      U32.is_le(x, 255)
    case Wr.Bad{}:
      True{}

def cfs.rgb_ok(d: Wr.Dec<Co.Rgb>) -> Bool:
  match d:
    case Wr.Got{c, s}:
      Color.co_fits_rgb(c)
    case Wr.Bad{}:
      True{}

def cfs.rgbs_ok(d: Wr.Dec<List<&2, Co.Rgb>>) -> Bool:
  match d:
    case Wr.Got{cs, s}:
      Color.co_fits_rgbs(cs)
    case Wr.Bad{}:
      True{}

def cfs.req_fits(r: FCo.Req) -> Bool:
  match r:
    case FCo.Quantize{cs}:
      Color.co_fits_rgbs(cs)
    case FCo.Lights{cs}:
      Color.co_fits_rgbs(cs)
    case FCo.Table{}:
      True{}

def cfs.req_ok(d: Wr.Dec<FCo.Req>) -> Bool:
  match d:
    case Wr.Got{r, s}:
      cfs.req_fits(r)
    case Wr.Bad{}:
      True{}

def cfs.ch_in(ok: Bool, x: U32, s: String, e: {U32.is_le(x, 255) == ok : Bool}) -> {cfs.ch_ok(Color.co_read_ch.in(ok, x, s)) == True{} : Bool}:
  match ok:
    case True{}:
      e
    case False{}:
      {==}

def cfs.ch(r: Wr.Dec<U32>) -> {cfs.ch_ok(Color.co_read_ch(r)) == True{} : Bool}:
  match r:
    case Wr.Got{+x, s}:
      cfs.ch_in(U32.is_le(x, 255), x, s, {==})
    case Wr.Bad{}:
      {==}

def cfs.rgb_b(+r: U32, +g: U32, d: Wr.Dec<U32>, hr: {U32.is_le(r, 255) == True{} : Bool}, hg: {U32.is_le(g, 255) == True{} : Bool}, hd: {cfs.ch_ok(d) == True{} : Bool}) -> {cfs.rgb_ok(Color.co_read_rgb.b(r, g, d)) == True{} : Bool}:
  match d:
    case Wr.Got{+b, s}:
      cfs.and(U32.is_le(r, 255), Bool.and(U32.is_le(g, 255), U32.is_le(b, 255)), hr, cfs.and(U32.is_le(g, 255), U32.is_le(b, 255), hg, hd))
    case Wr.Bad{}:
      {==}

def cfs.rgb_g(+r: U32, d: Wr.Dec<U32>, hr: {U32.is_le(r, 255) == True{} : Bool}, hd: {cfs.ch_ok(d) == True{} : Bool}) -> {cfs.rgb_ok(Color.co_read_rgb.g(r, d)) == True{} : Bool}:
  match d:
    case Wr.Got{+g, +s}:
      cfs.rgb_b(r, g, Color.co_read_ch(Wr.get_u32(s)), hr, hd, cfs.ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      {==}

def cfs.rgb_r(d: Wr.Dec<U32>, hd: {cfs.ch_ok(d) == True{} : Bool}) -> {cfs.rgb_ok(Color.co_read_rgb.r(d)) == True{} : Bool}:
  match d:
    case Wr.Got{+r, +s}:
      cfs.rgb_g(r, Color.co_read_ch(Wr.get_u32(s)), hd, cfs.ch(Wr.get_u32(s)))
    case Wr.Bad{}:
      {==}

def cfs.rgb(+s: String) -> {cfs.rgb_ok(Color.co_read_rgb(s)) == True{} : Bool}:
  cfs.rgb_r(Color.co_read_ch(Wr.get_u32(s)), cfs.ch(Wr.get_u32(s)))

def cfs.cons(+c: Co.Rgb, d: Wr.Dec<List<&2, Co.Rgb>>, hc: {Color.co_fits_rgb(c) == True{} : Bool}, hd: {cfs.rgbs_ok(d) == True{} : Bool}) -> {cfs.rgbs_ok(Color.co_read_rgbs.cons(c, d)) == True{} : Bool}:
  match d:
    case Wr.Got{cs, s}:
      cfs.and(Color.co_fits_rgb(c), Color.co_fits_rgbs(cs), hc, hd)
    case Wr.Bad{}:
      {==}

def cfs.go(n: Nat, cur: Wr.Dec<Co.Rgb>, h: {cfs.rgb_ok(cur) == True{} : Bool}) -> {cfs.rgbs_ok(Color.co_read_rgbs.go(n, cur)) == True{} : Bool}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{c, s}:
          cfs.and(Color.co_fits_rgb(c), True{}, h, {==})
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+c, +s}:
          cfs.cons(c, Color.co_read_rgbs.go(m, Color.co_read_rgb(s)), h, cfs.go(m, Color.co_read_rgb(s), cfs.rgb(s)))
        case Wr.Bad{}:
          {==}

def cfs.rgbs(d: Wr.Dec<Nat>) -> {cfs.rgbs_ok(Color.co_read_rgbs(d)) == True{} : Bool}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          cfs.go(m, Color.co_read_rgb(s), cfs.rgb(s))
    case Wr.Bad{}:
      {==}

def cfs.quantize(d: Wr.Dec<List<&2, Co.Rgb>>, h: {cfs.rgbs_ok(d) == True{} : Bool}) -> {cfs.req_ok(Color.co_read_quantize(d)) == True{} : Bool}:
  match d:
    case Wr.Got{cs, s}:
      h
    case Wr.Bad{}:
      {==}

def cfs.lights_r(d: Wr.Dec<List<&2, Co.Rgb>>, h: {cfs.rgbs_ok(d) == True{} : Bool}) -> {cfs.req_ok(Color.co_read_lights(d)) == True{} : Bool}:
  match d:
    case Wr.Got{cs, s}:
      h
    case Wr.Bad{}:
      {==}

def cfs.tag(t: Nat, +s: String) -> {cfs.req_ok(Color.co_read_req.tag(t, s)) == True{} : Bool}:
  match t:
    case 0n:
      cfs.quantize(Color.co_read_rgbs(Wr.get_nat(s)), cfs.rgbs(Wr.get_nat(s)))
    case 1n:
      cfs.lights_r(Color.co_read_rgbs(Wr.get_nat(s)), cfs.rgbs(Wr.get_nat(s)))
    case 2n:
      {==}
    case 3n+p:
      {==}

# every request the laws' reader reads has channels of at most 255
def cfs.req(r: Wr.Dec<Nat>) -> {cfs.req_ok(Color.co_read_req.go(r)) == True{} : Bool}:
  match r:
    case Wr.Got{t, s}:
      cfs.tag(t, s)
    case Wr.Bad{}:
      {==}

# The replies are the spec's
# --------------------------

def cfs.byte3(c: Co.Rgb, h: {Color.co_fits_rgb(c) == True{} : Bool}) -> {ColorMath.th.byte3(c) == True{} : Bool}:
  match c:
    case Co.Rgb{r, g, b}:
      h

def cfs.idxs(cs: List<&2, Co.Rgb>, -rest: String, +h: {Color.co_fits_rgbs(cs) == True{} : Bool}) -> {FCo.put_idxs.items(cs, rest) == ColorSpec.cx_idxs(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      +hc = LLogicBool.pf.and_l(Color.co_fits_rgb(c), Color.co_fits_rgbs(t), h)
      +ht = LLogicBool.pf.and_r(Color.co_fits_rgb(c), Color.co_fits_rgbs(t), h)
      %ColorMath.color_to256_spec(c, cfs.byte3(c, hc)) : {Wr.put_u32(Co.to256(c), FCo.put_idxs.items(t, rest)) == Wr.put_u32(_, ColorSpec.cx_idxs(t, rest)) : String}
      %cfs.idxs(t, rest, ht) : {Wr.put_u32(Co.to256(c), FCo.put_idxs.items(t, rest)) == Wr.put_u32(Co.to256(c), _) : String}
      {==}

# the luminance of laws/color/math.bend (over bend/color.bend's lin) is the
# spec's, over spec/theme/color.bend's
def cfs.lum(c: Co.Rgb) -> {ColorMath.th.lum(c) == ColorSpec.cx_lum(c) : U32}:
  match c:
    case Co.Rgb{+r, +g, +b}:
      %ColorMath.color_lin_spec(r) : {ColorMath.th.lum(Co.Rgb{r, g, b}) == (2126 * _ + 7152 * Cm.lin(g) + 722 * Cm.lin(b) : U32) : U32}
      %ColorMath.color_lin_spec(g) : {ColorMath.th.lum(Co.Rgb{r, g, b}) == (2126 * Co.lin(r) + 7152 * _ + 722 * Cm.lin(b) : U32) : U32}
      %ColorMath.color_lin_spec(b) : {ColorMath.th.lum(Co.Rgb{r, g, b}) == (2126 * Co.lin(r) + 7152 * Co.lin(g) + 722 * _ : U32) : U32}
      {==}

def cfs.lights(cs: List<&2, Co.Rgb>, -rest: String) -> {FCo.put_lights.items(cs, rest) == ColorSpec.cx_lights(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(Bool, Co.light(c), U32.is_gt(ColorMath.th.lum(c), 50000000), ColorMath.color_light_spec(c)) : {Wr.put_bool(_, FCo.put_lights.items(t, rest)) == ColorSpec.cx_lights(c <> t, rest) : String}
      %cfs.lum(c) : {Wr.put_bool(U32.is_gt(ColorMath.th.lum(c), 50000000), FCo.put_lights.items(t, rest)) == Wr.put_bool(U32.is_gt(_, 50000000), ColorSpec.cx_lights(t, rest)) : String}
      %cfs.lights(t, rest) : {Wr.put_bool(U32.is_gt(ColorMath.th.lum(c), 50000000), FCo.put_lights.items(t, rest)) == Wr.put_bool(U32.is_gt(ColorMath.th.lum(c), 50000000), _) : String}
      {==}

# the laws' palette spelling over Co.ansi256 is the spec's over
# th.ansi_any (color_ansi256_spec), index by index
def cfs.spell(k: Nat, +i: U32, +rest: String) -> {Color.co_spell_table(k, i, rest) == ColorSpec.cx_table(k, i, rest) : String}:
  match k:
    case 0n:
      {==}
    case 1n++m:
      %ColorMath.color_ansi256_spec(i) : {Color.co_spell_rgb(Co.ansi256(i), Color.co_spell_table(m, (i + 1 : U32), rest)) == Color.co_spell_rgb(_, ColorSpec.cx_table(m, (i + 1 : U32), rest)) : String}
      %cfs.spell(m, (i + 1 : U32), rest) : {Color.co_spell_rgb(Co.ansi256(i), Color.co_spell_table(m, (i + 1 : U32), rest)) == Color.co_spell_rgb(Co.ansi256(i), _) : String}
      {==}

def cfs.reply(r: FCo.Req, h: {cfs.req_fits(r) == True{} : Bool}) -> {FCo.reply(r) == ColorSpec.cx_answer(r) : String}:
  match r:
    case FCo.Quantize{+cs}:
      %cfs.idxs(cs, "", h) : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_idxs.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
      {==}
    case FCo.Lights{+cs}:
      %cfs.lights(cs, "") : {Wr.put_nat(List.length(&2, Co.Rgb, cs), FCo.put_lights.items(cs, "")) == Wr.put_nat(List.length(&2, Co.Rgb, cs), _) : String}
      {==}
    case FCo.Table{}:
      %cfs.spell(256n, 0, "") : {Wr.put_nat(256n, FCo.put_table("")) == Wr.put_nat(256n, _) : String}
      %PFfiAnswers.cp.table("") : {Wr.put_nat(256n, FCo.put_table("")) == Wr.put_nat(256n, _) : String}
      {==}

def cfs.end(b: Bool, r: FCo.Req, h: {cfs.req_fits(r) == True{} : Bool}) -> {FCo.run.end(b, r) == ColorSpec.cx_entry(Color.co_read_req.end(b, r)) : String}:
  match b:
    case True{}:
      cfs.reply(r, h)
    case False{}:
      {==}

def cfs.run(d: Wr.Dec<FCo.Req>, h: {cfs.req_ok(d) == True{} : Bool}) -> {FCo.run(d) == ColorSpec.cx_entry(Color.co_read_req.whole(d)) : String}:
  match d:
    case Wr.Got{r, s}:
      cfs.end(Wr.end(s), r, h)
    case Wr.Bad{}:
      {==}

def ColorSpec.color_ffi_spec(s):
  %LCo.ce.req(Wr.get_nat(s)) : {FCo.run(_) == ColorSpec.cx_entry(Color.co_read_req(s)) : String}
  cfs.run(Color.co_read_req.go(Wr.get_nat(s)), cfs.req(Wr.get_nat(s)))
