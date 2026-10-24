# eukhe: the proof of LAW command_ffi_reads_only_requests
#
# PROOF of LAW command_ffi_reads_only_requests: an answer that is not the error form
# comes from a request the decoder read whole (a malformed request or
# input left over answers the error form). The decoder accepts only
# spellings: each stage (count, entry fields, tags, line, row, key) is a
# wire value its exactness law inverts (wire_nat_exact, wire_str_exact,
# wire_bool_exact, wire_strs_exact), threading the equation of the input
# so far; a decoded value fits (wire_*_decoded_fit(s)). That request is
# the witness, and the entry answers it with the spelled reply (ce_run).

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/command/entry.bend as Command
import ../wire/base/spell.bend as LAWireSpell
import ./base/entry.bend as LACommandEntry
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_strs_exact.bend as PWireStrsExact
import ../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits


# ---- what a decoder answer says about its input ----

# an entry answer: the input s0 spells it, and it fits
def ci_ent(s0: String, d: Wr.Dec<FCmd.EntW>) -> Type:
  match d:
    case Wr.Got{+e, r}:
      {s0 == Command.cmd_spell_ent(e, r) : String} & {Command.cmd_ent_fits(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the entry's string-list fit is the wire kit's
def ci_strs_all(xs: List<&2, String>) -> {LawsBase.wire_strs_all(xs) == Command.cmd_strs_all(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(Bool, Bool, z => Bool.and(LawsBase.wire_fits(String.length(x)), z), LawsBase.wire_strs_all(t), Command.cmd_strs_all(t), ci_strs_all(t))

def ci_strs_fit(+xs: List<&2, String>, h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}) -> {Command.cmd_strs_fit(xs) == True{} : Bool}:
  %ci_strs_all(xs) : {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), _) == True{} : Bool}
  h

# ---- an entry: path, aliases, run, free, arg ----

def ci_arg(-s0: String, +p: List<&2, String>, +a: List<&2, String>, +r0: Bool, +f: Bool, +s4: String,
  pre: {s0 == LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, Wr.put_bool(f, s4)))) : String},
  fit: {Bool.and(Command.cmd_strs_fit(p), Command.cmd_strs_fit(a)) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> ci_ent(s0, FCmd.get_ent.arg(p, a, r0, f, d)):
  match d:
    case Wr.Got{+g, +s5}:
      (Equal.trans(String, s0, LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, Wr.put_bool(f, s4)))), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, Wr.put_bool(f, Wr.put_bool(g, s5))))), pre,
          Equal.cong(String, String, z => LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, Wr.put_bool(f, z)))), s4, Wr.put_bool(g, s5), Wire.wire_bool_exact(s4, g, s5, ed))),
        fit)
    case Wr.Bad{}:
      Unit{}

def ci_free(-s0: String, +p: List<&2, String>, +a: List<&2, String>, +r0: Bool, +s3: String,
  pre: {s0 == LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, s3))) : String},
  fit: {Bool.and(Command.cmd_strs_fit(p), Command.cmd_strs_fit(a)) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s3) == d : Wr.Dec<Bool>}) -> ci_ent(s0, FCmd.get_ent.free(p, a, r0, d)):
  match d:
    case Wr.Got{+f, +s4}:
      ci_arg(s0, p, a, r0, f, s4,
        Equal.trans(String, s0, LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, s3))), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, Wr.put_bool(f, s4)))), pre,
          Equal.cong(String, String, z => LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, z))), s3, Wr.put_bool(f, s4), Wire.wire_bool_exact(s3, f, s4, ed))),
        fit, Wr.get_bool(s4), {==})
    case Wr.Bad{}:
      Unit{}

def ci_run(-s0: String, +p: List<&2, String>, +a: List<&2, String>, +s2: String,
  pre: {s0 == LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, s2)) : String},
  fit: {Bool.and(Command.cmd_strs_fit(p), Command.cmd_strs_fit(a)) == True{} : Bool},
  d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> ci_ent(s0, FCmd.get_ent.run(p, a, d)):
  match d:
    case Wr.Got{+r0, +s3}:
      ci_free(s0, p, a, r0, s3,
        Equal.trans(String, s0, LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, s2)), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, Wr.put_bool(r0, s3))), pre,
          Equal.cong(String, String, z => LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, z)), s2, Wr.put_bool(r0, s3), Wire.wire_bool_exact(s2, r0, s3, ed))),
        fit, Wr.get_bool(s3), {==})
    case Wr.Bad{}:
      Unit{}

def ci_alias(-s0: String, +p: List<&2, String>, +s1: String,
  pre: {s0 == LawsBase.wire_spell_strs(p, s1) : String}, fp: {Command.cmd_strs_fit(p) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> ci_ent(s0, FCmd.get_ent.alias(p, d)):
  match d:
    case Wr.Got{+a, +s2}:
      +e2 = ed
      ci_run(s0, p, a, s2,
        Equal.trans(String, s0, LawsBase.wire_spell_strs(p, s1), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, s2)), pre,
          Equal.cong(String, String, z => LawsBase.wire_spell_strs(p, z), s1, LawsBase.wire_spell_strs(a, s2), Wire.wire_strs_exact(s1, a, s2, e2))),
        LAWireSpell.ws_and_tt(Command.cmd_strs_fit(p), Command.cmd_strs_fit(a), fp, ci_strs_fit(a, Wire.wire_strs_decoded_fit(s1, a, s2, e2))),
        Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ci_path(+s0: String, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s0) == d : Wr.Dec<List<&2, String>>}) -> ci_ent(s0, FCmd.get_ent.path(d)):
  match d:
    case Wr.Got{+p, +s1}:
      +e2 = ed
      ci_alias(s0, p, s1, Wire.wire_strs_exact(s0, p, s1, e2), ci_strs_fit(p, Wire.wire_strs_decoded_fit(s0, p, s1, e2)), Wr.get_list(~String, ~Wr.get_str, s1), {==})
    case Wr.Bad{}:
      Unit{}

# every entry the decoder reads is spelled, and fits
def ci_ent_all(+s0: String) -> ci_ent(s0, FCmd.get_ent(s0)):
  ci_path(s0, Wr.get_list(~String, ~Wr.get_str, s0), {==})

def ci_ent_at(+s: String, -d: Wr.Dec<FCmd.EntW>, er: {FCmd.get_ent(s) == d : Wr.Dec<FCmd.EntW>}) -> ci_ent(s, d):
  %er : ci_ent(s, _)
  ci_ent_all(s)

# ---- the table ----

# what the entry loop's answer says about its input s (m + 1 entries)
def ci_tl(s: String, m: Nat, d: Wr.Dec<List<&2, FCmd.EntW>>) -> Type:
  match d:
    case Wr.Got{+t, r}:
      {s == Command.cmd_spell_ents(t, r) : String} & ({List.length(&2, FCmd.EntW, t) == 1n+m : Nat} & {Command.cmd_ents_all(t) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def ci_tl_step(-s: String, +x: FCmd.EntW, +s3: String, -k: Nat, ea: {s == Command.cmd_spell_ent(x, s3) : String}, eb: {Command.cmd_ent_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, FCmd.EntW>>, ih: ci_tl(s3, k, d)) -> ci_tl(s, 1n+k, Wr.get_list.cons(FCmd.EntW, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, ee) = ih
      (e2, e3) = ee
      (Equal.trans(String, s, Command.cmd_spell_ent(x, s3), Command.cmd_spell_ent(x, Command.cmd_spell_ents(ys, r)), ea,
          Equal.cong(String, String, z => Command.cmd_spell_ent(x, z), s3, Command.cmd_spell_ents(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, FCmd.EntW, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(Command.cmd_ent_fits(x), Command.cmd_ents_all(ys), eb, e3)))
    case Wr.Bad{}:
      Unit{}

def ci_tl_step2(-s: String, +x: FCmd.EntW, +s3: String, -k: Nat, ex: ci_ent(s, Wr.Got{x, s3}),
  d: Wr.Dec<List<&2, FCmd.EntW>>, ih: ci_tl(s3, k, d)) -> ci_tl(s, 1n+k, Wr.get_list.cons(FCmd.EntW, x, d)):
  (ea, eb) = ex
  ci_tl_step(s, x, s3, k, ea, eb, d, ih)

def ci_tl_one(-s: String, +x: FCmd.EntW, -s3: String, ex: ci_ent(s, Wr.Got{x, s3})) -> ci_tl(s, 0n, Wr.Got{[x], s3}):
  (ea, eb) = ex
  (ea, ({==}, LAWireSpell.ws_and_tt(Command.cmd_ent_fits(x), True{}, eb, {==})))

# the entry loop accepts only spelled entries that fit
def ci_tl_spec(m: Nat, cur: Wr.Dec<FCmd.EntW>, +s: String, er: {FCmd.get_ent(s) == cur : Wr.Dec<FCmd.EntW>}) ->
  ci_tl(s, m, Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      ci_tl_one(s, x, s3, ci_ent_at(s, Wr.Got{x, s3}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ci_tl_step2(s, x, s3, k, ci_ent_at(s, Wr.Got{x, s3}, er),
        Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, k, FCmd.get_ent(s3)), ci_tl_spec(k, FCmd.get_ent(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a table decoder answer says about its input s
def ci_table(s: String, d: Wr.Dec<List<&2, FCmd.EntW>>) -> Type:
  match d:
    case Wr.Got{+t, r}:
      {s == Command.cmd_spell_table(t, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), Command.cmd_ents_all(t)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_table_eq(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, +t: List<&2, FCmd.EntW>, -r: String,
  e1: {s2 == Command.cmd_spell_ents(t, r) : String}, e2: {List.length(&2, FCmd.EntW, t) == 1n+m : Nat}) -> {s == Command.cmd_spell_table(t, r) : String}:
  %Equal.sym(Nat, List.length(&2, FCmd.EntW, t), 1n+m, e2) : {s == Wr.put_nat(_, Command.cmd_spell_ents(t, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ci_table_fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +t: List<&2, FCmd.EntW>,
  e2: {List.length(&2, FCmd.EntW, t) == 1n+m : Nat}, e3: {Command.cmd_ents_all(t) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), Command.cmd_ents_all(t)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, FCmd.EntW, t), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), Command.cmd_ents_all(t)) == True{} : Bool}
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), Command.cmd_ents_all(t), hn, e3)

def ci_table_conv(+s: String, +s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, FCmd.EntW>>, tl: ci_tl(s2, m, d)) -> ci_table(s, d):
  match d:
    case Wr.Got{+t, +r}:
      (e1, ee) = tl
      (e2, e3) = ee
      +e4 = e2
      (ci_table_eq(s, s2, m, en, t, r, e1, e4), ci_table_fit(m, hn, t, e4, e3))
    case Wr.Bad{}:
      Unit{}

def ci_table_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ci_table(s, Wr.get_list.start(~FCmd.EntW, ~FCmd.get_ent, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ci_table_conv(s, s2, m, en, hn, Wr.get_list.go(~FCmd.EntW, ~FCmd.get_ent, m, FCmd.get_ent(s2)), ci_tl_spec(m, FCmd.get_ent(s2), s2, {==}))

def ci_table_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  ci_table(s, Wr.get_list.start(~FCmd.EntW, ~FCmd.get_ent, r)):
  match r:
    case Wr.Got{+n, +s2}:
      +e2 = er
      ci_table_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e2), Wire.wire_nat_decoded_fits(s, n, s2, e2))
    case Wr.Bad{}:
      Unit{}

# every table the decoder reads is spelled, and fits
def ci_table_all(+s: String) -> ci_table(s, FCmd.get_table(s)):
  ci_table_top(s, Wr.get_nat(s), {==})

# ---- the question ----

# what a question decoder answer says about its input s
def ci_query(s: String, d: Wr.Dec<FCmd.Query>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == Command.cmd_spell_query(q, r) : String} & {Command.cmd_query_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_q_resolve(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> ci_query(s0, FCmd.get_query.resolve(d)):
  match d:
    case Wr.Got{+l, +r}:
      +e2 = ed
      (Equal.trans(String, s0, Wr.put_nat(0n, s1), Wr.put_nat(0n, Wr.put_str(l, r)), pre,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Wr.put_str(l, r), Wire.wire_str_exact(s1, l, r, e2))),
        Wire.wire_str_decoded_fits(s1, l, r, e2))
    case Wr.Bad{}:
      Unit{}

def ci_q_menu(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> ci_query(s0, FCmd.get_query.menu(d)):
  match d:
    case Wr.Got{+l, +r}:
      +e2 = ed
      (Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_str(l, r)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_str(l, r), Wire.wire_str_exact(s1, l, r, e2))),
        Wire.wire_str_decoded_fits(s1, l, r, e2))
    case Wr.Bad{}:
      Unit{}

def ci_press_tag(-s0: String, +l: String, +x: Cmd.Sel, -sx: String, pt: Nat, +s5: String,
  pre: {s0 == Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, sx))) : String},
  fl: {Bool.and(LawsBase.wire_fits(String.length(l)), Command.cmd_sel_fits(x)) == True{} : Bool},
  ex: {sx == Wr.put_nat(pt, s5) : String}) -> ci_query(s0, FCmd.get_query.press(l, x, FCmd.get_press.tag(pt, s5))):
  match pt:
    case 0n:
      (Equal.trans(String, s0, Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, sx))), Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, Wr.put_nat(0n, s5)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, z))), sx, Wr.put_nat(0n, s5), ex)),
        fl)
    case 1n:
      (Equal.trans(String, s0, Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, sx))), Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, Wr.put_nat(1n, s5)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, z))), sx, Wr.put_nat(1n, s5), ex)),
        fl)
    case 2n+y:
      Unit{}

def ci_press(-s0: String, +l: String, +x: Cmd.Sel, +sx: String,
  pre: {s0 == Wr.put_nat(2n, Wr.put_str(l, Command.cmd_spell_sel(x, sx))) : String},
  fl: {Bool.and(LawsBase.wire_fits(String.length(l)), Command.cmd_sel_fits(x)) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(sx) == d : Wr.Dec<Nat>}) -> ci_query(s0, FCmd.get_query.press(l, x, FCmd.get_press.go(d))):
  match d:
    case Wr.Got{+pt, +s5}:
      ci_press_tag(s0, l, x, sx, pt, s5, pre, fl, Wire.wire_nat_exact(sx, pt, s5, ed))
    case Wr.Bad{}:
      Unit{}

def ci_row(-s0: String, +l: String, +s3: String,
  pre: {s0 == Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(1n, s3))) : String},
  hl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> ci_query(s0, FCmd.get_query.sel(l, FCmd.get_sel.row(d))):
  match d:
    case Wr.Got{+i, +s4}:
      +e2 = ed
      ci_press(s0, l, Cmd.Row{i}, s4,
        Equal.trans(String, s0, Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(1n, s3))), Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(1n, Wr.put_nat(i, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(1n, z))), s3, Wr.put_nat(i, s4), Wire.wire_nat_exact(s3, i, s4, e2))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(l)), LawsBase.wire_fits(i), hl, Wire.wire_nat_decoded_fits(s3, i, s4, e2)),
        Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def ci_sel_tag(-s0: String, +l: String, -s2: String, st: Nat, +s3: String,
  pre: {s0 == Wr.put_nat(2n, Wr.put_str(l, s2)) : String},
  hl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool},
  ex: {s2 == Wr.put_nat(st, s3) : String}) -> ci_query(s0, FCmd.get_query.sel(l, FCmd.get_sel.tag(st, s3))):
  match st:
    case 0n:
      ci_press(s0, l, Cmd.NoRow{}, s3,
        Equal.trans(String, s0, Wr.put_nat(2n, Wr.put_str(l, s2)), Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(0n, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, z)), s2, Wr.put_nat(0n, s3), ex)),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(l)), True{}, hl, {==}),
        Wr.get_nat(s3), {==})
    case 1n:
      ci_row(s0, l, s3,
        Equal.trans(String, s0, Wr.put_nat(2n, Wr.put_str(l, s2)), Wr.put_nat(2n, Wr.put_str(l, Wr.put_nat(1n, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, z)), s2, Wr.put_nat(1n, s3), ex)),
        hl, Wr.get_nat(s3), {==})
    case 2n+y:
      Unit{}

def ci_sel(-s0: String, +l: String, +s2: String,
  pre: {s0 == Wr.put_nat(2n, Wr.put_str(l, s2)) : String},
  hl: {LawsBase.wire_fits(String.length(l)) == True{} : Bool},
  d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> ci_query(s0, FCmd.get_query.sel(l, FCmd.get_sel.go(d))):
  match d:
    case Wr.Got{+st, +s3}:
      ci_sel_tag(s0, l, s2, st, s3, pre, hl, Wire.wire_nat_exact(s2, st, s3, ed))
    case Wr.Bad{}:
      Unit{}

def ci_key(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> ci_query(s0, FCmd.get_query.key(d)):
  match d:
    case Wr.Got{+l, +s2}:
      +e2 = ed
      ci_sel(s0, l, s2,
        Equal.trans(String, s0, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_str(l, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_str(l, s2), Wire.wire_str_exact(s1, l, s2, e2))),
        Wire.wire_str_decoded_fits(s1, l, s2, e2), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def ci_qtag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> ci_query(s0, FCmd.get_query.tag(t, s1)):
  match t:
    case 0n:
      ci_q_resolve(s0, s1, ex, Wr.get_str(s1), {==})
    case 1n:
      ci_q_menu(s0, s1, ex, Wr.get_str(s1), {==})
    case 2n:
      ci_key(s0, s1, ex, Wr.get_str(s1), {==})
    case 3n+y:
      Unit{}

def ci_query_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ci_query(s, FCmd.get_query.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      ci_qtag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# every question the decoder reads is spelled, and fits
def ci_query_all(+s: String) -> ci_query(s, FCmd.get_query(s)):
  ci_query_top(s, Wr.get_nat(s), {==})

# ---- the request ----

def ci_req(s: String, d: Wr.Dec<FCmd.Req>) -> Type:
  match d:
    case Wr.Got{+r, rest}:
      {s == Command.cmd_spell_req(r, rest) : String} & {Command.cmd_req_fits(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ci_req_q(-s0: String, +t: List<&2, FCmd.EntW>, +s1: String, pre: {s0 == Command.cmd_spell_table(t, s1) : String},
  ft: {Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), Command.cmd_ents_all(t)) == True{} : Bool},
  d: Wr.Dec<FCmd.Query>, cq: ci_query(s1, d)) -> ci_req(s0, FCmd.get_req.query(t, d)):
  match d:
    case Wr.Got{+q, +rest}:
      (e1, e2) = cq
      (Equal.trans(String, s0, Command.cmd_spell_table(t, s1), Command.cmd_spell_table(t, Command.cmd_spell_query(q, rest)), pre,
          Equal.cong(String, String, z => Command.cmd_spell_table(t, z), s1, Command.cmd_spell_query(q, rest), e1)),
        LAWireSpell.ws_and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, FCmd.EntW, t)), Command.cmd_ents_all(t)), Command.cmd_query_fits(q), ft, e2))
    case Wr.Bad{}:
      Unit{}

def ci_req_t(+s0: String, d: Wr.Dec<List<&2, FCmd.EntW>>, ct: ci_table(s0, d)) -> ci_req(s0, FCmd.get_req.table(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e1, e2) = ct
      ci_req_q(s0, t, s1, e1, e2, FCmd.get_query(s1), ci_query_all(s1))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits
def ci_req_all(+s: String) -> ci_req(s, FCmd.get_req(s)):
  ci_req_t(s, FCmd.get_table(s), ci_table_all(s))

# ---- the entry ----

# the claim: s spells a request that fits, and the entry answers it
def ci_goal(+s: String) -> Type:
  &r: FCmd.Req -> {(s, (Command.cmd_req_fits(r), FCmd.ffi(s))) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}

def ci_rest.eq(+s: String, +r: FCmd.Req, ed: {FCmd.get_req(s) == Wr.Got{r, ""} : Wr.Dec<FCmd.Req>},
  e1: {s == Command.cmd_spell_req(r, "") : String}, e2: {Command.cmd_req_fits(r) == True{} : Bool}) ->
  {(s, (Command.cmd_req_fits(r), FCmd.ffi(s))) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}:
  %Equal.sym(Wr.Dec<FCmd.Req>, FCmd.get_req(s), Wr.Got{r, ""}, ed) : {(s, (Command.cmd_req_fits(r), FCmd.ffi.go(_))) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, FCmd.ffi.run(r), Command.cmd_spell_reply(r), LACommandEntry.ce_run(r)) : {(s, (Command.cmd_req_fits(r), _)) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(Bool, Command.cmd_req_fits(r), True{}, e2) : {(s, (_, Command.cmd_spell_reply(r))) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}
  %Equal.sym(String, s, Command.cmd_spell_req(r, ""), e1) : {(_, (True{}, Command.cmd_spell_reply(r))) == (Command.cmd_spell_req(r, ""), (True{}, Command.cmd_spell_reply(r))) : String & (Bool & String)}
  {==}

def ci_rest(+s: String, +r: FCmd.Req, rest: String, ed: {FCmd.get_req(s) == Wr.Got{r, rest} : Wr.Dec<FCmd.Req>},
  e1: {s == Command.cmd_spell_req(r, rest) : String}, e2: {Command.cmd_req_fits(r) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FCmd.ffi.whole(r, String.is_empty(rest))) == False{} : Bool}) -> ci_goal(s):
  match rest:
    case SNil{}:
      (r, ci_rest.eq(s, r, ed, e1, e2))
    case SCon{c, more}:
      LAWireSpell.ws_absurd(ci_goal(s), ok)

def ci_main(+s: String, d: Wr.Dec<FCmd.Req>, ed: {FCmd.get_req(s) == d : Wr.Dec<FCmd.Req>}, inv: ci_req(s, d),
  ok: {LawsBase.wire_opens_err(FCmd.ffi.go(d)) == False{} : Bool}) -> ci_goal(s):
  match d:
    case Wr.Got{+r, +rest}:
      (e1, e2) = inv
      ci_rest(s, r, rest, ed, e1, e2, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ci_goal(s), ok)

def Command.command_ffi_reads_only_requests(s, ok):
  ci_main(s, FCmd.get_req(s), {==}, ci_req_all(s), ok)
