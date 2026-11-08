# eukhe: the proof of LAW path_policy_ffi_reads_only_requests
#
# PROOF: what each list decoder reads is the spelling of a list that fits
# (ro.nl: wire_list_exact, wire_nats_spells, the item loop's fits), each
# Fl.unflat that reads paths reads the spec's flattening of them
# (ro.unflat_inv), each rule read is the spec's spelling of it
# (ro.rules_inv); the entry's stages carry the input spelled up to their
# field (`pre`), so an answer that is no error comes from a request read
# whole, nothing left, and is the spelled reply (LA.pp.reply_spec).

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/wire.bend as Wire
import ../wire/base/spell.bend as LAWireSpell
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./base.bend as LA

# s spelled up to a field a is s spelled up to its spelling b
def ro.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# A list of Nats read
# -------------------

# the item loop (m + 1 items): its items fit, and there are m + 1
def ro.LF(d: Wr.Dec<List<&2, Nat>>, m: Nat) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {LawsBase.wire_nats_fit(xs) == True{} : Bool} & {List.length(&2, Nat, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def ro.lf_step(+x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, -k: Nat, d: Wr.Dec<List<&2, Nat>>, ih: ro.LF(d, k)) -> ro.LF(Wr.get_list.cons(Nat, x, d), 1n+k):
  match d:
    case Wr.Got{+ys, r}:
      (f, n) = ih
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), fx, f), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, n))
    case Wr.Bad{}:
      Unit{}

def ro.lf_go(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> ro.LF(Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur), m):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, s3, er), {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ro.lf_step(x, Wire.wire_nat_decoded_fits(s, x, s3, er), k, Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), ro.lf_go(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# a list read fits
def ro.F(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {PathPolicy.pp_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.f_go(-m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, lf: ro.LF(d, m)) -> ro.F(d):
  match d:
    case Wr.Got{+xs, r}:
      (f, n) = lf
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, n) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, f)
    case Wr.Bad{}:
      Unit{}

def ro.f_start(n: Nat, +s2: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ro.F(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==})
    case 1n++m:
      ro.f_go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), ro.lf_go(m, Wr.get_nat(s2), s2, {==}))

def ro.f_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ro.F(Wr.get_list.start(~Nat, ~Wr.get_nat, r)):
  match r:
    case Wr.Got{+n, +s2}:
      ro.f_start(n, s2, Wire.wire_nat_decoded_fits(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

# what a list decoder reads is the spelling of a list that fits, then its rest
def ro.NL(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_spell_nats(xs, r) : String} & {PathPolicy.pp_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ro.nl_at(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}, fd: ro.F(d)) -> ro.NL(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LawsBase.wire_spell_nats(xs, r), Wire.wire_list_exact(s, xs, r, ed), Wire.wire_nats_spells(xs, r)), fd)
    case Wr.Bad{}:
      Unit{}

def ro.nl(+s: String) -> ro.NL(s, FPp.get_ns(s)):
  ro.nl_at(s, FPp.get_ns(s), {==}, ro.f_top(s, Wr.get_nat(s), {==}))

# Paths and rules read
# --------------------

# what a fold of ns says: the lists of its state flatten to ns
def ro.FI(ns: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {ns == PathPolicy.pp_flat(Fl.St.lists(st)) : List<&2, Nat>}

def ro.fold_step(-rest: List<&2, Nat>, m: Maybe<&2, Fl.St>, ih: ro.FI(rest, m), n: Nat) -> ro.FI(n <> rest, Fl.step(n, m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      match st:
        case Fl.Start{}:
          match n:
            case 0n:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, rest, Nil{}, ih)
            case 1n+x:
              Unit{}
        case Fl.Mid{o, d}:
          match n:
            case 0n:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => 0n <> z, rest, PathPolicy.pp_flat(o <> d), ih)
            case 1n+x:
              Equal.cong(List<&2, Nat>, List<&2, Nat>, z => {1n+x : Nat} <> z, rest, PathPolicy.pp_flat(o <> d), ih)

def ro.fold_inv(ns: List<&2, Nat>) -> ro.FI(ns, Fl.fold(ns)):
  match ns:
    case Nil{}:
      {==}
    case n <> +rest:
      ro.fold_step(rest, Fl.fold(rest), ro.fold_inv(rest), n)

# the paths Fl.unflat reads flatten to its input
def ro.UI(ns: List<&2, Nat>, m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{xss}:
      {ns == PathPolicy.pp_flat(xss) : List<&2, Nat>}

def ro.unflat_fin(-ns: List<&2, Nat>, m: Maybe<&2, Fl.St>, h: ro.FI(ns, m)) -> ro.UI(ns, Fl.unflat.fin(m)):
  match m:
    case None{}:
      Unit{}
    case Some{st}:
      h

def ro.unflat_inv(+ns: List<&2, Nat>) -> ro.UI(ns, Fl.unflat(ns)):
  ro.unflat_fin(ns, Fl.fold(ns), ro.fold_inv(ns))

# a rule read is the spec's spelling of it
def ro.R1(xs: List<&2, Nat>, m: Maybe<&2, Pp.Rule>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      {xs == PathPolicy.pp_rule(r) : List<&2, Nat>}

def ro.named(n: Nat, rest: List<&2, Nat>) -> ro.R1(2n <> n <> rest, FPp.rule.named(n, rest)):
  match rest:
    case Nil{}:
      {==}
    case x <> more:
      Unit{}

def ro.rule_inv(xs: List<&2, Nat>) -> ro.R1(xs, FPp.rule.of(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case t <> p:
      match t:
        case 0n:
          {==}
        case 1n+a:
          match a:
            case 0n:
              {==}
            case 1n+b:
              match b:
                case 0n:
                  match p:
                    case Nil{}:
                      Unit{}
                    case n <> rest:
                      ro.named(n, rest)
                case 1n+c:
                  Unit{}

# rules read are the spec's spelling of them
def ro.RO(xss: List<&2, List<&2, Nat>>, m: Maybe<&2, List<&2, Pp.Rule>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{rs}:
      {xss == PathPolicy.pp_rules(rs) : List<&2, List<&2, Nat>>}

def ro.cons(-x: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, m: Maybe<&2, Pp.Rule>, hm: ro.R1(x, m), ms: Maybe<&2, List<&2, Pp.Rule>>, hms: ro.RO(rest, ms)) -> ro.RO(x <> rest, FPp.rules.cons(m, ms)):
  match m:
    case Some{r}:
      match ms:
        case Some{rs}:
          %hm : {x <> rest == _ <> PathPolicy.pp_rules(rs) : List<&2, List<&2, Nat>>}
          %hms : {x <> rest == x <> _ : List<&2, List<&2, Nat>>}
          {==}
        case None{}:
          Unit{}
    case None{}:
      match ms:
        case Some{rs}:
          Unit{}
        case None{}:
          Unit{}

def ro.rules_inv(xss: List<&2, List<&2, Nat>>) -> ro.RO(xss, FPp.rules.of(xss)):
  match xss:
    case Nil{}:
      {==}
    case +x <> +rest:
      ro.cons(x, rest, FPp.rule.of(x), ro.rule_inv(x), FPp.rules.of(rest), ro.rules_inv(rest))

# the rules Rust's list reads flatten to its input
def ro.RI(b: List<&2, Nat>, m: Maybe<&2, List<&2, Pp.Rule>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{ru}:
      {b == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}

def ro.rules_at2(-b: List<&2, Nat>, -xss: List<&2, List<&2, Nat>>, hu: {b == PathPolicy.pp_flat(xss) : List<&2, Nat>}, mr: Maybe<&2, List<&2, Pp.Rule>>, hr: ro.RO(xss, mr)) -> ro.RI(b, mr):
  match mr:
    case None{}:
      Unit{}
    case Some{ru}:
      Equal.trans(List<&2, Nat>, b, PathPolicy.pp_flat(xss), PathPolicy.pp_flat(PathPolicy.pp_rules(ru)), hu, Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => PathPolicy.pp_flat(z), xss, PathPolicy.pp_rules(ru), hr))

def ro.rules_at(-b: List<&2, Nat>, m: Maybe<&2, List<&2, List<&2, Nat>>>, hu: ro.UI(b, m)) -> ro.RI(b, FPp.get_req.rules(m)):
  match m:
    case None{}:
      Unit{}
    case Some{+xss}:
      ro.rules_at2(b, xss, hu, FPp.rules.of(xss), ro.rules_inv(xss))

# The entry's stages
# ------------------

def ro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FPp.Req, q => {(s, (PathPolicy.pp_req_fits(q), a)) == (PathPolicy.pp_spell_req(q, ""), (True{}, PathPolicy.pp_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def ro.top_eq(+s: String, +q: FPp.Req, +a: String, e: {s == PathPolicy.pp_spell_req(q, "") : String}, f: {PathPolicy.pp_req_fits(q) == True{} : Bool}, ea: {a == PathPolicy.pp_spell_answer(q) : String}) -> {(s, (PathPolicy.pp_req_fits(q), a)) == (PathPolicy.pp_spell_req(q, ""), (True{}, PathPolicy.pp_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, PathPolicy.pp_spell_req(q, ""), e) : {(_, (PathPolicy.pp_req_fits(q), a)) == (PathPolicy.pp_spell_req(q, ""), (True{}, PathPolicy.pp_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, PathPolicy.pp_req_fits(q), True{}, f) : {(PathPolicy.pp_spell_req(q, ""), (_, a)) == (PathPolicy.pp_spell_req(q, ""), (True{}, PathPolicy.pp_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, PathPolicy.pp_spell_answer(q), ea) : {(PathPolicy.pp_spell_req(q, ""), (True{}, _)) == (PathPolicy.pp_spell_req(q, ""), (True{}, PathPolicy.pp_spell_answer(q))) : String & (Bool & String)}
  {==}

# the last stage: nothing left answers the request, anything left is the
# error form
def ro.fin(+s: String, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, s5: String, pre: {s == PathPolicy.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s5) : String}, f: {PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FPp.reply(Wr.end(s5), FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}})) == False{} : Bool}) -> ro.G(s, FPp.reply(Wr.end(s5), FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}})):
  match s5:
    case SNil{}:
      (FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, ro.top_eq(s, FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, FPp.reply(True{}, FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}), pre, f, LA.pp.reply_spec(ro, ru, se, at, l)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: input left over")), ok)

# the input spelled with the lists read is the spec's spelling of the paths
def ro.pre(-s: String, -a: List<&2, Nat>, -b: List<&2, Nat>, -c: List<&2, Nat>, -at: List<&2, Nat>, -l: Bool, -s5: String, -ro: List<&2, List<&2, Nat>>, -ru: List<&2, Pp.Rule>, -se: List<&2, List<&2, Nat>>, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}, ua: {a == PathPolicy.pp_flat(ro) : List<&2, Nat>}, ub: {b == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}, uc: {c == PathPolicy.pp_flat(se) : List<&2, Nat>}) -> {s == PathPolicy.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, s5) : String}:
  %ua : {s == LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(PathPolicy.pp_flat(PathPolicy.pp_rules(ru)), LawsBase.wire_spell_nats(PathPolicy.pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}
  %ub : {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(PathPolicy.pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}
  %uc : {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}
  pre

# and the lists' fits are the request's
def ro.fits(-a: List<&2, Nat>, -b: List<&2, Nat>, -c: List<&2, Nat>, -at: List<&2, Nat>, -l: Bool, -ro: List<&2, List<&2, Nat>>, -ru: List<&2, Pp.Rule>, -se: List<&2, List<&2, Nat>>, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, ua: {a == PathPolicy.pp_flat(ro) : List<&2, Nat>}, ub: {b == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}, uc: {c == PathPolicy.pp_flat(se) : List<&2, Nat>}) -> {PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == True{} : Bool}:
  %ua : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(_), PathPolicy.pp_nats_fit(PathPolicy.pp_flat(PathPolicy.pp_rules(ru)))), PathPolicy.pp_nats_fit(PathPolicy.pp_flat(se))), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  %ub : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(a), PathPolicy.pp_nats_fit(_)), PathPolicy.pp_nats_fit(PathPolicy.pp_flat(se))), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  %uc : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(a), PathPolicy.pp_nats_fit(b)), PathPolicy.pp_nats_fit(_)), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  LAWireSpell.ws_and_tt(Bool.and(Bool.and(PathPolicy.pp_nats_fit(a), PathPolicy.pp_nats_fit(b)), PathPolicy.pp_nats_fit(c)), PathPolicy.pp_nats_fit(at), LAWireSpell.ws_and_tt(Bool.and(PathPolicy.pp_nats_fit(a), PathPolicy.pp_nats_fit(b)), PathPolicy.pp_nats_fit(c), LAWireSpell.ws_and_tt(PathPolicy.pp_nats_fit(a), PathPolicy.pp_nats_fit(b), fa, fb), fc), fat)

# the read request spelled and fitting (each equation used twice), then
# the last stage
def ro.done(+s: String, -a: List<&2, Nat>, -b: List<&2, Nat>, -c: List<&2, Nat>, +at: List<&2, Nat>, +l: Bool, +s5: String, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, +ua: {a == PathPolicy.pp_flat(ro) : List<&2, Nat>}, +ub: {b == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}, +uc: {c == PathPolicy.pp_flat(se) : List<&2, Nat>}, ok: {LawsBase.wire_opens_err(FPp.reply(Wr.end(s5), FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}})) == False{} : Bool}) -> ro.G(s, FPp.reply(Wr.end(s5), FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}})):
  ro.fin(s, ro, ru, se, at, l, s5, ro.pre(s, a, b, c, at, l, s5, ro, ru, se, pre, ua, ub, uc), ro.fits(a, b, c, at, l, ro, ru, se, fa, fb, fc, fat, ua, ub, uc), ok)

# the paths and rules: each list a path list (unflat), the rules rules
def ro.build(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +at: List<&2, Nat>, +l: Bool, +s5: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, Wr.put_bool(l, s5))))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, mro: Maybe<&2, List<&2, List<&2, Nat>>>, uro: ro.UI(a, mro), mru: Maybe<&2, List<&2, Pp.Rule>>, uru: ro.RI(b, mru), mse: Maybe<&2, List<&2, List<&2, Nat>>>, use: ro.UI(c, mse), ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.build(mro, mru, mse, at, l, s5))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.build(mro, mru, mse, at, l, s5))):
  match mro:
    case None{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)
    case Some{+ro}:
      match mru:
        case None{}:
          LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)
        case Some{+ru}:
          match mse:
            case None{}:
              LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)
            case Some{+se}:
              ro.done(s, a, b, c, at, l, s5, ro, ru, se, pre, fa, fb, fc, fat, uro, uru, use, ok)

def ro.looped(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +at: List<&2, Nat>, +s4: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, s4)))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, fat: {PathPolicy.pp_nats_fit(at) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}, ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.looped(a, b, c, at, d))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.looped(a, b, c, at, d))):
  match d:
    case Wr.Got{+l, +s5}:
      ro.build(s, a, b, c, at, l, s5, ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, LawsBase.wire_spell_nats(at, z)))), s, s4, Wr.put_bool(l, s5), pre, Wire.wire_bool_exact(s4, l, s5, ed)), fa, fb, fc, fat, Fl.unflat(a), ro.unflat_inv(a), FPp.get_req.rules(Fl.unflat(b)), ro.rules_at(b, Fl.unflat(b), ro.unflat_inv(b)), Fl.unflat(c), ro.unflat_inv(c), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)

def ro.at(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +c: List<&2, Nat>, +s3: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, s3))) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, fc: {PathPolicy.pp_nats_fit(c) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: ro.NL(s3, d), ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.at(a, b, c, d))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.at(a, b, c, d))):
  match d:
    case Wr.Got{+at, +s4}:
      (e4, fat) = xd
      ro.looped(s, a, b, c, at, s4, ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, LawsBase.wire_spell_nats(c, z))), s, s3, LawsBase.wire_spell_nats(at, s4), pre, e4), fa, fb, fc, fat, Wr.get_bool(s4), {==}, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)

def ro.secret(+s: String, +a: List<&2, Nat>, +b: List<&2, Nat>, +s2: String, pre: {s == LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, s2)) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, fb: {PathPolicy.pp_nats_fit(b) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: ro.NL(s2, d), ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.secret(a, b, d))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.secret(a, b, d))):
  match d:
    case Wr.Got{+c, +s3}:
      (e3, fc) = xd
      ro.at(s, a, b, c, s3, ro.step(z => LawsBase.wire_spell_nats(a, LawsBase.wire_spell_nats(b, z)), s, s2, LawsBase.wire_spell_nats(c, s3), pre, e3), fa, fb, fc, FPp.get_ns(s3), ro.nl(s3), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)

def ro.rules(+s: String, +a: List<&2, Nat>, +s1: String, pre: {s == LawsBase.wire_spell_nats(a, s1) : String}, fa: {PathPolicy.pp_nats_fit(a) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, xd: ro.NL(s1, d), ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.rule_list(a, d))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.rule_list(a, d))):
  match d:
    case Wr.Got{+b, +s2}:
      (e2, fb) = xd
      ro.secret(s, a, b, s2, ro.step(z => LawsBase.wire_spell_nats(a, z), s, s1, LawsBase.wire_spell_nats(b, s2), pre, e2), fa, fb, FPp.get_ns(s2), ro.nl(s2), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)

def ro.roots(+s: String, d: Wr.Dec<List<&2, Nat>>, xd: ro.NL(s, d), ok: {LawsBase.wire_opens_err(FPp.answer(FPp.get_req.roots(d))) == False{} : Bool}) -> ro.G(s, FPp.answer(FPp.get_req.roots(d))):
  match d:
    case Wr.Got{+a, +s1}:
      (e1, fa) = xd
      ro.rules(s, a, s1, e1, fa, FPp.get_ns(s1), ro.nl(s1), ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(ro.G(s, Wr.err("path_policy: malformed request")), ok)

def PathPolicy.path_policy_ffi_reads_only_requests(s, ok):
  ro.roots(s, FPp.get_ns(s), ro.nl(s), ok)
