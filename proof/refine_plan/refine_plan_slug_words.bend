# eukhe: the proof of LAW refine_plan_slug_words
#
# PROOF: the code's text past each writer state (rps.E: nothing written,
# in a word, past a cut) is the spec's words joined from that state, char
# by char (rps.main); the reverse-lead-reverse trim is dropping the
# trailing `_`s (rps.rlr).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan
import ./base/chars.bend as LCh

# s without its trailing `_`s, read forward
def rps.drop.at(u: Bool, c: Char, r: String) -> String:
  match u:
    case False{}:
      SCon{c, r}
    case True{}:
      match r:
        case SNil{}:
          SNil{}
        case SCon{h, t}:
          SCon{c, SCon{h, t}}

def rps.drop(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      rps.drop.at(Char.is_eq(c, '_'), c, rps.drop(t))

# Reversal
# --------

def rps.lr(d: String, acc: String) -> String:
  match d:
    case SNil{}:
      Rp.slug.lead(acc)
    case SCon{h, t}:
      String.reverse.go(SCon{h, t}, acc)

def rps.lr.at(d: String, +c: Char, u: Bool, eu: {Char.is_eq(c, '_') == u : Bool}, +acc: String) -> {rps.lr(d, SCon{c, acc}) == rps.lr(rps.drop.at(u, c, d), acc) : String}:
  match d:
    case SNil{}:
      match u:
        case True{}:
          %Equal.sym(Bool, Char.is_eq(c, '_'), True{}, eu) : {Rp.slug.lead.at(_, c, acc, Rp.slug.lead(acc)) == Rp.slug.lead(acc) : String}
          {==}
        case False{}:
          %Equal.sym(Bool, Char.is_eq(c, '_'), False{}, eu) : {Rp.slug.lead.at(_, c, acc, Rp.slug.lead(acc)) == SCon{c, acc} : String}
          {==}
    case SCon{h, t}:
      match u:
        case True{}:
          {==}
        case False{}:
          {==}

# the leading `_`s of a reversal onto acc: the drop of s reversed onto acc,
# or, when s is all `_`, the leading `_`s of acc dropped
def rps.lead_rev(s: String, +acc: String) -> {Rp.slug.lead(String.reverse.go(s, acc)) == rps.lr(rps.drop(s), acc) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(String, Rp.slug.lead(String.reverse.go(t, SCon{c, acc})), rps.lr(rps.drop(t), SCon{c, acc}), rps.lr(rps.drop.at(Char.is_eq(c, '_'), c, rps.drop(t)), acc), rps.lead_rev(t, SCon{c, acc}), rps.lr.at(rps.drop(t), c, Char.is_eq(c, '_'), {==}, acc))

def rps.rev_rev(a: String, acc: String) -> {String.reverse.go(String.reverse.go(a, acc), SNil{}) == String.reverse.go(acc, a) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rps.rev_rev(t, SCon{h, acc})

def rps.rlr.at(d: String) -> {String.reverse.go(rps.lr(d, SNil{}), SNil{}) == d : String}:
  match d:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rps.rev_rev(SCon{h, t}, SNil{})

# the trailing `_`s dropped by reversing, dropping the leading ones, reversing
def rps.rlr(+s: String) -> {String.reverse(Rp.slug.lead(String.reverse(s))) == rps.drop(s) : String}:
  %Equal.sym(String, Rp.slug.lead(String.reverse.go(s, SNil{})), rps.lr(rps.drop(s), SNil{}), rps.lead_rev(s, SNil{})) : {String.reverse.go(_, SNil{}) == rps.drop(s) : String}
  rps.rlr.at(rps.drop(s))

# One char
# --------

# a char other than `_`: squeezing, leading and trailing drops keep it
def rps.sq_keep(+c: Char, ec: {Char.is_eq(c, '_') == False{} : Bool}, +m: String) -> {Rp.slug.squeeze(SCon{c, m}) == SCon{c, Rp.slug.squeeze(m)} : String}:
  %Equal.sym(Bool, Char.is_eq(c, '_'), False{}, ec) : {Rp.slug.squeeze.at(Bool.and(_, String.starts_with(m, "_")), c, Rp.slug.squeeze(m)) == SCon{c, Rp.slug.squeeze(m)} : String}
  {==}

def rps.lead_keep(+c: Char, ec: {Char.is_eq(c, '_') == False{} : Bool}, +r: String) -> {Rp.slug.lead(SCon{c, r}) == SCon{c, r} : String}:
  %Equal.sym(Bool, Char.is_eq(c, '_'), False{}, ec) : {Rp.slug.lead.at(_, c, r, Rp.slug.lead(r)) == SCon{c, r} : String}
  {==}

def rps.drop_keep(+c: Char, ec: {Char.is_eq(c, '_') == False{} : Bool}, +r: String) -> {rps.drop(SCon{c, r}) == SCon{c, rps.drop(r)} : String}:
  %Equal.sym(Bool, Char.is_eq(c, '_'), False{}, ec) : {rps.drop.at(_, c, rps.drop(r)) == SCon{c, rps.drop(r)} : String}
  {==}

def rps.sw_keep(+c: Char, ec: {Char.is_eq(c, '_') == False{} : Bool}, +m: String) -> {String.starts_with(SCon{c, m}, "_") == False{} : Bool}:
  %Equal.sym(Bool, Char.is_eq(c, '_'), False{}, ec) : {String.starts_with.go.if(SNil{}, m, _) == False{} : Bool}
  {==}

# the code's text past a writer state: nothing written, in a word, past a cut
def rps.E(at: RefinePlan.RsAt, m: String) -> String:
  match at:
    case RefinePlan.RsStart{}:
      rps.drop(Rp.slug.lead(Rp.slug.squeeze(m)))
    case RefinePlan.RsIn{}:
      rps.drop(Rp.slug.squeeze(m))
    case RefinePlan.RsGap{}:
      rps.drop(Rp.slug.squeeze(SCon{'_', m}))

def rps.cut_lead(b: Bool, +s: String) -> {Rp.slug.lead(Rp.slug.squeeze.at(b, '_', s)) == Rp.slug.lead(s) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a slug char c (not `_`) written in each state
def rps.keep(+c: Char, +ec: {Char.is_eq(c, '_') == False{} : Bool}, +m: String, +g: String, ih: {rps.E(RefinePlan.RsIn{}, m) == g : String}, +at: RefinePlan.RsAt) -> {rps.E(at, SCon{c, m}) == RefinePlan.rs_slug.word(at, c, g) : String}:
  match at:
    case RefinePlan.RsStart{}:
      %Equal.sym(String, Rp.slug.squeeze(SCon{c, m}), SCon{c, Rp.slug.squeeze(m)}, rps.sq_keep(c, ec, m)) : {rps.drop(Rp.slug.lead(_)) == SCon{c, g} : String}
      %Equal.sym(String, Rp.slug.lead(SCon{c, Rp.slug.squeeze(m)}), SCon{c, Rp.slug.squeeze(m)}, rps.lead_keep(c, ec, Rp.slug.squeeze(m))) : {rps.drop(_) == SCon{c, g} : String}
      %Equal.sym(String, rps.drop(SCon{c, Rp.slug.squeeze(m)}), SCon{c, rps.drop(Rp.slug.squeeze(m))}, rps.drop_keep(c, ec, Rp.slug.squeeze(m))) : {_ == SCon{c, g} : String}
      %ih : {SCon{c, rps.drop(Rp.slug.squeeze(m))} == SCon{c, _} : String}
      {==}
    case RefinePlan.RsIn{}:
      %Equal.sym(String, Rp.slug.squeeze(SCon{c, m}), SCon{c, Rp.slug.squeeze(m)}, rps.sq_keep(c, ec, m)) : {rps.drop(_) == SCon{c, g} : String}
      %Equal.sym(String, rps.drop(SCon{c, Rp.slug.squeeze(m)}), SCon{c, rps.drop(Rp.slug.squeeze(m))}, rps.drop_keep(c, ec, Rp.slug.squeeze(m))) : {_ == SCon{c, g} : String}
      %ih : {SCon{c, rps.drop(Rp.slug.squeeze(m))} == SCon{c, _} : String}
      {==}
    case RefinePlan.RsGap{}:
      %Equal.sym(Bool, String.starts_with(SCon{c, m}, "_"), False{}, rps.sw_keep(c, ec, m)) : {rps.drop(Rp.slug.squeeze.at(Bool.and(True{}, _), '_', Rp.slug.squeeze(SCon{c, m}))) == SCon{'_', SCon{c, g}} : String}
      %Equal.sym(String, Rp.slug.squeeze(SCon{c, m}), SCon{c, Rp.slug.squeeze(m)}, rps.sq_keep(c, ec, m)) : {rps.drop(SCon{'_', _}) == SCon{'_', SCon{c, g}} : String}
      %Equal.sym(String, rps.drop(SCon{c, Rp.slug.squeeze(m)}), SCon{c, rps.drop(Rp.slug.squeeze(m))}, rps.drop_keep(c, ec, Rp.slug.squeeze(m))) : {rps.drop.at(True{}, '_', _) == SCon{'_', SCon{c, g}} : String}
      %ih : {SCon{'_', SCon{c, rps.drop(Rp.slug.squeeze(m))}} == SCon{'_', SCon{c, _}} : String}
      {==}

# U+0130: `i`, then a cut
def rps.dotted(+m: String, +g: String, ih: {rps.E(RefinePlan.RsGap{}, m) == g : String}, +at: RefinePlan.RsAt) -> {rps.E(at, SCon{'i', SCon{'_', m}}) == RefinePlan.rs_slug.word(at, 'i', g) : String}:
  match at:
    case RefinePlan.RsStart{}:
      %ih : {rps.E(RefinePlan.RsStart{}, SCon{'i', SCon{'_', m}}) == SCon{'i', _} : String}
      {==}
    case RefinePlan.RsIn{}:
      %ih : {rps.E(RefinePlan.RsIn{}, SCon{'i', SCon{'_', m}}) == SCon{'i', _} : String}
      {==}
    case RefinePlan.RsGap{}:
      %ih : {rps.E(RefinePlan.RsGap{}, SCon{'i', SCon{'_', m}}) == SCon{'_', SCon{'i', _}} : String}
      {==}

# a cut
def rps.cut(+m: String, -t: String, ih0: {rps.E(RefinePlan.RsStart{}, m) == RefinePlan.rs_slug.go(t, RefinePlan.RsStart{}) : String}, ih2: {rps.E(RefinePlan.RsGap{}, m) == RefinePlan.rs_slug.go(t, RefinePlan.RsGap{}) : String}, +at: RefinePlan.RsAt) -> {rps.E(at, SCon{'_', m}) == RefinePlan.rs_slug.go(t, RefinePlan.rs_slug.next(RefinePlan.RsCut{}, at)) : String}:
  match at:
    case RefinePlan.RsStart{}:
      %Equal.sym(String, Rp.slug.lead(Rp.slug.squeeze(SCon{'_', m})), Rp.slug.lead(Rp.slug.squeeze(m)), rps.cut_lead(String.starts_with(m, "_"), Rp.slug.squeeze(m))) : {rps.drop(_) == RefinePlan.rs_slug.go(t, RefinePlan.RsStart{}) : String}
      ih0
    case RefinePlan.RsIn{}:
      ih2
    case RefinePlan.RsGap{}:
      ih2

# an alphanumeric ASCII char is not `_`
def rps.alnum.at(+c: Char, b: Bool, eb: {Char.is_eq(c, '_') == b : Bool}, eA: {Bool.or(Char.is_lower(c), Char.is_digit(c)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +ce = LCh.char_sound(c, '_', eb)
      LCh.absurdF({True{} == False{} : Bool}, Equal.trans(Bool, False{}, Bool.or(Char.is_lower(c), Char.is_digit(c)), True{}, Equal.sym(Bool, Bool.or(Char.is_lower(c), Char.is_digit(c)), False{}, Equal.cong(Char, Bool, x => Bool.or(Char.is_lower(x), Char.is_digit(x)), c, '_', ce)), eA))

def rps.alnum(+c: Char, eA: {Bool.or(Char.is_lower(c), Char.is_digit(c)) == True{} : Bool}) -> {Char.is_eq(c, '_') == False{} : Bool}:
  rps.alnum.at(c, Char.is_eq(c, '_'), {==}, eA)

# one char of the title: the code's text and the spec's agree in every state
def rps.step(+A: Bool, +Up: Bool, +D: Bool, +K: Bool, +c: Char, eA: {Bool.or(Char.is_lower(c), Char.is_digit(c)) == A : Bool}, eU: {Char.is_upper(c) == Up : Bool}, +m: String, +t: String, ih0: {rps.E(RefinePlan.RsStart{}, m) == RefinePlan.rs_slug.go(t, RefinePlan.RsStart{}) : String}, ih1: {rps.E(RefinePlan.RsIn{}, m) == RefinePlan.rs_slug.go(t, RefinePlan.RsIn{}) : String}, ih2: {rps.E(RefinePlan.RsGap{}, m) == RefinePlan.rs_slug.go(t, RefinePlan.RsGap{}) : String}, +at: RefinePlan.RsAt) -> {rps.E(at, Rp.slug.put.at(A, Up, D, K, c, m)) == RefinePlan.rs_slug.put(RefinePlan.rs_ch.at(A, Up, D, K, c), at, RefinePlan.rs_slug.go(t, RefinePlan.rs_slug.next(RefinePlan.rs_ch.at(A, Up, D, K, c), at))) : String}:
  match A:
    case True{}:
      rps.keep(c, rps.alnum(c, eA), m, RefinePlan.rs_slug.go(t, RefinePlan.RsIn{}), ih1, at)
    case False{}:
      match Up:
        case True{}:
          rps.keep(Char.to_lower(c), LCh.up.lower(c, eU), m, RefinePlan.rs_slug.go(t, RefinePlan.RsIn{}), ih1, at)
        case False{}:
          match D:
            case True{}:
              rps.dotted(m, RefinePlan.rs_slug.go(t, RefinePlan.RsGap{}), ih2, at)
            case False{}:
              match K:
                case True{}:
                  rps.keep('k', {==}, m, RefinePlan.rs_slug.go(t, RefinePlan.RsIn{}), ih1, at)
                case False{}:
                  rps.cut(m, t, ih0, ih2, at)

def rps.main(raw: String, +at: RefinePlan.RsAt) -> {rps.E(at, Rp.slug.marks(raw)) == RefinePlan.rs_slug.go(raw, at) : String}:
  match raw:
    case SNil{}:
      match at:
        case RefinePlan.RsStart{}:
          {==}
        case RefinePlan.RsIn{}:
          {==}
        case RefinePlan.RsGap{}:
          {==}
    case SCon{+c, +t}:
      rps.step(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, {==}, {==}, Rp.slug.marks(t), t, rps.main(t, RefinePlan.RsStart{}), rps.main(t, RefinePlan.RsIn{}), rps.main(t, RefinePlan.RsGap{}), at)

def rps.pick(+t: String, fb: String) -> {Rp.slug.pick(String.is_empty(t), t, fb) == RefinePlan.rs_slug.or(t, fb) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{h, r}:
      {==}

def rps.slug(+raw: String, +fb: String) -> {Rp.slug(raw, fb) == RefinePlan.rs_slug(raw, fb) : String}:
  +X = Rp.slug.lead(Rp.slug.squeeze(Rp.slug.marks(raw)))
  +T = String.take(String.reverse(Rp.slug.lead(String.reverse(X))), 80n)
  %Equal.sym(String, Rp.slug.pick(String.is_empty(T), T, fb), RefinePlan.rs_slug.or(T, fb), rps.pick(T, fb)) : {_ == RefinePlan.rs_slug(raw, fb) : String}
  %Equal.sym(String, String.reverse(Rp.slug.lead(String.reverse(X))), rps.drop(X), rps.rlr(X)) : {RefinePlan.rs_slug.or(String.take(_, 80n), fb) == RefinePlan.rs_slug(raw, fb) : String}
  %Equal.sym(String, rps.E(RefinePlan.RsStart{}, Rp.slug.marks(raw)), RefinePlan.rs_slug.go(raw, RefinePlan.RsStart{}), rps.main(raw, RefinePlan.RsStart{})) : {RefinePlan.rs_slug.or(String.take(_, 80n), fb) == RefinePlan.rs_slug(raw, fb) : String}
  {==}

def RefinePlan.refine_plan_slug_words(raw, fb):
  rps.slug(raw, fb)
