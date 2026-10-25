# eukhe: lemmas shared by the proofs of area overflow: the code's lazy
# message test is its strict form, whose searches are the spec's
# (text_pat_any, text_pat_hit) over the spec's tables (both compute to the
# same alternatives), and each part of the decision is the spec's, stop by
# stop

import Base
import ../../bend/text_pat.bend as Tp
import ../../bend/overflow.bend as O
import ../../bend/ffi_overflow.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/text_pat.bend as TextPat
import ../../laws/overflow.bend as Overflow
import ../text_pat/text_pat_fold.bend as PTextPatFold
import ../text_pat/text_pat_any.bend as PTextPatAny
import ../text_pat/text_pat_hit.bend as PTextPatHit

# Logic
# -----

def ovb.or_lazy(a: Bool, b: Bool) -> {Tp.pm.or(a, u => b) == Bool.or(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ovb.and_lazy(a: Bool, b: Bool) -> {Tp.pm.and(a, u => b) == Bool.and(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ovb.or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ovb.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# The decision
# ------------

# the message test on a folded text f is the spec's
def ovb.msg_f(+f: String, +msg: String, +p: String) -> {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(f, O.calm_pats())), Bool.or(Tp.any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))) == Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(p, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) : Bool}:
  %Equal.sym(Bool, Tp.any(f, O.calm_pats()), TextPat.sp_any(f, O.calm_pats()), TextPat.text_pat_any(f, O.calm_pats())) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(_), Bool.or(Tp.any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))) == Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(p, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) : Bool}
  %Equal.sym(Bool, Tp.any(f, O.overflow_pats()), TextPat.sp_any(f, O.overflow_pats()), TextPat.text_pat_any(f, O.overflow_pats())) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, O.calm_pats())), Bool.or(_, Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))) == Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(p, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) : Bool}
  %Equal.sym(Bool, Tp.hit(f, O.cerebras_pat()), TextPat.sp_any(f, [O.cerebras_pat()]), TextPat.text_pat_hit(f, O.cerebras_pat())) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, O.calm_pats())), Bool.or(TextPat.sp_any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), _)))) == Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(p, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()]))))) : Bool}
  {==}

# the code's lazy message test is its strict form
def ovb.lazy(+f: String, +msg: String, +p: String) -> {Tp.pm.and(Bool.not(String.is_empty(msg)), u => Tp.pm.and(Bool.not(Tp.any(f, O.calm_pats())), v => Tp.pm.or(Tp.any(f, O.overflow_pats()), w => Tp.pm.and(String.eq(p, "cerebras"), x => Tp.hit(f, O.cerebras_pat()))))) == Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(f, O.calm_pats())), Bool.or(Tp.any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))) : Bool}:
  +ce = String.eq(p, "cerebras")
  +hc = Tp.hit(f, O.cerebras_pat())
  +ao = Tp.any(f, O.overflow_pats())
  +nc = Bool.not(Tp.any(f, O.calm_pats()))
  +ne = Bool.not(String.is_empty(msg))
  %Equal.sym(Bool, Tp.pm.and(ce, x => hc), Bool.and(ce, hc), ovb.and_lazy(ce, hc)) : {Tp.pm.and(ne, u => Tp.pm.and(nc, v => Tp.pm.or(ao, w => _))) == Bool.and(ne, Bool.and(nc, Bool.or(ao, Bool.and(ce, hc)))) : Bool}
  %Equal.sym(Bool, Tp.pm.or(ao, w => Bool.and(ce, hc)), Bool.or(ao, Bool.and(ce, hc)), ovb.or_lazy(ao, Bool.and(ce, hc))) : {Tp.pm.and(ne, u => Tp.pm.and(nc, v => _)) == Bool.and(ne, Bool.and(nc, Bool.or(ao, Bool.and(ce, hc)))) : Bool}
  %Equal.sym(Bool, Tp.pm.and(nc, v => Bool.or(ao, Bool.and(ce, hc))), Bool.and(nc, Bool.or(ao, Bool.and(ce, hc))), ovb.and_lazy(nc, Bool.or(ao, Bool.and(ce, hc)))) : {Tp.pm.and(ne, u => _) == Bool.and(ne, Bool.and(nc, Bool.or(ao, Bool.and(ce, hc)))) : Bool}
  ovb.and_lazy(ne, Bool.and(nc, Bool.or(ao, Bool.and(ce, hc))))

# the code's message test is the spec's
def ovb.message(+msg: String, +p: String) -> {O.message_overflow(msg, p) == Overflow.sp_message(msg, p) : Bool}:
  +f = Tp.fold_str(msg)
  %Equal.sym(Bool, Tp.pm.and(Bool.not(String.is_empty(msg)), u => Tp.pm.and(Bool.not(Tp.any(f, O.calm_pats())), v => Tp.pm.or(Tp.any(f, O.overflow_pats()), w => Tp.pm.and(String.eq(p, "cerebras"), x => Tp.hit(f, O.cerebras_pat()))))), Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(f, O.calm_pats())), Bool.or(Tp.any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))), ovb.lazy(f, msg, p)) : {_ == Overflow.sp_message(msg, p) : Bool}
  %Equal.sym(String, Tp.fold_str(msg), TextPat.sp_fold(msg), TextPat.text_pat_fold(msg)) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(_, O.calm_pats())), Bool.or(Tp.any(_, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(_, O.cerebras_pat()))))) == Overflow.sp_message(msg, p) : Bool}
  ovb.msg_f(TextPat.sp_fold(msg), msg, p)

# the code's usage test is the spec's, stop by stop
def ovb.usage(st: O.Stop, +w: Nat, +u: Nat, o: Nat) -> {O.usage_overflow(st, w, u, o) == Overflow.sp_usage(st, w, u, o) : Bool}:
  match st:
    case O.SStop{}:
      %Equal.sym(Bool, Bool.or(Nat.is_lt(w, u), False{}), Nat.is_lt(w, u), ovb.or_false(Nat.is_lt(w, u))) : {Bool.and(Nat.is_lt(0n, w), _) == Bool.and(Nat.is_lt(0n, w), Nat.is_lt(w, u)) : Bool}
      {==}
    case O.SLength{}:
      {==}
    case O.SOther{}:
      ovb.and_false(Nat.is_lt(0n, w))
    case O.SError{}:
      ovb.and_false(Nat.is_lt(0n, w))

def ovb.err(st: O.Stop) -> {O.is_error(st) == Overflow.sp_is_error(st) : Bool}:
  match st:
    case O.SStop{}:
      {==}
    case O.SLength{}:
      {==}
    case O.SOther{}:
      {==}
    case O.SError{}:
      {==}
