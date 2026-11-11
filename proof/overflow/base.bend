# eukhe: lemmas shared by the proofs of area overflow: the code's lazy
# message test is its strict form (ovb.strict), whose searches are the
# laws' matcher (text_pat_any, text_pat_hit) over the laws' tables (both
# compute to the same alternatives)

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

# the message test in strict form, searched with the laws' matcher over
# the laws' tables (a proof term, not a spec: the laws state properties of
# O.message_overflow)
def ovb.strict(+msg: String, +p: String) -> Bool:
  +f = TextPat.sp_fold(msg)
  Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(TextPat.sp_any(f, Overflow.sp_calm_pats())), Bool.or(TextPat.sp_any(f, Overflow.sp_overflow_pats()), Bool.and(String.eq(p, "cerebras"), TextPat.sp_any(f, [Overflow.sp_cerebras()])))))

# the code's message test is its strict form
def ovb.message(+msg: String, +p: String) -> {O.message_overflow(msg, p) == ovb.strict(msg, p) : Bool}:
  +f = Tp.fold_str(msg)
  %Equal.sym(Bool, Tp.pm.and(Bool.not(String.is_empty(msg)), u => Tp.pm.and(Bool.not(Tp.any(f, O.calm_pats())), v => Tp.pm.or(Tp.any(f, O.overflow_pats()), w => Tp.pm.and(String.eq(p, "cerebras"), x => Tp.hit(f, O.cerebras_pat()))))), Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(f, O.calm_pats())), Bool.or(Tp.any(f, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(f, O.cerebras_pat()))))), ovb.lazy(f, msg, p)) : {_ == ovb.strict(msg, p) : Bool}
  %Equal.sym(String, Tp.fold_str(msg), TextPat.sp_fold(msg), TextPat.text_pat_fold(msg)) : {Bool.and(Bool.not(String.is_empty(msg)), Bool.and(Bool.not(Tp.any(_, O.calm_pats())), Bool.or(Tp.any(_, O.overflow_pats()), Bool.and(String.eq(p, "cerebras"), Tp.hit(_, O.cerebras_pat()))))) == ovb.strict(msg, p) : Bool}
  ovb.msg_f(TextPat.sp_fold(msg), msg, p)
