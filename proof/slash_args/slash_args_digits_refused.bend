# eukhe: the proof of LAW slash_args_digits_refused
#
# PROOF: the code's positive test is the law's leading digit test
# (LA.sab.positive_lead), False here; the u64 test needs it, the
# keep-alive test needs it or the text `0`.

import Base
import ../../bend/slash_args.bend as Sa
import ../../laws/slash_args/model.bend as SlashArgs
import ./base.bend as LA

def sdr.or_f(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def SlashArgs.slash_args_digits_refused(s, n):
  +pf = Equal.trans(Bool, Sa.positive(s), SlashArgs.sa_lead(s), False{}, LA.sab.positive_lead(s), n)
  (Equal.cong(Bool, Bool, y => Bool.and(y, Bool.or(Nat.is_lt(String.length(s), 20n), Bool.and(Nat.is_eq(String.length(s), 20n), String.is_le(s, "18446744073709551615")))), Sa.positive(s), False{}, pf), Equal.trans(Bool, Sa.keep_ok(s), Bool.or(String.eq(s, "0"), False{}), String.eq(s, "0"), Equal.cong(Bool, Bool, y => Bool.or(String.eq(s, "0"), Bool.and(y, Bool.or(Nat.is_lt(String.length(s), 10n), Bool.and(Nat.is_eq(String.length(s), 10n), String.is_le(s, "2147483647"))))), Sa.positive(s), False{}, pf), sdr.or_f(String.eq(s, "0"))))
