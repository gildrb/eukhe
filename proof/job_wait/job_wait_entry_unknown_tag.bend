# eukhe: the proof of LAW job_wait_entry_unknown_tag
# An encoded tag past 1 reads back as itself, or Bad when too long
# (LAWireSpell.ws_nat_read); either way the entry answers its error form
# and keeps the wait.

import Base
import ../../bend/ffi_job_wait.bend as FJw
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/job_wait.bend as JobWait
import ../wire/base/spell.bend as LAWireSpell

def jwu.end(whole: Bool, +w: FJw.Wt, n: Nat) -> {FJw.step.end(whole, w, 2n+n) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match whole:
    case True{}:
      {==}
    case False{}:
      {==}

def jwu.read(b: Bool, +w: FJw.Wt, +n: Nat, +rest: String) -> {FJw.step.go(w, LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}:
  match b:
    case True{}:
      jwu.end(Wr.end(rest), w, n)
    case False{}:
      {==}

def JobWait.job_wait_entry_unknown_tag(w, n, rest):
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n+n, rest)), LAWireSpell.ws_nat_answer(LawsBase.wire_fits(2n+n), 2n+n, rest), LAWireSpell.ws_nat_read(2n+n, rest)) : {FJw.step.go(w, _) == (FJw.Open{w}, SCon{'E', SCon{' ', "job_wait: malformed event"}}) : FJw.St & String}
  jwu.read(LawsBase.wire_fits(2n+n), w, n, rest)
