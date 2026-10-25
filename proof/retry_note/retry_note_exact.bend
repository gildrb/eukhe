# eukhe: the proof of LAW retry_note_exact

import Base
import ../../bend/retry_note.bend as Rn
import ../../bend/ffi_retry_note.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

# PROOF of LAW retry_note_exact: per cause both sides compute to the same text once the period (0, 1, more) and the reported limit (0, more) are split; the calls the code joins are the spec's join (rn.calls).

def RetryNote.retry_note_exact(a, c):
  match c:
    case Rn.Repeated{p, l}:
      match p:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+q:
          {==}
    case Rn.NoAnswer{}:
      {==}
    case Rn.Length{t, r, k}:
      match t:
        case 0n:
          {==}
        case 1n+u:
          {==}
    case Rn.Leaked{m, why, r, k}:
      {==}
    case Rn.Redirect{cs, n, r, k}:
      %LARetryNote.rn.calls(cs) : {String.append("Harness note, attempt ", String.append(Nat.show(a), String.append(": ", Rn.redirect(n, r, k, _)))) == RetryNote.note_spec(a, Rn.Redirect{cs, n, r, k}) : String}
      {==}
    case Rn.Stalled{ms}:
      {==}
