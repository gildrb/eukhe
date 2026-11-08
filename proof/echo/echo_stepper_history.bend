# eukhe: the proof of LAW echo_stepper_history
#
# PROOF: the open is `open.start` of the input's reading, so the law is
# eh.open for that reading: a refused open answers its error, then the
# refused error per step (eh.refused); a counting open answers its count,
# then the counts (eh.counts, by induction on the events, with the code's
# n + 1 read as the spec's successor: eh.add_one).

import Base
import ../../bend/ffi_echo.bend as FEc
import ../../bend/wire.bend as Wr
import ../../laws/echo.bend as Echo

# n + 1 is the successor of n
def eh.add_one(n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n), 1n+p, eh.add_one(p))

# a refused stepper replies x, then the refused error per event
def eh.refused(evs: List<&2, String>, +x: String) -> {Echo.ec_feed(evs, (FEc.Refused{}, x)) == x <> Echo.ec_refused(evs) : List<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case e <> t:
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, Echo.ec_feed(t, (FEc.Refused{}, Wr.err("echo: the open was refused"))), Wr.err("echo: the open was refused") <> Echo.ec_refused(t), eh.refused(t, Wr.err("echo: the open was refused")))

def eh.counts(evs: List<&2, String>, +n: Nat, +last: String, +x: String) -> {Echo.ec_feed(evs, (FEc.Echo{n, last}, x)) == x <> Echo.ec_counts(evs, n, last) : List<&2, String>}:
  match evs:
    case Nil{}:
      {==}
    case +e <> t:
      +y = String.append(Nat.show(Nat.add(n, 1n)), SCon{' ', last})
      %eh.add_one(n) : {x <> Echo.ec_feed(t, (FEc.Echo{Nat.add(n, 1n), e}, y)) == x <> (String.append(Nat.show(_), SCon{' ', last}) <> Echo.ec_counts(t, _, e)) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => x <> z, Echo.ec_feed(t, (FEc.Echo{Nat.add(n, 1n), e}, y)), y <> Echo.ec_counts(t, Nat.add(n, 1n), e), eh.counts(t, Nat.add(n, 1n), e, y))

def eh.open(m: Maybe<&2, U32>, evs: List<&2, String>) -> {Echo.ec_feed(evs, FEc.open.start(m)) == Echo.ec_spec(m, evs) : List<&2, String>}:
  match m:
    case None{}:
      eh.refused(evs, Wr.err("echo: open wants a decimal U32"))
    case Some{+k}:
      eh.counts(evs, U32.to_nat(k), "", U32.show(k))

def Echo.echo_stepper_history(input, evs):
  eh.open(U32.read(input), evs)
