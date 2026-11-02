# eukhe: the laws of area stop, section entry: the entry of the compiled
# core for the Directors at a candidate stop (bend/ffi_stop.bend) on
# every input, stated with a reader built only from the wire primitives
# of bend/wire.bend and the spellers and spec answers of laws/stop.bend

import Base
import ../../bend/stop.bend as S
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../stop.bend as LawsStop

# LAWS (R6 of laws/stop.bend, on every input): an input that is exactly
# one request Rust writes (eukhe-durable harness/generation/stop.rs: 0 the
# walk: cut, text, broken, pending (Bools); 1 a length note: the attempt,
# then the cut reply's tokens, row, cap (Nats); 2 the round note: max,
# done (Nats)) answers the spelled spec answer (LawsStop.sp_w_reply); any
# other input (a tag past 2, a field missing or malformed, input left
# over) answers exactly `E stop: malformed request`.

# The reader of a request
# -----------------------

def st.r_walk.pending(c: Bool, t: Bool, b: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{p, s}:
      Wr.Got{FS.AskWalk{S.Facts{c, t, b, p}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_walk.broken(c: Bool, t: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{b, s}:
      st.r_walk.pending(c, t, b, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_walk.text(c: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{t, s}:
      st.r_walk.broken(c, t, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_walk.cut(d: Wr.Dec<Bool>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{c, s}:
      st.r_walk.text(c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_note.cap(a: Nat, t: Nat, w: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{k, s}:
      Wr.Got{FS.AskNote{a, S.Cut{t, w, k}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_note.row(a: Nat, t: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{w, s}:
      st.r_note.cap(a, t, w, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_note.tokens(a: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{t, s}:
      st.r_note.row(a, t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_note.attempt(d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{a, s}:
      st.r_note.tokens(a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_rounds.done(m: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{n, s}:
      Wr.Got{FS.AskRounds{m, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_rounds.max(d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{m, s}:
      st.r_rounds.done(m, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def st.r_ask.tag(d: Wr.Dec<Nat>) -> Wr.Dec<FS.Ask>:
  match d:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          st.r_walk.cut(Wr.get_bool(s))
        case 1n:
          st.r_note.attempt(Wr.get_nat(s))
        case 2n:
          st.r_rounds.max(Wr.get_nat(s))
        case 3n+k:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s, and the input after it
def st.r_ask(s: String) -> Wr.Dec<FS.Ask>:
  st.r_ask.tag(Wr.get_nat(s))

# The entry
# ---------

def st.entry.end(whole: Bool, a: FS.Ask) -> String:
  match whole:
    case True{}:
      LawsStop.sp_w_reply(a)
    case False{}:
      Wr.err("stop: malformed request")

def st.entry.go(d: Wr.Dec<FS.Ask>) -> String:
  match d:
    case Wr.Got{a, s}:
      st.entry.end(Wr.end(s), a)
    case Wr.Bad{}:
      Wr.err("stop: malformed request")

# the answer to the input s
def st.entry(s: String) -> String:
  st.entry.go(st.r_ask(s))

# Laws
# ----

# LAW stop_entry_exact (R6): on every input the entry answers exactly the
# spelled spec answer of the request the input is (read whole), and
# `E stop: malformed request` on any other input
# EXCLUDES: a default answer for a malformed request (a field missing, a
#   char that is no Bool, a Nat with no end mark), a field read into
#   another, input left over ignored, another error text
law stop_entry_exact:
  for +s: String
  {FS.ffi(s) == st.entry(s) : String}

# LAW stop_entry_reads (R6): the reader reads every request Rust writes,
# every Nat within the wire, back whole, and leaves the input after it
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law stop_entry_reads:
  for +a: FS.Ask
  for +rest: String
  for h: {LawsStop.sp_fit(a) == True{} : Bool}
  {st.r_ask(LawsStop.sp_w_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FS.Ask>}

# LAW stop_entry_malformed_example (R6): anchor: a walk with a fact
# missing, a walk with a char that is no Bool, a note with a field
# missing, a round note with a Nat with no end mark: each is refused
# EXCLUDES: a default pick or note for a request Rust never writes
law stop_entry_malformed_example:
  {[FS.ffi("0,FTF"), FS.ffi("0,FTFX"), FS.ffi("1,3,0,1,"), FS.ffi("2,250,1")] == [Wr.err("stop: malformed request"), Wr.err("stop: malformed request"), Wr.err("stop: malformed request"), Wr.err("stop: malformed request")] : List<&2, String>}
