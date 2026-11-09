# eukhe: the laws of area stop, section entry: the reader of the entry of
# the compiled core for the Directors at a candidate stop
# (bend/ffi_stop.bend `get_ask`, the decoder `ffi` runs) on every input,
# stated with the spellers of laws/stop.bend (sp_w_ask, built from the
# wire primitives of bend/wire.bend)

import Base
import ../../bend/ffi_stop.bend as FS
import ../../bend/wire.bend as Wr
import ../stop.bend as LawsStop

# LAWS (R6 of laws/stop.bend, on every input): the entry's reader reads
# exactly the requests Rust writes (eukhe-durable harness/generation/
# stop.rs: 0 the walk: cut, text, broken, pending (Bools); 1 a length
# note: the attempt, then the cut reply's tokens, row, cap (Nats); 2 the
# round note: max, done (Nats)): each spelled request back whole, and
# nothing else; laws/stop.bend states what the entry answers to them.

# LAW stop_entry_reads (R6): the entry's reader reads every request Rust
# writes, every Nat within the wire, back whole, and leaves the input
# after it
# EXCLUDES: a reader (and so an entry) that refuses or misreads a request
#   Rust writes, or eats the input after it
law stop_entry_reads:
  for +a: FS.Ask
  for +rest: String
  for h: {LawsStop.sp_fit(a) == True{} : Bool}
  {FS.get_ask(LawsStop.sp_w_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FS.Ask>}

# LAW stop_entry_reads_only_spelled (R6): an input the entry's reader
# accepts is exactly a spelled request (the request it read, then the
# rest): the reader refuses every other input (a tag past 2, a field
# missing, a char that is no Bool, a Nat spelled another way or with no
# end mark). What the entry answers to a refused input is stated by
# stop_entry_unknown, stop_entry_left_over and the anchors, not here
# EXCLUDES: a default request read from malformed input, a second spelling
#   of a request accepted
law stop_entry_reads_only_spelled:
  for +s: String
  for +a: FS.Ask
  for +rest: String
  for h: {FS.get_ask(s) == Wr.Got{a, rest} : Wr.Dec<FS.Ask>}
  {s == LawsStop.sp_w_ask(a, rest) : String}

# LAW stop_entry_malformed_example (R6): anchor: a walk with a fact
# missing, a walk with a char that is no Bool, a note with a field
# missing, a round note with a Nat with no end mark: each is refused
# EXCLUDES: a default pick or note for a request Rust never writes
law stop_entry_malformed_example:
  {[FS.ffi("0,FTF"), FS.ffi("0,FTFX"), FS.ffi("1,3,0,1,"), FS.ffi("2,250,1")] == [Wr.err("stop: malformed request"), Wr.err("stop: malformed request"), Wr.err("stop: malformed request"), Wr.err("stop: malformed request")] : List<&2, String>}
