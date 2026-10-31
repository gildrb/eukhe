# eukhe: the laws of area call_lift

import Base
import ../bend/call_lift.bend as Cl
import ../bend/ffi_call_lift.bend as FCl
import ../bend/wire.bend as Wr
import ../spec/harness/lift.bend as Sp
import ../spec/harness/lift_wire.bend as SpW

# (H1) Stored calls lifted to the current dialect
# -----------------------------------------------
# bend/call_lift.bend, run as the compiled core by bend/ffi_call_lift.bend
# (eukhe-bend rules/call_lift.rs; asked by eukhe-durable harness/lift.rs
# for the stamped calls of every transcript the context orders, so every
# model request, after a resume, a fork or a model switch, sends the
# calls in their families' current dialects). spec/harness/lift.bend
# restates the lift (L1-L5), spec/harness/lift_wire.bend the wire
# (W1-W3). Every input is free: any table, call, transcript and string;
# the entry's laws hold for the shipped table, Cl.table().
#
# R1: a call's lift is the spec's (L1-L5), for every table.
# R2: a known rev (the current one, or one whose chain arrives) ends at
#     the family's current rev: nothing known is left behind or stranded.
# R3: a lift is idempotent: the call it leaves lifts as current, or as
#     before when it was left untouched.
# R4: a call at its family's current rev, and a call of a family the
#     table lacks, are untouched.
# R5: no argument is lost: every stored argument comes back once, in its
#     order, and every added argument has its filled receipt.
# R6: replay is byte-stable: the spelling of a transcript's lifts is the
#     spelling of each call's lift, one after another, so a turn added
#     after it never changes the bytes before it.
# R7: the entry answers each request Rust writes (W1, every count and
#     name within the wire) with the spelling (W2) of the spec's lifts by
#     the shipped table, and any input that is not exactly one request
#     with exactly `E call_lift: malformed request`.

# Laws: the lift (R1-R5)
# ----------------------

# LAW call_lift_refines_spec (R1): the lift of every call by every table is
# the spec's
# EXCLUDES: a family found by a later row or another name, a step taken
#   from another rev, a chain that loops past the family's steps, ops out
#   of order, a rename of every argument named `from` or onto a taken
#   name, a fill over a present argument, a receipt dropped or reordered,
#   a lifted call that keeps its old rev
law call_lift_refines_spec:
  for +t: List<&2, Cl.Fam>
  for +c: Cl.Call
  {Cl.lift(t, c) == Sp.lift_spec(t, c) : Cl.Lift}

# LAW call_lift_reaches_current (R2): a call at a known rev of its family
# ends at the family's current rev
# EXCLUDES: a known old rev stranded, a lift that stops one step short, a
#   lifted call stamped with an intermediate rev
law call_lift_reaches_current:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for +r: String
  for +ks: List<&2, String>
  for known: {Sp.known(t, f, r) == True{} : Bool}
  {Sp.at_current(t, f, Cl.lift(t, Cl.Call{f, r, ks})) == True{} : Bool}

# LAW call_lift_idempotent (R3): the call a lift leaves lifts as current
# (or as before, when the lift left it untouched)
# EXCLUDES: a lifted call lifted again on the next replay (the ops applied
#   twice), a lift that changes its answer between replays
law call_lift_idempotent:
  for +t: List<&2, Cl.Fam>
  for +c: Cl.Call
  {Cl.lift(t, Sp.applied(c, Cl.lift(t, c))) == Sp.settled(Cl.lift(t, c)) : Cl.Lift}

# LAW call_lift_current_is_identity (R4): a call at its family's current
# rev is current, whatever its arguments
# EXCLUDES: a current call rewritten (its arguments renamed, filled or
#   reordered), a current call stamped again
law call_lift_current_is_identity:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for +r: String
  for +ks: List<&2, String>
  for cur: {Sp.current(t, f) == Some{r} : Maybe<&2, String>}
  {Cl.lift(t, Cl.Call{f, r, ks}) == Cl.Current{} : Cl.Lift}

# LAW call_lift_unknown_family_untouched (R4): a call of a family the table
# lacks is unknown, whatever its rev and arguments
# EXCLUDES: a foreign tool's call (an MCP tool, a plugin) rewritten or
#   stamped by another family's steps
law call_lift_unknown_family_untouched:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for r: String
  for ks: List<&2, String>
  for no: {Sp.current(t, f) == None{} : Maybe<&2, String>}
  {Cl.lift(t, Cl.Call{f, r, ks}) == Cl.Unknown{} : Cl.Lift}

# LAW call_lift_preserves_unmapped (R5): every stored argument comes back
# once, in order (renamed or not), and every added one has a filled
# receipt
# EXCLUDES: an argument the table does not name dropped, duplicated or
#   moved, a rename that drops the argument it renames, a fill without a
#   receipt or a receipt without a fill
law call_lift_preserves_unmapped:
  for +t: List<&2, Cl.Fam>
  for +f: String
  for +r: String
  for +ks: List<&2, String>
  {Sp.kept_of(ks, Cl.lift(t, Cl.Call{f, r, ks})) == Sp.upto(ks, 0n) : List<&2, Nat>} & {Sp.added_of(Cl.lift(t, Cl.Call{f, r, ks})) == Sp.filled_of(Cl.lift(t, Cl.Call{f, r, ks})) : Nat}

# LAW call_lift_replay_byte_stable (R6): the lifts of a transcript spell as
# those of its first part, then those of the rest
# EXCLUDES: a call's spelling that depends on an earlier or later call (a
#   turn added after a prefix changing the prefix's bytes, and with them
#   the provider's prefix cache)
law call_lift_replay_byte_stable:
  for +t: List<&2, Cl.Fam>
  for +xs: List<&2, Cl.Call>
  for +ys: List<&2, Cl.Call>
  for +rest: String
  {FCl.put_lifts(t, List.append(&2, Cl.Call, xs, ys), rest) == FCl.put_lifts(t, xs, FCl.put_lifts(t, ys, rest)) : String}

# LAW call_lift_table_example (R1-R4): anchor: the shipped table: zoom@1
# (9695afec6) lifts to zoom@2 with its arguments as stored, zoom@2 and
# edit@hl.1 are current, an MCP tool is unknown, a zoom rev that never
# existed is stranded
# EXCLUDES: a shipped table that drops a family or a step, or moves a
#   current rev
law call_lift_table_example:
  {[Cl.lift(Cl.table(), Cl.Call{"zoom", "1", ["i", "id", "n"]}), Cl.lift(Cl.table(), Cl.Call{"zoom", "2", ["i", "id"]}), Cl.lift(Cl.table(), Cl.Call{"edit", "hl.1", ["i", "input"]}), Cl.lift(Cl.table(), Cl.Call{"mcp", "1", ["q"]}), Cl.lift(Cl.table(), Cl.Call{"zoom", "0", []})] == [Cl.Lifted{"2", [Cl.Kept{0n, "i"}, Cl.Kept{1n, "id"}, Cl.Kept{2n, "n"}], []}, Cl.Current{}, Cl.Current{}, Cl.Unknown{}, Cl.Stranded{}] : List<&2, Cl.Lift>}

# LAW call_lift_ops_example (R1, R5): anchor: two steps: a rename and a
# fill, then a rename onto a taken name (clashed); a fill of a present
# argument and a rename without its argument do nothing; a cycle strands
# EXCLUDES: a spec that drifts from the receipts Rust records
law call_lift_ops_example:
  {[Cl.lift([Cl.Fam{"t", "3", [Cl.Step{"1", "2", [Cl.Rename{"file", "path"}, Cl.Fill{"limit", "10"}]}, Cl.Step{"2", "3", [Cl.Rename{"a", "path"}]}]}], Cl.Call{"t", "1", ["a", "file", "x"]}), Cl.lift([Cl.Fam{"t", "3", [Cl.Step{"1", "2", [Cl.Rename{"file", "path"}, Cl.Fill{"limit", "10"}]}, Cl.Step{"2", "3", [Cl.Rename{"a", "path"}]}]}], Cl.Call{"t", "2", ["path", "limit"]}), Cl.lift([Cl.Fam{"c", "3", [Cl.Step{"1", "2", []}, Cl.Step{"2", "1", []}]}], Cl.Call{"c", "1", []})] == [Cl.Lifted{"3", [Cl.Kept{0n, "a"}, Cl.Kept{1n, "path"}, Cl.Kept{2n, "x"}, Cl.Added{"limit", "10"}], [Cl.Renamed{"file", "path"}, Cl.Filled{"limit"}, Cl.Clashed{"a", "path"}]}, Cl.Lifted{"3", [Cl.Kept{0n, "path"}, Cl.Kept{1n, "limit"}], []}, Cl.Stranded{}] : List<&2, Cl.Lift>}

# Laws: the entry (R7)
# --------------------

# LAW call_lift_entry_answers (R7): the entry answers every request Rust
# spells, every count and name within the wire, with the spelling of the
# spec's lifts by the shipped table
# EXCLUDES: a field misread or swapped (a family and a rev, two names), a
#   lift tag of another answer, a lift answered for another call or out
#   of order, a count that differs from the calls, a default
law call_lift_entry_answers:
  for +cs: List<&2, Cl.Call>
  for fit: {SpW.fit_req(cs) == True{} : Bool}
  {FCl.ffi(SpW.w_req(cs, "")) == SpW.w_reply(cs) : String}

# LAW call_lift_entry_reads (R7): the laws' reader reads every spelled
# request that fits the wire back whole, so call_lift_entry_malformed_exact
# refuses only what Rust never writes
# EXCLUDES: a reader (and so an entry) that refuses a request Rust writes
law call_lift_entry_reads:
  for +cs: List<&2, Cl.Call>
  for fit: {SpW.fit_req(cs) == True{} : Bool}
  {SpW.read(SpW.w_req(cs, "")) == Some{cs} : Maybe<&2, List<&2, Cl.Call>>}

# LAW call_lift_entry_malformed_exact (R7): every input that is not exactly
# one request (a malformed field, a short list, input left over) gets
# exactly the error form 'E ', then "call_lift: malformed request"
# EXCLUDES: a lift answered for input that is no request, another error
#   text, a default
law call_lift_entry_malformed_exact:
  for +s: String
  for no: {SpW.read(s) == None{} : Maybe<&2, List<&2, Cl.Call>>}
  {FCl.ffi(s) == Wr.err("call_lift: malformed request") : String}

# LAW call_lift_entry_example (R7): anchor: the strings Rust sends and the
# replies it reads: a zoom@1 call lifted next to a current bash call, no
# calls, a stranded rev, an unknown family; input left over and a bare
# count
# EXCLUDES: another spelling of a request or a reply
law call_lift_entry_example:
  {[FCl.ffi("2,4,zoom1,13,1,i2,id1,n4,bash1,11,1,i"), FCl.ffi("0,"), FCl.ffi("1,4,zoom1,00,"), FCl.ffi("1,3,mcp1,10,"), FCl.ffi("1,4,zoom1,20,x"), FCl.ffi("9")] == ["2,3,1,23,0,0,1,i0,1,2,id0,2,1,n0,1,", "0,", "1,2,", "1,0,", Wr.err("call_lift: malformed request"), Wr.err("call_lift: malformed request")] : List<&2, String>}
