# eukhe: the laws of area server_peer

import Base
import ../bend/server_peer.bend as Sp
import ../bend/ffi_server_peer.bend as FSp
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (S1) Whom a client accepts as the listener of an endpoint
# ---------------------------------------------------------
# bend/server_peer.bend, run as the compiled core by
# bend/ffi_server_peer.bend (crates/eukhe-types/src/platform/transport.rs:
# every connect that reaches an abstract endpoint, on Linux, where a
# process of any user can bind a free name first; the listener records its
# pid in eukhe's run dir once bound). Every input is free: any uids, any
# pids, any recorded pid.
#
# R1: a client talks to a listener only when the listener runs as the
#     client's uid and its pid is the pid recorded for the endpoint; 0 is
#     no record, so a listener is never accepted without one.
# R2: a listener of the client's uid whose pid is the recorded one (a pid
#     above 0) is accepted.
# R3 (inferred: what the refusal Rust reports names): a refusal names the
#     first condition of R1 that fails, in the order: another uid; no
#     record; another pid.
# R4: the entry answers each request Rust writes (the listener's uid, the
#     client's uid, the listener's pid, the recorded pid: four Nats within
#     the wire) with the verdict of R1-R3 under Rust's tag (0 served, 1
#     another uid, 2 no record, 3 another pid), reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E server_peer: malformed request`.

# Spec helpers
# ------------

# R4: the reply Rust reads (crates/eukhe-bend/src/rules/server_peer.rs:
# tag 0 Served, 1 OtherUid, 2 NoRecord, 3 OtherPid)
def sp_tag(v: Sp.Served) -> Nat:
  match v:
    case Sp.Served{}:
      0n
    case Sp.OtherUid{}:
      1n
    case Sp.NoRecord{}:
      2n
    case Sp.OtherPid{}:
      3n

# R4: the request Rust writes for q, before rest: its four Nats in order
def sp_spell(q: FSp.Req, rest: String) -> String:
  match q:
    case FSp.Req{p, o, i, c}:
      Wr.put_nat(p, Wr.put_nat(o, Wr.put_nat(i, Wr.put_nat(c, rest))))

# every Nat of q fits the wire
def sp_fits(q: FSp.Req) -> Bool:
  match q:
    case FSp.Req{p, o, i, c}:
      Bool.and(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(o), Bool.and(LawsBase.wire_fits(i), LawsBase.wire_fits(c))))

# R1-R3: the model's verdict on q
def sp_verdict(q: FSp.Req) -> Sp.Served:
  match q:
    case FSp.Req{p, o, i, c}:
      Sp.served(p, o, i, c)

# Laws: the verdict
# -----------------

# LAW server_peer_served_only_recorded_own (R1): a listener is accepted only when its uid is the client's, its pid is the recorded one, and a pid is recorded (not 0)
# EXCLUDES: a listener of another uid accepted (an abstract name another
#   user bound first), a listener whose pid differs from the record, a
#   listener accepted with no record, a check of the uid alone
law server_peer_served_only_recorded_own:
  for +p: Nat
  for +own: Nat
  for +pid: Nat
  for +rec: Nat
  for ok: {Sp.served(p, own, pid, rec) == Sp.Served{} : Sp.Served}
  {p == own : Nat} & ({pid == rec : Nat} & {Nat.is_eq(rec, 0n) == False{} : Bool})

# LAW server_peer_recorded_own_served (R2): a listener of the client's uid whose pid is the recorded pid (any pid above 0) is accepted
# EXCLUDES: a rule that refuses every listener, or the client's own daemon
law server_peer_recorded_own_served:
  for +own: Nat
  for +q: Nat
  {Sp.served(own, own, 1n+q, 1n+q) == Sp.Served{} : Sp.Served}

# LAW server_peer_other_uid (R3): a listener of another uid is refused as another uid, whatever its pid and the record
# EXCLUDES: another uid reported as a missing record or another pid
law server_peer_other_uid:
  for +p: Nat
  for +own: Nat
  for +pid: Nat
  for +rec: Nat
  for ne: {Nat.is_eq(p, own) == False{} : Bool}
  {Sp.served(p, own, pid, rec) == Sp.OtherUid{} : Sp.Served}

# LAW server_peer_no_record (R3): a listener of the client's uid with no recorded pid is refused as no record, whatever its pid
# EXCLUDES: a missing record taken as pid 0 matching a peer pid 0 (a
#   listener in another pid namespace), a missing record reported as
#   another pid
law server_peer_no_record:
  for +own: Nat
  for +pid: Nat
  {Sp.served(own, own, pid, 0n) == Sp.NoRecord{} : Sp.Served}

# LAW server_peer_other_pid (R3): a listener of the client's uid whose pid is not the recorded pid is refused as another pid
# EXCLUDES: another pid reported as another uid or as no record
law server_peer_other_pid:
  for +own: Nat
  for +pid: Nat
  for +q: Nat
  for ne: {Nat.is_eq(pid, 1n+q) == False{} : Bool}
  {Sp.served(own, own, pid, 1n+q) == Sp.OtherPid{} : Sp.Served}

# LAW server_peer_example (R1-R3): anchor: the client's daemon, a squatter of another uid, a listener with no record, a squatter of the same uid, a peer pid 0 with no record
# EXCLUDES: a verdict that ignores the uid, the record or the pid
law server_peer_example:
  {[Sp.served(1000n, 1000n, 4242n, 4242n), Sp.served(1001n, 1000n, 4242n, 4242n), Sp.served(1000n, 1000n, 4242n, 0n), Sp.served(1000n, 1000n, 4243n, 4242n), Sp.served(1000n, 1000n, 0n, 0n)] == [Sp.Served{}, Sp.OtherUid{}, Sp.NoRecord{}, Sp.OtherPid{}, Sp.NoRecord{}] : List<&2, Sp.Served>}

# Laws: the entry (R4)
# --------------------

# LAW server_peer_entry_reads (R4): the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: fields read in another order, a decoder that eats or skips
#   input after the request
law server_peer_entry_reads:
  for +q: FSp.Req
  for +rest: String
  for h: {sp_fits(q) == True{} : Bool}
  {FSp.get_req(sp_spell(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSp.Req>}

# LAW server_peer_entry_answers (R4): the entry answers every request Rust spells (four Nats within the wire) with the model's verdict (pinned by the laws above) under Rust's reply tag
# EXCLUDES: a field misread, a reply tag other than Rust's, a default
law server_peer_entry_answers:
  for +q: FSp.Req
  for h: {sp_fits(q) == True{} : Bool}
  {FSp.ffi(sp_spell(q, "")) == Wr.put_nat(sp_tag(sp_verdict(q)), "") : String}

# LAW server_peer_entry_exact (R4): every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: a verdict made on input that is no request (a malformed
#   number, a missing field, input left over)
law server_peer_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSp.ffi(s)) == False{} : Bool}
  exs q: FSp.Req
  {s == sp_spell(q, "") : String} & {sp_fits(q) == True{} : Bool}

# LAW server_peer_entry_refuses (R4): every error the entry answers is exactly `E server_peer: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law server_peer_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSp.ffi(s)) == True{} : Bool}
  {FSp.ffi(s) == Wr.err("server_peer: malformed request") : String}

# LAW server_peer_entry_example (R4): anchor: the wire strings Rust sends and the replies it reads; a missing field and input left over
# EXCLUDES: tags in another order, fields in another order
law server_peer_entry_example:
  {[FSp.ffi("1000,1000,42,42,"), FSp.ffi("1001,1000,42,42,"), FSp.ffi("1000,1000,42,0,"), FSp.ffi("1000,1000,43,42,"), FSp.ffi("1000,1000,42,"), FSp.ffi("1000,1000,42,42,7,")] == ["0,", "1,", "2,", "3,", Wr.err("server_peer: malformed request"), Wr.err("server_peer: malformed request")] : List<&2, String>}
