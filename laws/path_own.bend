# eukhe: the laws of area path_own

import Base
import ../bend/path_policy.bend as Pp
import ../bend/path_own.bend as Po
import ../bend/ffi_path_own.bend as FPo
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (I3, I13) The own paths
# -----------------------
# spec/README.md I3, I13. bend/path_own.bend: the agent can't write
# Eukhe's own config and credentials, the session record or a protected
# file of a check under acceptance; nothing asks, the write is refused.
# The caller (eukhe-shell, the document tools) names these places with
# own rules (eukhe-core durable/path_policy.rs `own`, set on the policy
# by eukhe-types `PathPolicy::with_own`: the agent dir as a Dir rule, the
# agent profiles dir, each settings file the session reads, the sessions
# and sessions-archive dirs and each --protect file of a set check as
# Tree rules), resolves the path an access touches to its real path
# (eukhe-types path_policy::resolve; names deepest first) and asks the
# class of the access, given the path policy's class of the path
# (eukhe-shell paths::own_write). It runs as the compiled core by
# bend/ffi_path_own.bend (eukhe-bend rules/path_own.rs). Every input is
# free: any rules, any path, any class.
#
# R1 (I3): a read keeps the judge's class: no read is Own.
# R2 (I3): a write no own rule names keeps the judge's class.
# R3 (I3): a Tree rule names its path and everything under it, and
#     nothing else: a write there is Own, whatever the judge's class.
# R4 (I3): a Dir rule names its directory and each entry directly in it,
#     and nothing else (nothing deeper, nothing above): a write there is
#     Own, whatever the judge's class.
# R5 (I3): of the rules, the first that names a write gives the place the
#     answer names (from 0), so the caller can say why.
# R6 (I13): the entry answers each request Rust writes (every number
#     within the wire) with the model's answer, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E path_own: malformed request`.
#
# Not pinned here, gated by Rust tests: the own places in the rules
# (eukhe_core::durable::path_policy::tests::
# every_loader_file_and_the_session_record_are_own); the real paths
# (eukhe_types::path_policy::tests::
# real_paths_follow_links_on_the_existing_part); that an Own write is
# refused with the path and why, and in a script it and the steps after
# it do not run (eukhe_shell::run::tests::
# every_step_runs_unasked_and_an_own_write_stops_the_script and
# an_own_write_in_a_pipeline_runs_none_of_its_stages;
# eukhe_core::durable::path_policy::tests::
# a_document_write_to_an_own_path_is_refused; every client:
# irreversible_unasked_e2e).

# Spec helpers
# ------------

# R2-R5: the answer of rules xs then ys, from the answers of xs (a) and
# of ys (b) and the number n of rules of xs: a's place when xs names the
# write, else b with its place n further on
def po_then(a: Po.Wc, n: Nat, b: Po.Wc) -> Po.Wc:
  match a:
    case Po.Own{i}:
      Po.Own{i}
    case Po.Judged{c}:
      match b:
        case Po.Own{j}:
          Po.Own{Nat.add(n, j)}
        case Po.Judged{d}:
          Po.Judged{d}

# R6: the wire code of a class
def sp_po_code(c: Pp.Cls) -> Nat:
  match c:
    case Pp.Inside{}:
      0n
    case Pp.Outside{}:
      1n
    case Pp.Protected{}:
      2n
    case Pp.Secret{}:
      3n

# R2-R4: the answer of one rule is Own at place 0 or the judge's class c
def po_one(x: Po.Wc, +c: Pp.Cls) -> Bool:
  match x:
    case Po.Own{i}:
      Nat.is_eq(i, 0n)
    case Po.Judged{d}:
      Nat.is_eq(sp_po_code(d), sp_po_code(c))

# R6: 1 + each name of xs
def po_succ(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> rest:
      (1n+x) <> po_succ(rest)

# R6: a list of paths as one list of Nats: each path's names (1 + name),
# then 0
def po_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> rest:
      List.append(&2, Nat, po_succ(xs), 0n <> po_flat(rest))

# R6: a rule as a path: 0 then its path (Tree), 1 then its path (Dir)
def sp_po_rule(r: Po.Rule) -> List<&2, Nat>:
  match r:
    case Po.Tree{p}:
      0n <> p
    case Po.Dir{p}:
      1n <> p

def sp_po_rules(rs: List<&2, Po.Rule>) -> List<&2, List<&2, Nat>>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      sp_po_rule(r) <> sp_po_rules(rest)

# R6: a list of Nats, spelled, then rest
def sp_po_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

# R6: the request q as Rust writes it, then rest: the rules (one flat
# list), the path, the judge's class, whether it writes
def sp_po_req(q: FPo.Req, rest: String) -> String:
  match q:
    case FPo.Req{rs, at, c, w}:
      sp_po_ns(po_flat(sp_po_rules(rs)), sp_po_ns(at, Wr.put_nat(sp_po_code(c), Wr.put_bool(w, rest))))

# R6: a list of Nats fits the wire: its length and each item
def po_ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# R6: every number of a request fits the wire
def po_req_fits(q: FPo.Req) -> Bool:
  match q:
    case FPo.Req{rs, at, c, w}:
      Bool.and(po_ns_fit(po_flat(sp_po_rules(rs))), po_ns_fit(at))

# R6: an answer, spelled: 0 then the judge's class, or 1 then the place
def sp_po_wc(x: Po.Wc) -> String:
  match x:
    case Po.Judged{c}:
      Wr.put_nat(0n, Wr.put_nat(sp_po_code(c), ""))
    case Po.Own{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))

# R6: the model's answer to q, spelled
def sp_po_reply(q: FPo.Req) -> String:
  match q:
    case FPo.Req{rs, at, c, w}:
      sp_po_wc(Po.class(rs, at, c, w))

# Laws: reads and rule lists (R1, R2, R5)
# --------------------------------------

# LAW path_own_read (R1): a read keeps the judge's class, whatever the
# rules name
# EXCLUDES: a read of an own path refused (the agent can always read its
#   settings and its session record); a read's class changed
law path_own_read:
  for rs: List<&2, Po.Rule>
  for +at: List<&2, Nat>
  for c: Pp.Cls
  {Po.class(rs, at, c, False{}) == Po.Judged{c} : Po.Wc}

# LAW path_own_none (R2): with no own rule, a write keeps the judge's
# class
# EXCLUDES: a write refused with no rule; a protected or secret write
#   turned Own by its class alone
law path_own_none:
  for +at: List<&2, Nat>
  for c: Pp.Cls
  {Po.class(Nil{}, at, c, True{}) == Po.Judged{c} : Po.Wc}

# LAW path_own_one (R2, R5): the answer of one rule to a write is Own at
# place 0 or the judge's class
# EXCLUDES: the judge's class replaced (a write turned Protected or
#   Outside), a place counted from 1
law path_own_one:
  for r: Po.Rule
  for +at: List<&2, Nat>
  for +c: Pp.Cls
  {po_one(Po.class([r], at, c, True{}), c) == True{} : Bool}

# LAW path_own_concat (R2, R5): the answer of rules xs then ys to a write
# is the answer of xs when xs names it, else the answer of ys with its
# place moved past the rules of xs
# EXCLUDES: the last naming rule's place, a place within ys alone, a rule
#   of ys named over one of xs, a write one rule names that the others
#   let through, a rule skipped
law path_own_concat:
  for +xs: List<&2, Po.Rule>
  for +ys: List<&2, Po.Rule>
  for +at: List<&2, Nat>
  for +c: Pp.Cls
  {Po.class(List.append(&2, Po.Rule, xs, ys), at, c, True{}) == po_then(Po.class(xs, at, c, True{}), List.length(&2, Po.Rule, xs), Po.class(ys, at, c, True{})) : Po.Wc}

# Laws: what a rule names (R3, R4)
# --------------------------------

# LAW path_own_tree (R3): a write to a Tree rule's path or anything under
# it (k: the names below it, deepest first) is Own, whatever the judge's
# class
# EXCLUDES: only the path itself named, only its direct entries, a write
#   the judge classed secret, inside or outside let through
law path_own_tree:
  for +k: List<&2, Nat>
  for +p: List<&2, Nat>
  for c: Pp.Cls
  {Po.class([Po.Tree{p}], List.append(&2, Nat, k, p), c, True{}) == Po.Own{0n} : Po.Wc}

# LAW path_own_tree_only (R3): a write a Tree rule names is its path or
# under it
# EXCLUDES: a rule that names an ancestor of its path (refusing a write to
#   the workspace that holds a check file), a sibling, a path that merely
#   shares the last name
law path_own_tree_only:
  for +p: List<&2, Nat>
  for +at: List<&2, Nat>
  for c: Pp.Cls
  for own: {Po.class([Po.Tree{p}], at, c, True{}) == Po.Own{0n} : Po.Wc}
  exs k: List<&2, Nat>
  {at == List.append(&2, Nat, k, p) : List<&2, Nat>}

# LAW path_own_dir (R4): a write to a Dir rule's directory or to an entry
# n directly in it is Own, whatever the judge's class
# EXCLUDES: the directory's entries let through (settings.json, auth.json
#   written), the directory itself let through (the agent dir moved)
law path_own_dir:
  for +n: Nat
  for +p: List<&2, Nat>
  for +c: Pp.Cls
  {Po.class([Po.Dir{p}], p, c, True{}) == Po.Own{0n} : Po.Wc} & {Po.class([Po.Dir{p}], n <> p, c, True{}) == Po.Own{0n} : Po.Wc}

# LAW path_own_dir_only (R4): a write a Dir rule names is its directory or
# an entry directly in it
# EXCLUDES: a Dir rule read as a Tree (refusing a write deep under the
#   agent dir, as in a workspace kept there), an ancestor of the directory
#   named
law path_own_dir_only:
  for +p: List<&2, Nat>
  for +at: List<&2, Nat>
  for c: Pp.Cls
  for own: {Po.class([Po.Dir{p}], at, c, True{}) == Po.Own{0n} : Po.Wc}
  exs k: List<&2, Nat>
  {at == List.append(&2, Nat, k, p) : List<&2, Nat>} & {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool}

# LAW path_own_example (R1-R5): anchor: the agent dir /1/2 (a Dir rule,
# last), its sessions (3), sessions-archive (4) and agents (5) trees and a
# settings file /1/7/6 as Tree rules: its settings.json (8), a session
# file, an agent profile and the sessions dir itself are Own at their
# rule's place (the sessions tree before the agent dir); a file deeper
# under the agent dir, the home dir /1 and a workspace file /1/7/14 keep
# the judge's class; the settings file is Own though judged inside; a read
# of auth.json (13) stays secret
# EXCLUDES: the agent dir's rule naming everything under it, the home dir
#   refused, a read refused, places counted from the last rule
law path_own_example:
  {[Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [8n, 2n, 1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [9n, 10n, 3n, 2n, 1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [11n, 5n, 2n, 1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [3n, 2n, 1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [9n, 12n, 2n, 1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [1n], Pp.Protected{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [14n, 7n, 1n], Pp.Inside{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [6n, 7n, 1n], Pp.Inside{}, True{}), Po.class([Po.Tree{[3n, 2n, 1n]}, Po.Tree{[4n, 2n, 1n]}, Po.Tree{[5n, 2n, 1n]}, Po.Tree{[6n, 7n, 1n]}, Po.Dir{[2n, 1n]}], [13n, 2n, 1n], Pp.Secret{}, False{})] == [Po.Own{4n}, Po.Own{0n}, Po.Own{2n}, Po.Own{0n}, Po.Judged{Pp.Protected{}}, Po.Judged{Pp.Protected{}}, Po.Judged{Pp.Inside{}}, Po.Own{3n}, Po.Judged{Pp.Secret{}}] : List<&2, Po.Wc>}

# Laws: the entry (R6)
# --------------------

# LAW path_own_entry_answers (R6): the entry answers every request Rust
# writes, every number within the wire, with the model's answer, spelled
# EXCLUDES: a request misread (the path read as a rule, the class codes
#   renumbered, read and write swapped), a default, another reply spelling
law path_own_entry_answers:
  for +q: FPo.Req
  for fits: {po_req_fits(q) == True{} : Bool}
  {FPo.ffi(sp_po_req(q, "")) == sp_po_reply(q) : String}

# LAW path_own_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law path_own_entry_reads:
  for +q: FPo.Req
  for +rest: String
  for fits: {po_req_fits(q) == True{} : Bool}
  {FPo.get_req(sp_po_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FPo.Req>}

# LAW path_own_entry_exact (R6): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request: an unknown rule tag
#   (2 or more) or class code (4 or more), a name after the last end mark,
#   a number past the wire, input left over
law path_own_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FPo.ffi(s)) == False{} : Bool}
  exs q: FPo.Req
  {s == sp_po_req(q, "") : String} & {po_req_fits(q) == True{} : Bool}

# LAW path_own_entry_refuses (R6): every error the entry answers is
# exactly `E path_own: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law path_own_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FPo.ffi(s)) == True{} : Bool}
  {FPo.ffi(s) == Wr.err("path_own: malformed request") : String}

# LAW path_own_entry_example (R6): anchor: the wire strings Rust sends and
# the replies it reads: a write under a Tree rule is Own at place 0; the
# read of it keeps the class protected (2); a write two levels under a Dir
# rule keeps it; a rule tag 2, a class code 4, input left over and a name
# after the last end mark are refused
# EXCLUDES: another request or reply spelling
law path_own_entry_example:
  {[FPo.ffi("4,1,3,2,0,3,5,2,1,2,T"), FPo.ffi("4,1,3,2,0,3,5,2,1,2,F"), FPo.ffi("4,2,3,2,0,4,9,5,2,1,2,T"), FPo.ffi("4,3,3,2,0,3,5,2,1,2,T"), FPo.ffi("4,1,3,2,0,3,5,2,1,4,T"), FPo.ffi("4,1,3,2,0,3,5,2,1,2,TT"), FPo.ffi("2,1,3,0,0,T")] == ["1,0,", "0,2,", "0,2,", Wr.err("path_own: malformed request"), Wr.err("path_own: malformed request"), Wr.err("path_own: malformed request"), Wr.err("path_own: malformed request")] : List<&2, String>}
