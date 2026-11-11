# eukhe: the laws of area shell

import Base
import ../bend/ffi_shell.bend as FSh
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ../bend/wire_flat.bend as Fl
import ./base.bend as LawsBase

# ---- shell ----

# LAWS (G2, compiled core): the approval gate of a shell step runs as the
# compiled model (bend/ffi_shell.bend over bend/tools.bend part 4; Rust:
# crates/eukhe-bend/src/rules/shell.rs, called by crates/eukhe-shell/src/
# run.rs for each step and by the document tools' gate). The entry laws
# are open claims about FSh.ffi, stated with spec spellers built only from
# the wire primitives of bend/wire.bend and bend/wire_flat.bend (their
# round trips: laws/wire.bend); the decision laws (R3-R5) state what the
# model's decision is, by properties written from the requirement, never
# by a copy of the model.
#
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: a step's effects (`Tl.join` of its parts'
#     effects) and whether it runs unasked (`Tl.within`), whether effects
#     run unasked, and what an answer to a gated step does (`Tl.gate`).
# R2: every other input (an unknown tag, a part with no flag or a flag
#     past 1, a number past the wire, a short list, input left over)
#     answers exactly the error form "shell: malformed request".
# R3: a step's effects are, part by part in order, the secret effect (6)
#     when the part names a path that is or holds a secret, then the
#     part's own codes other than 6, in order (only a named secret path
#     gives 6).
# R4: effects run unasked exactly when each is an effect code (0 read, 1
#     write, 2 exec, 3 net, 4 outside, 5 protected, 6 secret: an auto set
#     may hold any of them) and is in the auto set.
# R5: the answer yes to a gated step lets it run (0); no stops the script
#     at it (1, its id).
# R6: the parts of a step travel as one flat list of Nats (bend/
#     wire_flat.bend): each inner list's items as 1 + item, then the end
#     mark 0; a flat list is read back exactly when it is such a spelling,
#     as the lists it spells.
# Every input is free: any auto set, any parts, any effects, any step id,
# any answer, any text.

# Spec spellers
# -------------

def spell_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

def spell_flag(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# a part as Rust writes it: its flag, then its own codes
def spell_part(p: Tl.Part) -> List<&2, Nat>:
  match p:
    case Tl.Part{o, s}:
      spell_flag(s) <> o

def spell_parts(ps: List<&2, Tl.Part>) -> List<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      spell_part(p) <> spell_parts(rest)

# the request q as Rust writes it, then rest
def spell_req(q: FSh.Req, rest: String) -> String:
  match q:
    case FSh.QStep{a, ps}:
      Wr.put_nat(0n, spell_ns(a, spell_ns(Fl.flat(spell_parts(ps)), rest)))
    case FSh.QAllows{a, es}:
      Wr.put_nat(1n, spell_ns(a, spell_ns(es, rest)))
    case FSh.QAnswer{i, y}:
      Wr.put_nat(2n, Wr.put_nat(i, Wr.put_bool(y, rest)))

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(q: FSh.Req) -> Bool:
  match q:
    case FSh.QStep{a, ps}:
      Bool.and(ns_fit(a), ns_fit(Fl.flat(spell_parts(ps))))
    case FSh.QAllows{a, es}:
      Bool.and(ns_fit(a), ns_fit(es))
    case FSh.QAnswer{i, y}:
      LawsBase.wire_fits(i)

# what an answer does: the step runs (0), or the script stops at it (1, id)
def spell_end(e: Tl.End) -> String:
  match e:
    case Tl.Finished{}:
      Wr.put_nat(0n, "")
    case Tl.Denied{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))

# the model's decision on q, spelled: a step's effects and whether it runs
# unasked; whether effects run unasked; what the user's answer y to the
# gated step i does
def spell_answer(q: FSh.Req) -> String:
  match q:
    case FSh.QStep{+a, ps}:
      +es = Tl.join(Tl.parts.effs(ps))
      spell_ns(es, Wr.put_bool(Tl.within(es, a), ""))
    case FSh.QAllows{+a, es}:
      Wr.put_bool(Tl.within(es, a), "")
    case FSh.QAnswer{i, y}:
      spell_end(Tl.Ran.end(Tl.gate(y, Tl.Step{i, Nil{}}, Tl.Ran{Nil{}, Tl.Finished{}})))

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "shell: malformed request"}}

# Laws: the entry (R1, R2, R5)
# ----------------------------

# LAW shell_ffi_answers: every request Rust writes (every number within the wire) gets the model's decision
# EXCLUDES: a request Rust writes refused or misread (the reader and the
#   speller disagree), a flat part list misread
law shell_ffi_answers:
  for +q: FSh.Req
  for fits: {req_fits(q) == True{} : Bool}
  {FSh.ffi(spell_req(q, "")) == spell_answer(q) : String}

# LAW shell_ffi_left_over: a request Rust writes followed by more input gets exactly the error form
# EXCLUDES: a second request or trailing bytes read past or ignored
law shell_ffi_left_over:
  for +q: FSh.Req
  for +more: String
  for fits: {req_fits(q) == True{} : Bool}
  for some: {String.is_empty(more) == False{} : Bool}
  {FSh.ffi(spell_req(q, more)) == malformed() : String}

# LAW shell_ffi_reads_only_requests (R2): every input the entry does not answer with an error is exactly one request Rust writes (spelled by spell_req from the wire primitives, nothing after it) whose every number fits the wire
# EXCLUDES: an answer for input that is no request: an unknown tag (3 or
#   more), a part with no flag or a flag past 1, a short list, a number
#   past the wire, a Bool that is no T or F, input left over
law shell_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSh.ffi(s)) == False{} : Bool}
  exs q: FSh.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW shell_ffi_refuses (R2): every error the entry answers is exactly the error form "shell: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law shell_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSh.ffi(s)) == True{} : Bool}
  {FSh.ffi(s) == malformed() : String}

# LAW shell_answer_ends (R5): the entry answers the user's yes to the gated step i (i within the wire) with 0 (the step runs), and a no with 1 then i (the script stops at step i)
# EXCLUDES: a yes that stops the script, a no that lets the step run, a
#   stop at another step than the one asked
law shell_answer_ends:
  for +i: Nat
  for fits: {LawsBase.wire_fits(i) == True{} : Bool}
  {FSh.ffi(spell_req(FSh.QAnswer{i, True{}}, "")) == Wr.put_nat(0n, "") : String} &
  {FSh.ffi(spell_req(FSh.QAnswer{i, False{}}, "")) == Wr.put_nat(1n, Wr.put_nat(i, "")) : String}

# LAW shell_ffi_example: anchor: the strings Rust sends: a step of a part {read, exec} and a part {read} that names a secret, under the auto set {write}; effects {read} under {read}; a denied and an approved answer to step 4; a part with flag 2 and an unknown tag are refused
# EXCLUDES: another spelling of a request or a reply
law shell_ffi_example:
  {FSh.ffi("0,1,1,7,1,1,3,0,2,1,0,") == "4,0,2,6,0,F" : String} &
  {FSh.ffi("1,1,0,1,0,") == "T" : String} &
  {FSh.ffi("2,4,F") == "1,4," : String} &
  {FSh.ffi("2,4,T") == "0," : String} &
  {FSh.ffi("0,0,2,3,0,") == malformed() : String} &
  {FSh.ffi("3,") == malformed() : String}

# Laws: a step's effects (R3)
# ---------------------------
# The effects the entry answers for a step of parts ps are
# Tl.join(Tl.parts.effs(ps)) (shell_ffi_answers). These five laws fix that
# list for every ps: the effects of parts in a row are each part's in turn;
# a part's are 6 first when it names a secret path, then its own codes'
# effects, which are code by code each code other than 6.

# LAW shell_effects_concat (R3): the effects of the parts ps then qs are the effects of ps, then those of qs
# EXCLUDES: a part's effects lost, reordered or duplicated across parts, a
#   deduplication across parts
law shell_effects_concat:
  for +ps: List<&2, Tl.Part>
  for +qs: List<&2, Tl.Part>
  {Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, ps, qs))) == List.append(&2, Nat, Tl.join(Tl.parts.effs(ps)), Tl.join(Tl.parts.effs(qs))) : List<&2, Nat>}

# LAW shell_effects_secret_first (R3): a part that names a secret path has the secret effect 6 first, then exactly the effects the same part has when it names none
# EXCLUDES: a named secret path without the secret effect, the secret
#   effect after the own codes, a named secret that changes the other codes
law shell_effects_secret_first:
  for +o: List<&2, Nat>
  {Tl.join(Tl.parts.effs([Tl.Part{o, True{}}])) == 6n <> Tl.join(Tl.parts.effs([Tl.Part{o, False{}}])) : List<&2, Nat>}

# LAW shell_effects_own_split (R3): a part (naming no secret path) whose own codes are xs then ys has the effects of a part with own codes xs, then those of a part with own codes ys
# EXCLUDES: own codes reordered, deduplicated or lost within a part
law shell_effects_own_split:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  {Tl.join(Tl.parts.effs([Tl.Part{List.append(&2, Nat, xs, ys), False{}}])) == List.append(&2, Nat, Tl.join(Tl.parts.effs([Tl.Part{xs, False{}}])), Tl.join(Tl.parts.effs([Tl.Part{ys, False{}}]))) : List<&2, Nat>}

# LAW shell_effects_own_code (R3): a part naming no secret path whose one own code c is not 6 has exactly the effect c
# EXCLUDES: an own code dropped, changed or doubled
law shell_effects_own_code:
  for +c: Nat
  for not6: {Nat.is_eq(c, 6n) == False{} : Bool}
  {Tl.join(Tl.parts.effs([Tl.Part{[c], False{}}])) == [c] : List<&2, Nat>}

# LAW shell_effects_own_six (R3): a part naming no secret path has no effect from an own code 6, nor from no own code
# EXCLUDES: the secret effect from a part's own codes (only a named secret
#   path gives it), an effect invented for a part with no codes
law shell_effects_own_six:
  {Tl.join(Tl.parts.effs([Tl.Part{[6n], False{}}])) == Nil{} : List<&2, Nat>} &
  {Tl.join(Tl.parts.effs([Tl.Part{Nil{}, False{}}])) == Nil{} : List<&2, Nat>}

# Laws: whether effects run unasked (R4)
# --------------------------------------
# The entry answers Tl.within(es, auto) (shell_ffi_answers). These laws
# fix it for every es and auto: no effect runs unasked; effects in a row
# run unasked when each part of the row does; one effect c runs unasked
# exactly when c is a code 0 to 6 and auto holds c somewhere.

# LAW shell_within_concat (R4): the effects es then fs run unasked exactly when es runs unasked and fs runs unasked
# EXCLUDES: one effect outside the auto set run unasked when others are
#   inside, only the first or last effect checked
law shell_within_concat:
  for +es: List<&2, Nat>
  for +fs: List<&2, Nat>
  for +auto: List<&2, Nat>
  {Tl.within(List.append(&2, Nat, es, fs), auto) == Bool.and(Tl.within(es, auto), Tl.within(fs, auto)) : Bool}

# LAW shell_within_none (R4): no effect runs unasked under every auto set
# EXCLUDES: a step with no effect asked
law shell_within_none:
  for auto: List<&2, Nat>
  {Tl.within(Nil{}, auto) == True{} : Bool}

# LAW shell_within_one_in (R4): an effect code c from 0 to 6 that the auto set holds (at any place: auto is pre, c, post) runs unasked
# EXCLUDES: an effect in the auto set asked, an auto set read only up to
#   its first or from its last item, a code 4 to 6 never granted
law shell_within_one_in:
  for +c: Nat
  for +pre: List<&2, Nat>
  for +post: List<&2, Nat>
  for code: {Nat.is_lt(c, 7n) == True{} : Bool}
  {Tl.within([c], List.append(&2, Nat, pre, c <> post)) == True{} : Bool}

# LAW shell_within_one_out (R4): an effect c that runs unasked is an effect code (below 7) that the auto set holds: auto is pre, c, post for some pre and post
# EXCLUDES: an effect outside the auto set run unasked, an unknown code (7
#   or more) run unasked though an auto set holds it
law shell_within_one_out:
  for +c: Nat
  for +auto: List<&2, Nat>
  for runs: {Tl.within([c], auto) == True{} : Bool}
  exs pre: List<&2, Nat>
  exs post: List<&2, Nat>
  {auto == List.append(&2, Nat, pre, c <> post) : List<&2, Nat>} & {Nat.is_lt(c, 7n) == True{} : Bool}

# Laws: the flat parts (R6)
# -------------------------

# LAW shell_flat_concat (R6): the flat list of lists xss then yss is the flat list of xss, then that of yss
# EXCLUDES: lists reordered, merged, or an end mark shared between two
#   lists
law shell_flat_concat:
  for +xss: List<&2, List<&2, Nat>>
  for +yss: List<&2, List<&2, Nat>>
  {Fl.flat(List.append(&2, List<&2, Nat>, xss, yss)) == List.append(&2, Nat, Fl.flat(xss), Fl.flat(yss)) : List<&2, Nat>}

# LAW shell_flat_one_items (R6): in the flat list of one list xs, the item at each place i of xs is there at the same place as 1 + item
# EXCLUDES: an item written without its offset, items reordered or shifted
law shell_flat_one_items:
  for +xs: List<&2, Nat>
  for +i: Nat
  for +x: Nat
  for at: {List.get(&2, Nat, xs, i) == Some{x} : Maybe<&2, Nat>}
  {List.get(&2, Nat, Fl.flat([xs]), i) == Some{1n+x} : Maybe<&2, Nat>}

# LAW shell_flat_one_end (R6): the flat list of one list xs is one longer than xs and ends with the end mark 0 (at the place length of xs)
# EXCLUDES: a lost end mark, an extra item, an end mark not last
law shell_flat_one_end:
  for +xs: List<&2, Nat>
  {List.length(&2, Nat, Fl.flat([xs])) == 1n+List.length(&2, Nat, xs) : Nat} &
  {List.get(&2, Nat, Fl.flat([xs]), List.length(&2, Nat, xs)) == Some{0n} : Maybe<&2, Nat>}

# LAW shell_flat_example (R6): anchor: the example of bend/wire_flat.bend's doc: [[4], [], [0, 7]] is [5, 0, 0, 1, 8, 0]
# EXCLUDES: another spelling of the flat parts
law shell_flat_example:
  {Fl.flat([[4n], Nil{}, [0n, 7n]]) == [5n, 0n, 0n, 1n, 8n, 0n] : List<&2, Nat>}

# LAW shell_unflat_reads (R6): the flat list reader reads every flat list back as the lists it spells
# EXCLUDES: a spelled list refused, misread, cut or merged with the next
law shell_unflat_reads:
  for +xss: List<&2, List<&2, Nat>>
  {Fl.unflat(Fl.flat(xss)) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}

# LAW shell_unflat_exact (R6): the flat list reader reads a list only when it is the flat spelling of what it reads
# EXCLUDES: items after the last end mark read as a list, a 0 item read as
#   an item, any list read as something it does not spell
law shell_unflat_exact:
  for +ns: List<&2, Nat>
  for +xss: List<&2, List<&2, Nat>>
  for h: {Fl.unflat(ns) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  {ns == Fl.flat(xss) : List<&2, Nat>}
