# eukhe: the laws of area shell

import Base
import ../bend/ffi_shell.bend as FSh
import ../bend/tools.bend as Tl
import ../bend/wire.bend as Wr
import ../bend/wire_flat.bend as Fl
import ./base.bend as LawsBase

# ---- shell ----

# LAWS (G2, compiled core): the verdict of a shell step runs as the
# compiled model (bend/ffi_shell.bend over bend/tools.bend part 4; Rust:
# crates/eukhe-bend/src/rules/shell.rs, called by crates/eukhe-shell/src/
# run.rs for each step). The entry laws are open claims about FSh.ffi,
# stated with spec spellers built only from the wire primitives of
# bend/wire.bend and bend/wire_flat.bend (their round trips:
# laws/wire.bend); the decision laws (R3, R7, R8) state what the model's
# decision is, by properties written from the requirement, never by a
# copy of the model.
#
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: a step's effects (`Tl.pieces.effs`) and
#     whether it runs (`Tl.verdict`).
# R2: every other input (an unknown tag, tags 0 to 2 included, a part
#     with no flag or a flag past 1, a number past the wire, a short list,
#     input left over) answers exactly the error form "shell: malformed
#     request".
# R3: a step's effects are, part by part in order, the secret effect (6)
#     when the part names a path that is or holds a secret, then the
#     part's own codes other than 6, in order (only a named secret path
#     gives 6).
# R6: the parts of a step travel as one flat list of Nats (bend/
#     wire_flat.bend): each inner list's items as 1 + item, then the end
#     mark 0; a flat list is read back exactly when it is such a spelling,
#     as the lists it spells.
# R7 (spec/README.md I2, I3): a step (tag 3, `verdict`) runs exactly when
#     no part of it writes an own path (eukhe's own config and
#     credentials, the session record, a protected file of a check); no
#     setting enters the verdict; its effects are those of R3.
# R8 (spec/README.md I3): a script runs its steps in order up to the first
#     step that writes an own path; that step and every later one do not
#     run, and the script ends stopped at that step's id; a script with no
#     such step runs every step. A step here is a pipeline (a lone command
#     is a pipeline of one stage): its stages start together, so a
#     pipeline with a stage that writes an own path runs none of its
#     stages, and the script ends stopped at that stage's id. A step
#     planned from its parts carries the parts' effects (R3) and writes an
#     own path exactly when its verdict (R7) refuses it. Tl.script is the
#     model: no entry runs it. Rust runs the script (crates/eukhe-shell/
#     src/run.rs `Shell::run`, `pipeline`), asking the entry's verdict (R7)
#     for each stage. Rust tests gate it: eukhe_shell::run::tests::
#     every_step_runs_unasked_and_an_own_write_stops_the_script (the steps
#     before the refused one run, it and the later ones do not, the end
#     names its id; a pipeline with no own write runs every stage) and
#     an_own_write_in_a_pipeline_runs_none_of_its_stages.
# Every input is free: any parts, any effects, any step id, any text.

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

# a part as the verdict question spells it: its secret flag, its own-write
# flag, then its own codes
def spell_piece(p: Tl.Piece) -> List<&2, Nat>:
  match p:
    case Tl.Piece{o, s, m}:
      spell_flag(s) <> spell_flag(m) <> o

def spell_pieces(ps: List<&2, Tl.Piece>) -> List<&2, List<&2, Nat>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      spell_piece(p) <> spell_pieces(rest)

# the request q as Rust writes it, then rest
def spell_req(q: FSh.Req, rest: String) -> String:
  match q:
    case FSh.QVerdict{ps}:
      Wr.put_nat(3n, spell_ns(Fl.flat(spell_pieces(ps)), rest))

# a list of Nats fits the wire: its length and each item
def ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# every number of a request fits the wire
def req_fits(q: FSh.Req) -> Bool:
  match q:
    case FSh.QVerdict{ps}:
      ns_fit(Fl.flat(spell_pieces(ps)))

# R7: a verdict as Rust reads it: 0 runs, 1 refused
def spell_verdict(v: Tl.Verdict) -> Nat:
  match v:
    case Tl.Runs{}:
      0n
    case Tl.Refused{}:
      1n

# R7: the verdict is a refusal
def refused(v: Tl.Verdict) -> Bool:
  match v:
    case Tl.Runs{}:
      False{}
    case Tl.Refused{}:
      True{}

# R7: a part without its own-write fact
def piece_part(p: Tl.Piece) -> Tl.Part:
  match p:
    case Tl.Piece{o, s, m}:
      Tl.Part{o, s}

def pieces_parts(ps: List<&2, Tl.Piece>) -> List<&2, Tl.Part>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      piece_part(p) <> pieces_parts(rest)

# the model's decision on q, spelled: a step's effects and whether it runs
def spell_answer(q: FSh.Req) -> String:
  match q:
    case FSh.QVerdict{+ps}:
      spell_ns(Tl.pieces.effs(ps), Wr.put_nat(spell_verdict(Tl.verdict(ps)), ""))

# the error form of every input that is not exactly one request
def malformed() -> String:
  SCon{'E', SCon{' ', "shell: malformed request"}}

# Laws: the entry (R1, R2)
# ------------------------

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
# EXCLUDES: an answer for input that is no request: an unknown tag (0 to
#   2, 4 or more), a part with no flag or a flag past 1, a short list, a
#   number past the wire, input left over
law shell_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSh.ffi(s)) == False{} : Bool}
  exs q: FSh.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW shell_ffi_req_exact (R2): the entry's decoder reads a request only from a spelled one: whatever it decodes is a request whose every number fits the wire (spell_req), then the input after it
# EXCLUDES: a decoder that invents a request (a default request for an
#   unknown tag, tags 0 to 2 included, empty or short input), reads a
#   number with a leading zero or past the wire
law shell_ffi_req_exact:
  for +s: String
  for +q: FSh.Req
  for +rest: String
  for +h: {FSh.get_req(s) == Wr.Got{q, rest} : Wr.Dec<FSh.Req>}
  {s == spell_req(q, rest) : String} & {req_fits(q) == True{} : Bool}

# LAW shell_ffi_req_example (R2): anchor: an old tag (0), an unknown tag
# (4), a tag with a leading zero and empty input are no request
# EXCLUDES: a default request for an unknown tag or empty input
law shell_ffi_req_example:
  {[FSh.get_req("0,"), FSh.get_req("4,"), FSh.get_req("03,"), FSh.get_req("")] == [Wr.Bad{}, Wr.Bad{}, Wr.Bad{}, Wr.Bad{}] : List<&2, Wr.Dec<FSh.Req>>}

# LAW shell_ffi_refuses (R2): every error the entry answers is exactly the error form "shell: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law shell_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSh.ffi(s)) == True{} : Bool}
  {FSh.ffi(s) == malformed() : String}

# LAW shell_ffi_example: anchor: the strings Rust sends: a part {read} runs; a part {write, protected} that writes an own path is refused; the tags 0 to 2 (the approval gate's) and 4, and a part with own-write flag 2, are refused
# EXCLUDES: another spelling of a request or a reply, an approval gate
#   question answered
law shell_ffi_example:
  {FSh.ffi("0,1,1,7,1,1,3,0,2,1,0,") == malformed() : String} &
  {FSh.ffi("1,1,0,1,0,") == malformed() : String} &
  {FSh.ffi("2,4,T") == malformed() : String} &
  {FSh.ffi("4,") == malformed() : String} &
  {FSh.ffi("3,4,1,1,1,0,") == "1,0,0," : String} &
  {FSh.ffi("3,5,1,2,2,6,0,") == "2,1,5,1," : String} &
  {FSh.ffi("3,3,1,3,0,") == malformed() : String}

# Laws: whether a step runs (R7)
# ------------------------------
# The entry answers Tl.verdict(ps) for a step of parts ps
# (shell_ffi_answers). These laws fix it for every ps: a step with no
# part runs; one part is refused exactly when it writes an own path;
# parts in a row are refused exactly when one of them is. No setting
# enters it: every other step runs unasked (I2), a step that writes an
# own path is refused (I3).

# LAW shell_verdict_none (R7): a step with no part runs
# EXCLUDES: an empty step refused
law shell_verdict_none:
  {Tl.verdict(Nil{}) == Tl.Runs{} : Tl.Verdict}

# LAW shell_verdict_one (R7): a step of one part is refused exactly when
# the part writes an own path, whatever its effects and secret flag
# EXCLUDES: a refusal of a write outside the workspace, a net or secret
#   access or any irreversible effect; an own write that runs; a verdict
#   read from the secret flag
law shell_verdict_one:
  for +o: List<&2, Nat>
  for +s: Bool
  for +m: Bool
  {refused(Tl.verdict([Tl.Piece{o, s, m}])) == m : Bool}

# LAW shell_verdict_concat (R7): the parts ps then qs are refused exactly
# when ps is or qs is
# EXCLUDES: only the first or last part read, an own write hidden by the
#   parts beside it
law shell_verdict_concat:
  for +ps: List<&2, Tl.Piece>
  for +qs: List<&2, Tl.Piece>
  {refused(Tl.verdict(List.append(&2, Tl.Piece, ps, qs))) == Bool.or(refused(Tl.verdict(ps)), refused(Tl.verdict(qs))) : Bool}

# LAW shell_verdict_effects (R3, R7): the effects of a step answered with
# its verdict are those of the same parts without the own-write fact (R3
# fixes them)
# EXCLUDES: an own write that adds, drops or reorders an effect
law shell_verdict_effects:
  for +ps: List<&2, Tl.Piece>
  {Tl.pieces.effs(ps) == Tl.join(Tl.parts.effs(pieces_parts(ps))) : List<&2, Nat>}

# Laws: a script (R8)
# -------------------

# R8: the steps of a planned script as they run: each step's id and
# effects
def sh_steps(ss: List<&2, Tl.Planned>) -> List<&2, Tl.Step>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Tl.Planned{i, e, m}:
          Tl.Step{i, e} <> sh_steps(rest)

# R8: no step of ss writes an own path
def sh_none_own(ss: List<&2, Tl.Planned>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Tl.Planned{i, e, m}:
          Bool.and(Bool.not(m), sh_none_own(rest))

# LAW shell_plan (R3, R7, R8): the step planned with id i from parts ps
# has id i, the parts' effects, and writes an own path exactly when its
# verdict refuses it
# EXCLUDES: a planned step that runs although its verdict refuses it, one
#   stopped though it runs, its effects or id lost
law shell_plan:
  for +i: Nat
  for +ps: List<&2, Tl.Piece>
  {Tl.plan(i, ps) == Tl.Planned{i, Tl.pieces.effs(ps), refused(Tl.verdict(ps))} : Tl.Planned}

# LAW shell_script_runs_all (R8): a script none of whose steps writes an
# own path runs every step, in order, and ends with every step run (of
# the model Tl.script; Rust's loop mirrors it, gated by its tests, R8)
# EXCLUDES: a step dropped, repeated or reordered; a script stopped early
#   (a net, secret or outside step taken as a stop)
law shell_script_runs_all:
  for +ss: List<&2, Tl.Planned>
  for free: {sh_none_own(ss) == True{} : Bool}
  {Tl.script(ss) == Tl.Did{sh_steps(ss), Tl.AllRan{}} : Tl.Did}

# LAW shell_script_stops (R8): steps that write no own path, then step i
# that writes one: the steps before it run, in order; it and every later
# step do not, and the script ends stopped at i (of the model Tl.script;
# Rust's loop mirrors it, gated by its tests, R8)
# EXCLUDES: the refused step run, a later step run, the steps before it
#   dropped, a stop named by another id
law shell_script_stops:
  for +pre: List<&2, Tl.Planned>
  for +i: Nat
  for +e: List<&2, Nat>
  for +post: List<&2, Tl.Planned>
  for free: {sh_none_own(pre) == True{} : Bool}
  {Tl.script(List.append(&2, Tl.Planned, pre, Tl.Planned{i, e, True{}} <> post)) == Tl.Did{sh_steps(pre), Tl.StoppedAt{i}} : Tl.Did}

# Laws: a step's effects (R3)
# ---------------------------
# The effects the entry answers for a step of parts ps are
# Tl.join(Tl.parts.effs(ps)) of the parts without their own-write fact
# (shell_ffi_answers, shell_verdict_effects). These five laws fix that
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
