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
# run.rs for each step and by the document tools' gate). Each law is an
# open claim about FSh.ffi, the function the core runs, stated with spec
# spellers built only from the wire primitives of bend/wire.bend and
# bend/wire_flat.bend (their round trips: laws/wire.bend).
#
# R1: a request Rust writes reads back whole and the entry answers it with
#     the model's decision: a step's effects (`Tl.join` of its parts'
#     effects) and whether it runs unasked (`Tl.within`), whether effects
#     run unasked, and what an answer to a gated step does (`Tl.gate`).
# R2: every other input (an unknown tag, a part with no flag or a flag
#     past 1, a number past the wire, a short list, input left over)
#     answers exactly the error form "shell: malformed request".
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

# Reader: the requests, read with the wire primitives
# ---------------------------------------------------

def read_ns(s: String) -> Wr.Dec<List<&2, Nat>>:
  Wr.get_list(~Nat, ~Wr.get_nat, s)

# the part an inner list spells: flag 0 or 1, then its own codes
def read_part(xs: List<&2, Nat>) -> Maybe<&2, Tl.Part>:
  match xs:
    case Nil{}:
      None{}
    case f <> o:
      match f:
        case 0n:
          Some{Tl.Part{o, False{}}}
        case 1n:
          Some{Tl.Part{o, True{}}}
        case 2n+g:
          None{}

def read_parts.cons(m: Maybe<&2, Tl.Part>, ms: Maybe<&2, List<&2, Tl.Part>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match ms:
        case None{}:
          None{}
        case Some{ps}:
          Some{p <> ps}

def read_parts(xss: List<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match xss:
    case Nil{}:
      Some{Nil{}}
    case xs <> rest:
      read_parts.cons(read_part(xs), read_parts(rest))

def read_parts.flat(m: Maybe<&2, List<&2, List<&2, Nat>>>) -> Maybe<&2, List<&2, Tl.Part>>:
  match m:
    case None{}:
      None{}
    case Some{xss}:
      read_parts(xss)

def read_step.parts(a: List<&2, Nat>, m: Maybe<&2, List<&2, Tl.Part>>, s: String) -> Wr.Dec<FSh.Req>:
  match m:
    case None{}:
      Wr.Bad{}
    case Some{ps}:
      Wr.Got{FSh.QStep{a, ps}, s}

def read_step.flat(a: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{ns, s}:
      read_step.parts(a, read_parts.flat(Fl.unflat(ns)), s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_step(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{a, s}:
      read_step.flat(a, read_ns(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_allows.effs(a: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{FSh.QAllows{a, es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_allows(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{a, s}:
      read_allows.effs(a, read_ns(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_answer.yes(i: Nat, r: Wr.Dec<Bool>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{y, s}:
      Wr.Got{FSh.QAnswer{i, y}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_answer(r: Wr.Dec<Nat>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{i, s}:
      read_answer.yes(i, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_req.tag(t: Nat, s: String) -> Wr.Dec<FSh.Req>:
  match t:
    case 0n:
      read_step(read_ns(s))
    case 1n:
      read_allows(read_ns(s))
    case 2n:
      read_answer(Wr.get_nat(s))
    case 3n+u:
      Wr.Bad{}

def read_req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FSh.Req>:
  match r:
    case Wr.Got{t, s}:
      read_req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# the request s starts with, and what follows it
def read_req(s: String) -> Wr.Dec<FSh.Req>:
  read_req.go(Wr.get_nat(s))

def spec.end(whole: Bool, q: FSh.Req) -> String:
  match whole:
    case True{}:
      spell_answer(q)
    case False{}:
      malformed()

def spec.run(r: Wr.Dec<FSh.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply to s: the model's decision on the request s is exactly, else
# the error form
def spec(s: String) -> String:
  spec.run(read_req(s))

# Laws
# ----

# LAW shell_ffi_exact: on every input the entry answers the model's decision on the request the input is exactly (a step's effects and whether it runs unasked; whether effects run unasked; what an answer does), and exactly the error form "shell: malformed request" on any other input
# EXCLUDES: a decision other than the model's, a default for malformed
#   input, a request misread (a field dropped, swapped, a flag past 1 read
#   as a flag, a number past the wire read), input left over ignored,
#   another error text
law shell_ffi_exact:
  for +s: String
  {FSh.ffi(s) == spec(s) : String}

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

# LAW shell_ffi_example: anchor: the strings Rust sends: a step of a part {read, exec} and a part {read} that names a secret, under the auto set {write}; effects {read} under {read}; a denied and an approved answer to step 4; a part with flag 2 and an unknown tag are refused
# EXCLUDES: another spelling of a request or a reply
law shell_ffi_example:
  {FSh.ffi("0,1,1,7,1,1,3,0,2,1,0,") == "4,0,2,6,0,F" : String} &
  {FSh.ffi("1,1,0,1,0,") == "T" : String} &
  {FSh.ffi("2,4,F") == "1,4," : String} &
  {FSh.ffi("2,4,T") == "0," : String} &
  {FSh.ffi("0,0,2,3,0,") == malformed() : String} &
  {FSh.ffi("3,") == malformed() : String}
