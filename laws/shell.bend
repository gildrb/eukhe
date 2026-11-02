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

# ---- shell: the decision and the flat parts, pinned to the requirement ----

# LAWS (G2, the decision): the decision the entry answers and the flat
# list its parts travel in, stated with spec functions written from the
# requirement (bend/tools.bend part 4, crates/eukhe-bend/WIRE.md), never
# the model's own, so R1's "the model's decision" is itself pinned.
#
# R3: a step's effects are, part by part in order, the secret effect (6)
#     when the part names a path that is or holds a secret, then the
#     part's own codes other than 6 (only a named secret path gives 6).
# R4: effects run unasked exactly when each is an effect code (0 read, 1
#     write, 2 exec, 3 net, 4 outside, 5 protected, 6 secret: an auto set
#     may hold any of them) and is in the auto set.
# R5: the answer yes to a gated step lets it run (0); no stops the script
#     at it (1, its id).
# R6: the parts of a step travel as one flat list of Nats: each inner
#     list's items as 1 + item, then the end mark 0; a flat list is read
#     back exactly when it is such a spelling, as the lists it spells.

# Spec functions
# --------------

# R6: the items of xs (each 1 + item), its end mark 0, then rest
def sh_flat_one(xs: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      0n <> rest
    case x <> t:
      {1n+x : Nat} <> sh_flat_one(t, rest)

# R6: every list of xss, in order, flat
def sh_flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> t:
      sh_flat_one(xs, sh_flat(t))

# R4: x is an item of xs
def sh_has(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), sh_has(rest, x))

# R4: c is an effect code (0 to 6)
def sh_code(c: Nat) -> Bool:
  Nat.is_lt(c, 7n)

# R4: every effect of es is an effect code in the auto set
def sh_within(es: List<&2, Nat>, +auto: List<&2, Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case +c <> rest:
      Bool.and(Bool.and(sh_code(c), sh_has(auto, c)), sh_within(rest, auto))

def sh_plain.keep(six: Bool, c: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match six:
    case True{}:
      r
    case False{}:
      c <> r

# R3: the codes of cs other than 6, then rest
def sh_plain(cs: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      rest
    case +c <> t:
      sh_plain.keep(Nat.is_eq(c, 6n), c, sh_plain(t, rest))

# R3: the secret effect when the part names a secret path, then rest
def sh_secret(s: Bool, rest: List<&2, Nat>) -> List<&2, Nat>:
  match s:
    case True{}:
      6n <> rest
    case False{}:
      rest

# R3: the effects of a step made of the parts ps
def sh_effs(ps: List<&2, Tl.Part>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case Tl.Part{o, s}:
          sh_secret(s, sh_plain(o, sh_effs(t)))

# R5: what the answer y to the gated step i does, spelled
def sh_end(i: Nat, y: Bool) -> String:
  match y:
    case True{}:
      Wr.put_nat(0n, "")
    case False{}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))

# the reply R3-R5 give a request
def sh_reply(q: FSh.Req) -> String:
  match q:
    case FSh.QStep{+a, ps}:
      +es = sh_effs(ps)
      spell_ns(es, Wr.put_bool(sh_within(es, a), ""))
    case FSh.QAllows{+a, es}:
      Wr.put_bool(sh_within(es, a), "")
    case FSh.QAnswer{i, y}:
      sh_end(i, y)

def sh_spec.end(whole: Bool, q: FSh.Req) -> String:
  match whole:
    case True{}:
      sh_reply(q)
    case False{}:
      malformed()

def sh_spec.run(r: Wr.Dec<FSh.Req>) -> String:
  match r:
    case Wr.Got{q, s}:
      sh_spec.end(Wr.end(s), q)
    case Wr.Bad{}:
      malformed()

# the reply R1-R6 give the input s: the reply to the request s is exactly
# (read by read_req, whose flat list reader Fl.unflat shell_unflat_reads
# and shell_unflat_exact pin to sh_flat), else the error form
def sh_spec(s: String) -> String:
  sh_spec.run(read_req(s))

# Laws
# ----

# LAW shell_flat_spelled: the flat list of a step's parts is the R6 spelling: each inner list's items as 1 + item, then 0
# EXCLUDES: an item written without its offset, a lost end mark, lists
#   reordered (spell_req would then spell what Rust does not write)
law shell_flat_spelled:
  for +xss: List<&2, List<&2, Nat>>
  {Fl.flat(xss) == sh_flat(xss) : List<&2, Nat>}

# LAW shell_unflat_reads: the flat list reader reads every R6 spelling back as the lists it spells
# EXCLUDES: a spelled list refused, misread, cut or merged with the next
law shell_unflat_reads:
  for +xss: List<&2, List<&2, Nat>>
  {Fl.unflat(sh_flat(xss)) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}

# LAW shell_unflat_exact: the flat list reader reads a list only when it is the R6 spelling of what it reads
# EXCLUDES: items after the last end mark read as a list, a 0 item read as
#   an item, any list read as something it does not spell
law shell_unflat_exact:
  for +ns: List<&2, Nat>
  for +xss: List<&2, List<&2, Nat>>
  for h: {Fl.unflat(ns) == Some{xss} : Maybe<&2, List<&2, List<&2, Nat>>>}
  {ns == sh_flat(xss) : List<&2, Nat>}

# LAW shell_effects_spec: a step's effects are, part by part, 6 when the part names a secret path, then its own codes other than 6
# EXCLUDES: a part's effect lost, reordered or duplicated; the secret
#   effect from a part's own codes or missing for a named secret path
law shell_effects_spec:
  for +ps: List<&2, Tl.Part>
  {Tl.join(Tl.parts.effs(ps)) == sh_effs(ps) : List<&2, Nat>}

# LAW shell_within_spec: effects run unasked exactly when each is an effect code (0 to 6) in the auto set
# EXCLUDES: one effect outside the auto set run unasked, an unknown code
#   run unasked, an effect in the auto set asked
law shell_within_spec:
  for +es: List<&2, Nat>
  for +auto: List<&2, Nat>
  {Tl.within(es, auto) == sh_within(es, auto) : Bool}

# LAW shell_ffi_spec: on every input the entry answers the reply R3-R6 give the request the input is exactly, and the error form on any other input
# EXCLUDES: a decision the model computes wrong (an effect lost or added,
#   a step run unasked outside the auto set, a denial that does not stop
#   at the step), a default for malformed input, input left over ignored
law shell_ffi_spec:
  for +s: String
  {FSh.ffi(s) == sh_spec(s) : String}
