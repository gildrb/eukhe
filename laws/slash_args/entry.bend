# eukhe: the laws of area slash_args: the entry (bend/ffi_slash_args.bend)

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as SlashArgs

# (D2) The entry
# --------------
# R10: the entry answers each request Rust writes (a tag: 0 goal, 1
#      autonomous, 2 words, 3 objective; then the text, its length within
#      the wire) with the spec's answer of R1-R9 spelled as below, reads
#      exactly the request and nothing after it, and answers any other
#      input (an unknown tag, a short text, input left over) with the exact
#      error form `E slash_args: malformed request`.
# R11: the answers: a goal is its tag (0 status, 1 clear, 2 pause, 3
#      resume, 4 start, 5 error) then for start the objective and the
#      budget (0 none | 1 then its digits), for an error its text. An
#      autonomous answer is its tag (0 status, 1 on, 2 off, 3 error) then
#      for on the options (four limits, each 0 none | 1 then 0 unlimited |
#      1 its digits; the gates 0 none | 1 then the commands (0 none | 1 then
#      the list), the retries and the timeout (each 0 none | 1 its
#      digits); the keep-alive (0 none | 1 its digits)), for an error its
#      text. Words are the list of words. An objective is answered as a
#      goal: start without a budget, or the error.

# Spec spellers
# -------------

def sae_text(k: Nat, a: String, rest: String) -> String:
  Wr.put_nat(k, Wr.put_str(a, rest))

# a request, then rest
def sae_req(q: FSa.Req, rest: String) -> String:
  match q:
    case FSa.QGoal{a}:
      sae_text(0n, a, rest)
    case FSa.QAuto{a}:
      sae_text(1n, a, rest)
    case FSa.QWords{a}:
      sae_text(2n, a, rest)
    case FSa.QObjective{a}:
      sae_text(3n, a, rest)

def sae_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def sae_goal(g: Sa.Goal) -> String:
  match g:
    case Sa.GStatus{}:
      Wr.put_nat(0n, "")
    case Sa.GClear{}:
      Wr.put_nat(1n, "")
    case Sa.GPause{}:
      Wr.put_nat(2n, "")
    case Sa.GResume{}:
      Wr.put_nat(3n, "")
    case Sa.GStart{o, b}:
      Wr.put_nat(4n, Wr.put_str(o, sae_mstr(b, "")))
    case Sa.GErr{e}:
      Wr.put_nat(5n, Wr.put_str(e, ""))

def sae_lim(m: Maybe<&2, Sa.Lim>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{l}:
      match l:
        case Sa.LUnl{}:
          Wr.put_nat(1n, Wr.put_nat(0n, rest))
        case Sa.LNum{d}:
          Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_str(d, rest)))

def sae_cmds(m: Maybe<&2, List<&2, String>>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{cs}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(cs, rest))

def sae_gates(m: Maybe<&2, Sa.Gates>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{g}:
      match g:
        case Sa.Gates{cs, r, t}:
          Wr.put_nat(1n, sae_cmds(cs, sae_mstr(r, sae_mstr(t, rest))))

def sae_conf(c: Sa.Conf) -> String:
  match c:
    case Sa.Conf{a, b, k, m, g, p}:
      sae_lim(a, sae_lim(b, sae_lim(k, sae_lim(m, sae_gates(g, sae_mstr(p, ""))))))

def sae_auto(a: Sa.Auto) -> String:
  match a:
    case Sa.AStatus{}:
      Wr.put_nat(0n, "")
    case Sa.AOn{c}:
      Wr.put_nat(1n, sae_conf(c))
    case Sa.AOff{}:
      Wr.put_nat(2n, "")
    case Sa.AErr{e}:
      Wr.put_nat(3n, Wr.put_str(e, ""))

# the spelled answer of the spec to a request
def sae_reply(q: FSa.Req) -> String:
  match q:
    case FSa.QGoal{a}:
      sae_goal(SlashArgs.sa_goal(a))
    case FSa.QAuto{a}:
      sae_auto(SlashArgs.sa_auto(a))
    case FSa.QWords{a}:
      LawsBase.wire_spell_strs(SlashArgs.sa_words(a), "")
    case FSa.QObjective{a}:
      sae_goal(SlashArgs.sa_goal.objective(a, None{}))

# the request's text fits the wire
def sae_fits(q: FSa.Req) -> Bool:
  match q:
    case FSa.QGoal{a}:
      LawsBase.wire_fits(String.length(a))
    case FSa.QAuto{a}:
      LawsBase.wire_fits(String.length(a))
    case FSa.QWords{a}:
      LawsBase.wire_fits(String.length(a))
    case FSa.QObjective{a}:
      LawsBase.wire_fits(String.length(a))

# Laws
# ----

# LAW slash_args_entry_answers (R10, R11): the entry answers every request
# Rust spells, its text within the wire, with the spec's answer spelled
# EXCLUDES: questions swapped, a field misread, an answer of another tag
#   or field order, the budget's or a limit's digits dropped, words
#   spelled without their count, a default
law slash_args_entry_answers:
  for +q: FSa.Req
  for fit: {sae_fits(q) == True{} : Bool}
  {FSa.ffi(sae_req(q, "")) == sae_reply(q) : String}

# LAW slash_args_entry_left_over (R10): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into the text
law slash_args_entry_left_over:
  for +q: FSa.Req
  for +c: Char
  for +t: String
  for fit: {sae_fits(q) == True{} : Bool}
  {FSa.ffi(sae_req(q, SCon{c, t})) == Wr.err("slash_args: malformed request") : String}

# LAW slash_args_entry_exact (R10): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, a
#   short text, input left over)
law slash_args_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSa.ffi(s)) == False{} : Bool}
  exs q: FSa.Req
  {s == sae_req(q, "") : String} & {sae_fits(q) == True{} : Bool}

# LAW slash_args_entry_refuses (R10): every error the entry answers is
# exactly `E slash_args: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law slash_args_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSa.ffi(s)) == True{} : Bool}
  {FSa.ffi(s) == Wr.err("slash_args: malformed request") : String}

# LAW slash_args_entry_unknown_tag (R10): a request tag past 3 answers the
# error form, whatever follows
# EXCLUDES: an unknown tag read as a known question
law slash_args_entry_unknown_tag:
  for +n: Nat
  for +rest: String
  {FSa.ffi(Wr.put_nat(4n+n, rest)) == Wr.err("slash_args: malformed request") : String}

# LAW slash_args_entry_example (R10, R11): anchor: the wire strings Rust
# sends and the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law slash_args_entry_example:
  {[FSa.ffi("0,0,"), FSa.ffi("0,9,--budget="), FSa.ffi("0,4,a bc"), FSa.ffi("1,2,on"), FSa.ffi("1,11,on --gate=x"), FSa.ffi("2,7,a 'b c'"), FSa.ffi("3,3, a "), FSa.ffi("4,0,"), FSa.ffi("0,0,x")] == ["0,", "5,45,Goal token budget must be a positive integer.", "4,4,a bc0,", "1,0,0,0,0,0,0,", "1,0,0,0,0,1,1,1,1,x0,0,0,", "2,1,a3,b c", "4,1,a0,", Wr.err("slash_args: malformed request"), Wr.err("slash_args: malformed request")] : List<&2, String>}
