# eukhe: lemmas of the workflow entry proofs: the spelling
#
# The laws' spelling of a request is the entry's encoding (sp.req), and
# the laws' spelled reply is the entry's answer (sp.answer). A spelled
# request that fits reads whole (sp.ffi): the entry answers its end check.

import Base
import ../../../bend/ffi_workflow.bend as FW
import ../../../bend/wire.bend as Wr
import ../../../bend/workflow.bend as W
import ../../../laws/workflow/model.bend as Workflow
import ../base.bend as LA

def sp.sts(s: W.Sts, -rest: String) -> {Workflow.wfw_spell_sts(s, rest) == FW.put_sts(s, rest) : String}:
  match s:
    case W.Queued{}:
      {==}
    case W.Running{}:
      {==}
    case W.Finished{}:
      {==}
    case W.Erred{}:
      {==}
    case W.Cancelled{}:
      {==}
    case W.Cached{}:
      {==}

def sp.prior(m: Maybe<&2, W.Sts>, +rest: String) -> {Workflow.wfw_spell_prior(m, rest) == FW.put_prior(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %sp.sts(s, rest) : {Workflow.wfw_spell_prior(Some{s}, rest) == Wr.put_nat(1n, _) : String}
      {==}

def sp.row(r: W.Row, +rest: String) -> {Workflow.wfw_spell_row(r, rest) == FW.put_row(r, rest) : String}:
  match r:
    case W.Row{+k, +s}:
      %sp.sts(s, rest) : {Workflow.wfw_spell_row(W.Row{k, s}, rest) == Wr.put_nat(k, _) : String}
      {==}

def sp.items(xs: List<&2, W.Row>, +rest: String) -> {Workflow.wfw_spell_rows.items(xs, rest) == LA.pww.row_items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %sp.row(x, LA.pww.row_items(t, rest)) : {Workflow.wfw_spell_rows.items(x <> t, rest) == _ : String}
      %sp.items(t, rest) : {Workflow.wfw_spell_row(x, Workflow.wfw_spell_rows.items(t, rest)) == Workflow.wfw_spell_row(x, _) : String}
      {==}

def sp.rows(+xs: List<&2, W.Row>, +rest: String) -> {Workflow.wfw_spell_rows(xs, rest) == Wr.put_list(~W.Row, ~FW.put_row, xs, rest) : String}:
  %Equal.sym(String, Wr.put_list(~W.Row, ~FW.put_row, xs, rest), Wr.put_nat(List.length(&2, W.Row, xs), LA.pww.row_items(xs, rest)), LA.pww.row_put(xs, rest)) : {Workflow.wfw_spell_rows(xs, rest) == _ : String}
  %sp.items(xs, rest) : {Workflow.wfw_spell_rows(xs, rest) == Wr.put_nat(List.length(&2, W.Row, xs), _) : String}
  {==}

def sp.pool(p: W.Pool, -rest: String) -> {Workflow.wfw_spell_pool(p, rest) == FW.put_pool(p, rest) : String}:
  match p:
    case W.Pool{t, l}:
      {==}

# the laws' spelling of a request is the entry's encoding
def sp.req(q: FW.Req, +rest: String) -> {Workflow.wfw_spell_req(q, rest) == FW.put_req(q, rest) : String}:
  match q:
    case FW.AdmitReq{+prior, +k, +rows, +p}:
      +l = Workflow.wfw_spell_req(FW.AdmitReq{prior, k, rows, p}, rest)
      %sp.pool(p, rest) : {l == Wr.put_nat(0n, FW.put_prior(prior, Wr.put_nat(k, Wr.put_list(~W.Row, ~FW.put_row, rows, _)))) : String}
      %sp.rows(rows, Workflow.wfw_spell_pool(p, rest)) : {l == Wr.put_nat(0n, FW.put_prior(prior, Wr.put_nat(k, _))) : String}
      %sp.prior(prior, Wr.put_nat(k, Workflow.wfw_spell_rows(rows, Workflow.wfw_spell_pool(p, rest)))) : {l == Wr.put_nat(0n, _) : String}
      {==}
    case FW.LimitsReq{c, m, cap}:
      {==}

def sp.admit(a: W.Admit, -rest: String) -> {Workflow.wfw_spell_admit(a, rest) == FW.put_admit(a, rest) : String}:
  match a:
    case W.Ended{}:
      {==}
    case W.Reattach{}:
      {==}
    case W.Reuse{i}:
      {==}
    case W.Spawn{}:
      {==}
    case W.Refused{}:
      {==}

def sp.decision(d: W.Admit & W.Pool) -> {Workflow.wfw_spell_decision(d) == FW.put_decision(d, "") : String}:
  match d:
    case (+a, +p):
      %sp.pool(p, "") : {Workflow.wfw_spell_decision((a, p)) == FW.put_admit(a, _) : String}
      sp.admit(a, Workflow.wfw_spell_pool(p, ""))

def sp.limits(l: W.Limits) -> {Workflow.wfw_spell_limits(l) == FW.put_limits(l, "") : String}:
  match l:
    case W.Limits{c, m}:
      {==}

# the laws' spelled reply is the entry's answer, turned around
def sp.answer(q: FW.Req) -> {FW.answer(q) == Workflow.wfw_spell_answer(q) : String}:
  match q:
    case FW.AdmitReq{prior, k, rows, p}:
      Equal.sym(String, Workflow.wfw_spell_decision(W.admit(prior, k, rows, p)), FW.put_decision(W.admit(prior, k, rows, p), ""), sp.decision(W.admit(prior, k, rows, p)))
    case FW.LimitsReq{c, m, cap}:
      Equal.sym(String, Workflow.wfw_spell_limits(W.effective(W.Limits{c, m}, cap)), FW.put_limits(W.effective(W.Limits{c, m}, cap), ""), sp.limits(W.effective(W.Limits{c, m}, cap)))

# a spelled request that fits reads whole: the entry answers its end check
# on what is left
def sp.ffi(+q: FW.Req, +rest: String, fits: {Workflow.wfw_req_fits(q) == True{} : Bool}) -> {FW.ffi(Workflow.wfw_spell_req(q, rest)) == FW.ffi.end(Wr.end(rest), q) : String}:
  %Equal.sym(String, Workflow.wfw_spell_req(q, rest), FW.put_req(q, rest), sp.req(q, rest)) : {FW.ffi(_) == FW.ffi.end(Wr.end(rest), q) : String}
  %LA.pww.req(q, rest, fits) : {FW.ffi.go(_) == FW.ffi.end(Wr.end(rest), q) : String}
  {==}
