# eukhe: the proof of LAW wfw_ffi_exact
#
# PROOF: the entry's decoder takes, stage by stage, the same branches on
# the same wire primitives as the spec's reader (wfx.tag .. wfx.left); its
# rows are read by the list reader, which wire_list_reads_items pins to
# the count and that many items, each read by the entry's row reader as
# the spec's row reader reads it (wfx.row, wfx.then, wfx.list). On a
# request with nothing after it the entry answers W.admit or W.effective,
# which the laws wf_admitted_never_respawns, wf_reuses_first_answer,
# wf_spawns_within_budget, wf_refused_when_spent and wf_limits_capped pin
# to the spec's answer (wfx.admit, wfx.reply), spelled as the spec spells
# it. The two error texts are the spec's.

import Base
import ../../bend/ffi_workflow.bend as FW
import ../../bend/wire.bend as Wr
import ../../bend/workflow.bend as W
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/workflow.bend as Workflow
import ../wire/wire_list_reads_items.bend as PWireListReadsItems
import ./wf_admitted_never_respawns.bend as PWfAdmittedNeverRespawns
import ./wf_reuses_first_answer.bend as PWfReusesFirstAnswer
import ./wf_spawns_within_budget.bend as PWfSpawnsWithinBudget
import ./wf_refused_when_spent.bend as PWfRefusedWhenSpent
import ./wf_limits_capped.bend as PWfLimitsCapped

# Rows
# ----

def wfx.row_sts(+k: Nat, d: Wr.Dec<Nat>) -> {FW.get_row.sts(k, FW.get_sts.go(d)) == Workflow.wfs_read_row.sts(k, Workflow.wfs_read_sts(d)) : Wr.Dec<W.Row>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n+p:
          {==}
    case Wr.Bad{}:
      {==}

def wfx.row_of(d: Wr.Dec<Nat>) -> {FW.get_row.go(d) == Workflow.wfs_read_row.of(d) : Wr.Dec<W.Row>}:
  match d:
    case Wr.Got{+k, +s}:
      wfx.row_sts(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry's row reader is the spec's
def wfx.row(+s: String) -> {FW.get_row(s) == Workflow.wfs_read_row(s) : Wr.Dec<W.Row>}:
  wfx.row_of(Wr.get_nat(s))

# m more rows after the row d answers, read by either row reader
def wfx.then(m: Nat, d: Wr.Dec<W.Row>) -> {LawsBase.wire_items.then(W.Row, d, x => LawsBase.wire_items(~W.Row, ~FW.get_row, m, x)) == LawsBase.wire_items.then(W.Row, d, x => LawsBase.wire_items(~W.Row, ~Workflow.wfs_read_row, m, x)) : Wr.Dec<List<&2, W.Row>>}:
  match m:
    case 0n:
      match d:
        case Wr.Got{x, r}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+j:
      match d:
        case Wr.Got{+x, +r}:
          +g = Workflow.wfs_read_row(r)
          %Equal.sym(Wr.Dec<W.Row>, FW.get_row(r), g, wfx.row(r)) : {LawsBase.wire_items.cons(W.Row, x, LawsBase.wire_items.then(W.Row, _, y => LawsBase.wire_items(~W.Row, ~FW.get_row, j, y))) == LawsBase.wire_items.cons(W.Row, x, LawsBase.wire_items.then(W.Row, g, y => LawsBase.wire_items(~W.Row, ~Workflow.wfs_read_row, j, y))) : Wr.Dec<List<&2, W.Row>>}
          %Equal.sym(Wr.Dec<List<&2, W.Row>>, LawsBase.wire_items.then(W.Row, g, y => LawsBase.wire_items(~W.Row, ~FW.get_row, j, y)), LawsBase.wire_items.then(W.Row, g, y => LawsBase.wire_items(~W.Row, ~Workflow.wfs_read_row, j, y)), wfx.then(j, g)) : {LawsBase.wire_items.cons(W.Row, x, _) == LawsBase.wire_items.cons(W.Row, x, LawsBase.wire_items.then(W.Row, g, y => LawsBase.wire_items(~W.Row, ~Workflow.wfs_read_row, j, y))) : Wr.Dec<List<&2, W.Row>>}
          {==}
        case Wr.Bad{}:
          {==}

# a list of rows read by either row reader
def wfx.list(d: Wr.Dec<Nat>) -> {LawsBase.wire_read_list.count(~W.Row, ~FW.get_row, d) == LawsBase.wire_read_list.count(~W.Row, ~Workflow.wfs_read_row, d) : Wr.Dec<List<&2, W.Row>>}:
  match d:
    case Wr.Got{n, +r}:
      match n:
        case 0n:
          {==}
        case 1n+j:
          +g = Workflow.wfs_read_row(r)
          %Equal.sym(Wr.Dec<W.Row>, FW.get_row(r), g, wfx.row(r)) : {LawsBase.wire_items.then(W.Row, _, y => LawsBase.wire_items(~W.Row, ~FW.get_row, j, y)) == LawsBase.wire_items.then(W.Row, g, y => LawsBase.wire_items(~W.Row, ~Workflow.wfs_read_row, j, y)) : Wr.Dec<List<&2, W.Row>>}
          wfx.then(j, g)
    case Wr.Bad{}:
      {==}

# The request
# -----------

def wfx.left(+prior: Maybe<&2, W.Sts>, +k: Nat, +rows: List<&2, W.Row>, +t: Nat, d: Wr.Dec<Nat>) -> {FW.get_req.pool(prior, k, rows, FW.get_pool.left(t, d)) == Workflow.wfs_read.left(prior, k, rows, t, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wfx.taken(+prior: Maybe<&2, W.Sts>, +k: Nat, +rows: List<&2, W.Row>, d: Wr.Dec<Nat>) -> {FW.get_req.pool(prior, k, rows, FW.get_pool.go(d)) == Workflow.wfs_read.taken(prior, k, rows, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{+t, +s}:
      wfx.left(prior, k, rows, t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wfx.rows(+prior: Maybe<&2, W.Sts>, +k: Nat, d: Wr.Dec<List<&2, W.Row>>) -> {FW.get_req.rows(prior, k, d) == Workflow.wfs_read.rows(prior, k, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{+rows, +s}:
      wfx.taken(prior, k, rows, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wfx.key(+prior: Maybe<&2, W.Sts>, d: Wr.Dec<Nat>) -> {FW.get_req.key(prior, d) == Workflow.wfs_read.key(prior, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{+k, +s}:
      +sp = LawsBase.wire_read_list(~W.Row, ~Workflow.wfs_read_row, s)
      %Equal.sym(Wr.Dec<List<&2, W.Row>>, Wr.get_list(~W.Row, ~FW.get_row, s), LawsBase.wire_read_list(~W.Row, ~FW.get_row, s), Wire.wire_list_reads_items(~W.Row, ~FW.get_row, s)) : {FW.get_req.rows(prior, k, _) == Workflow.wfs_read.rows(prior, k, sp) : Wr.Dec<FW.Req>}
      %Equal.sym(Wr.Dec<List<&2, W.Row>>, LawsBase.wire_read_list(~W.Row, ~FW.get_row, s), sp, wfx.list(Wr.get_nat(s))) : {FW.get_req.rows(prior, k, _) == Workflow.wfs_read.rows(prior, k, sp) : Wr.Dec<FW.Req>}
      wfx.rows(prior, k, sp)
    case Wr.Bad{}:
      {==}

def wfx.prior_some(d: Wr.Dec<Nat>) -> {FW.get_req.admit(FW.get_prior.some(FW.get_sts.go(d))) == Workflow.wfs_read.prior_some(Workflow.wfs_read_sts(d)) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          wfx.key(Some{W.Queued{}}, Wr.get_nat(s))
        case 1n:
          wfx.key(Some{W.Running{}}, Wr.get_nat(s))
        case 2n:
          wfx.key(Some{W.Finished{}}, Wr.get_nat(s))
        case 3n:
          wfx.key(Some{W.Erred{}}, Wr.get_nat(s))
        case 4n:
          wfx.key(Some{W.Cancelled{}}, Wr.get_nat(s))
        case 5n:
          wfx.key(Some{W.Cached{}}, Wr.get_nat(s))
        case 6n+p:
          {==}
    case Wr.Bad{}:
      {==}

def wfx.prior(d: Wr.Dec<Nat>) -> {FW.get_req.admit(FW.get_prior.go(d)) == Workflow.wfs_read.prior(d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          wfx.key(None{}, Wr.get_nat(s))
        case 1n:
          wfx.prior_some(Wr.get_nat(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def wfx.cap(+c: Nat, +m: Nat, d: Wr.Dec<Nat>) -> {FW.get_req.cap(c, m, d) == Workflow.wfs_read.cap(c, m, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{cap, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wfx.max(+c: Nat, d: Wr.Dec<Nat>) -> {FW.get_req.max(c, d) == Workflow.wfs_read.max(c, d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{+m, +s}:
      wfx.cap(c, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def wfx.conc(d: Wr.Dec<Nat>) -> {FW.get_req.limits(d) == Workflow.wfs_read.conc(d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{+c, +s}:
      wfx.max(c, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder reads as the spec's reader
def wfx.tag(d: Wr.Dec<Nat>) -> {FW.get_req.go(d) == Workflow.wfs_read.tag(d) : Wr.Dec<FW.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          wfx.prior(Wr.get_nat(s))
        case 1n:
          wfx.conc(Wr.get_nat(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

# The answer
# ----------

# a new call: the model's admission is the spec's, for every first answer
def wfx.fresh(hit: Maybe<&2, Nat>, +k: Nat, +rows: List<&2, W.Row>, p: W.Pool, eh: {Workflow.wf_first(rows, k) == hit : Maybe<&2, Nat>}) -> {W.admit(None{}, k, rows, p) == Workflow.wfs_fresh(hit, p) : W.Admit & W.Pool}:
  match hit:
    case Some{i}:
      Workflow.wf_reuses_first_answer(k, rows, p, i, eh)
    case None{}:
      match p:
        case W.Pool{t, l}:
          match l:
            case 0n:
              Workflow.wf_refused_when_spent(k, rows, t, eh)
            case 1n+m:
              Workflow.wf_spawns_within_budget(k, rows, t, m, eh)

# the model's admission is the spec's
def wfx.admit(prior: Maybe<&2, W.Sts>, +k: Nat, +rows: List<&2, W.Row>, p: W.Pool) -> {W.admit(prior, k, rows, p) == Workflow.wfs_admit(prior, k, rows, p) : W.Admit & W.Pool}:
  match prior:
    case Some{s}:
      Workflow.wf_admitted_never_respawns(s, k, rows, p)
    case None{}:
      wfx.fresh(Workflow.wf_first(rows, k), k, rows, p, {==})

def wfx.decision.at(a: W.Admit, t: Nat, l: Nat) -> {FW.put_decision((a, W.Pool{t, l}), "") == Workflow.wfs_spell_decision((a, W.Pool{t, l})) : String}:
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

def wfx.decision(d: W.Admit & W.Pool) -> {FW.put_decision(d, "") == Workflow.wfs_spell_decision(d) : String}:
  match d:
    case (a, p):
      match p:
        case W.Pool{t, l}:
          wfx.decision.at(a, t, l)

# the entry's reply to a whole request is the spec's
def wfx.reply(q: FW.Req) -> {FW.answer(q) == Workflow.wfs_reply(q) : String}:
  match q:
    case FW.AdmitReq{+prior, +k, +rows, +p}:
      %Equal.sym(W.Admit & W.Pool, W.admit(prior, k, rows, p), Workflow.wfs_admit(prior, k, rows, p), wfx.admit(prior, k, rows, p)) : {FW.put_decision(_, "") == Workflow.wfs_spell_decision(Workflow.wfs_admit(prior, k, rows, p)) : String}
      wfx.decision(Workflow.wfs_admit(prior, k, rows, p))
    case FW.LimitsReq{+c, +m, cap}:
      match cap:
        case 0n:
          {==}
        case 1n+x:
          %Equal.sym(W.Limits, W.effective(W.Limits{c, m}, 1n+x), W.Limits{Workflow.wf_min(c, 1n+x), m}, Workflow.wf_limits_capped(c, m, x)) : {FW.put_limits(_, "") == Wr.put_nat(Workflow.wf_min(c, 1n+x), Wr.put_nat(m, "")) : String}
          {==}

def wfx.end(q: FW.Req, r: String) -> {FW.ffi.end(Wr.end(r), q) == Workflow.wfs_entry.of(Wr.Got{q, r}) : String}:
  match r:
    case SNil{}:
      wfx.reply(q)
    case SCon{c, t}:
      {==}

def wfx.go(d: Wr.Dec<FW.Req>) -> {FW.ffi.go(d) == Workflow.wfs_entry.of(d) : String}:
  match d:
    case Wr.Got{q, r}:
      wfx.end(q, r)
    case Wr.Bad{}:
      {==}

def Workflow.wfw_ffi_exact(s):
  %wfx.tag(Wr.get_nat(s)) : {FW.ffi(s) == Workflow.wfs_entry.of(_) : String}
  wfx.go(FW.get_req(s))
