# eukhe: the laws of area refine_plan: a proposal's apply and a result's
# rollback (bend/refine_plan.bend; requirements R4 and R5 in ./model.bend)

import Base
import ../../bend/refine_plan.bend as Rp
import ./model.bend as RefinePlan

# Spec helpers
# ------------
# They read through the code only for an edit's id (Rp.ids, pinned by the
# R2 laws) and its validation (Rp.check, pinned by refine_plan_check_rules).

# a plan's rows
def rs_rows(p: Rp.Plan) -> List<&2, Rp.Row>:
  match p:
    case Rp.Plan{rows, changes}:
      rows

# a plan's change lines
def rs_changes(p: Rp.Plan) -> List<&2, String>:
  match p:
    case Rp.Plan{rows, changes}:
      changes

# a rollback's edits
def rs_picks(b: Rp.Back) -> List<&2, Rp.Pick>:
  match b:
    case Rp.Back{summary, rationale, outcome, reason, picks}:
      picks

# Plan (R4)
# ---------

def rs_tag(c: Rp.Comp) -> Nat:
  match c:
    case Rp.KPrompt{}:
      0n
    case Rp.KMemory{}:
      1n
    case Rp.KSkill{}:
      2n
    case Rp.KSubagent{}:
      3n
    case Rp.KFactory{}:
      4n

# the same kind
def rs_same(a: Rp.Comp, b: Rp.Comp) -> Bool:
  Nat.is_eq(rs_tag(a), rs_tag(b))

def rs_left.at(hit: Bool, p: Bool, acc: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      acc

def rs_left.out(x: Rp.Out, hit: Bool, acc: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match x:
    case Rp.OInvalid{m}:
      acc
    case Rp.ORefused{m}:
      acc
    case Rp.ORemoved{}:
      rs_left.at(hit, False{}, acc)
    case Rp.OWritten{}:
      rs_left.at(hit, True{}, acc)

# the presence a row leaves for the entry of kind c and id: removed
# (absent) or written (present) by it, else as it was
def rs_left.row(r: Rp.Row, +c: Rp.Comp, +id: String, acc: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match r:
    case Rp.Row{rv, rc, rid, x}:
      rs_left.out(x, Bool.and(rs_same(rc, c), String.eq(rid, id)), acc)

def rs_left.go(rows: List<&2, Rp.Row>, +c: Rp.Comp, +id: String, acc: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match rows:
    case Nil{}:
      acc
    case r <> t:
      rs_left.go(t, c, id, rs_left.row(r, c, id, acc))

# R4: whether the earlier rows (first first) left the entry of kind c and
# id present: the last of them that removed or wrote it; none: no earlier
# row did
def rs_left(rows: List<&2, Rp.Row>, +c: Rp.Comp, +id: String) -> Maybe<&2, Bool>:
  rs_left.go(rows, c, id, None{})

def rs_head(xs: List<&2, Maybe<&2, String>>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      x

# R4: an edit's id, the one the ids question (R2) answers for it
def rs_cid(+e: Rp.Ed) -> Maybe<&2, String>:
  rs_head(Rp.ids([e]))

# R4: an invalid edit's action: create without a kind, else its action
# (none: create)
def rs_bad_verb(e: Rp.Ed) -> Rp.Verb:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      match verb:
        case None{}:
          Rp.ACreate{}
        case Some{v}:
          match comp:
            case None{}:
              Rp.ACreate{}
            case Some{c}:
              v

# R4: an edit's kind (none: memory)
def rs_kind(e: Rp.Ed) -> Rp.Comp:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      match comp:
        case None{}:
          Rp.KMemory{}
        case Some{c}:
          c

# R4: what an action does to an entry present or not
def rs_final(v: Rp.Verb, p: Bool) -> Rp.Out:
  match v:
    case Rp.ACreate{}:
      match p:
        case True{}:
          Rp.ORefused{"entry already exists"}
        case False{}:
          Rp.OWritten{}
    case Rp.AUpdate{}:
      match p:
        case True{}:
          Rp.OWritten{}
        case False{}:
          Rp.ORefused{"entry not found"}
    case Rp.ADelete{}:
      match p:
        case True{}:
          Rp.ORemoved{}
        case False{}:
          Rp.ORefused{"entry not found"}

def rs_decide.at(m: Maybe<&2, String>, f: Rp.Out) -> Rp.Out:
  match m:
    case None{}:
      f
    case Some{x}:
      Rp.ORefused{x}

# R4: a valid edit of action v and kind c, its entry's presence as the
# earlier rows left it (look): R4's refusals in order, else the action on
# the entry (present as left, else as stored)
def rs_decide(o: Rp.Opts, e: Rp.Ed, +v: Rp.Verb, +c: Rp.Comp, +look: Maybe<&2, Bool>) -> Rp.Out:
  match o:
    case Rp.Opts{factory, baseline}:
      match e:
        case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
          rs_decide.at(RefinePlan.rs_first([RefinePlan.RsRule{Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning"}, RefinePlan.RsRule{Bool.and(RefinePlan.rs_is_factory(c), Bool.and(Bool.not(RefinePlan.rs_is_delete(v)), Bool.not(factory))), "the factory is disabled; run /factory on to enable it"}, RefinePlan.RsRule{Bool.not(held), "eukhe's memory is the chat: say it in your reply"}]), rs_final(v, Maybe.default(&2, Bool, look, exists)))

def rs_row.at(+o: Rp.Opts, +prev: List<&2, Rp.Row>, +e: Rp.Ed, +id: String, k: Rp.Check) -> Rp.Row:
  match k:
    case Rp.CBad{msg}:
      Rp.Row{rs_bad_verb(e), rs_kind(e), id, Rp.OInvalid{msg}}
    case Rp.COk{+v, +c}:
      Rp.Row{v, c, id, rs_decide(o, e, v, c, rs_left(prev, c, id))}

# R4: the row of an edit after the rows prev of the edits before it: its
# validation (R3) with its id (R2; none: empty), then, when valid, R4's
# decision on the entry as prev left it
def rs_row(+o: Rp.Opts, +prev: List<&2, Rp.Row>, +e: Rp.Ed) -> Rp.Row:
  +cid = rs_cid(e)
  rs_row.at(o, prev, e, Maybe.default(&2, String, cid, ""), Rp.check(e, cid))

# a row that removed or wrote its entry
def rs_applied(r: Rp.Row) -> Bool:
  match r:
    case Rp.Row{v, c, id, x}:
      match x:
        case Rp.OInvalid{m}:
          False{}
        case Rp.ORefused{m}:
          False{}
        case Rp.ORemoved{}:
          True{}
        case Rp.OWritten{}:
          True{}

# R4: a row's change line: `<action> <kind>:<id>`
def rs_line(r: Rp.Row) -> String:
  match r:
    case Rp.Row{v, c, id, x}:
      String.concat([RefinePlan.rp_verb_name(v), " ", RefinePlan.rp_comp_name(c), ":", id])

def rs_lines.each(rows: List<&2, Rp.Row>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case r <> t:
      rs_line(r) <> rs_lines.each(t)

# R4: the change lines of the rows that removed or wrote their entry, in
# order
def rs_lines(rows: List<&2, Rp.Row>) -> List<&2, String>:
  rs_lines.each(List.filter(~Rp.Row, ~rs_applied, rows))

def rs_plan.go(eds: List<&2, Rp.Ed>, +o: Rp.Opts, +prev: List<&2, Rp.Row>) -> List<&2, Rp.Row>:
  match eds:
    case Nil{}:
      prev
    case e <> t:
      rs_plan.go(t, o, List.append(&2, Rp.Row, prev, [rs_row(o, prev, e)]))

# R4: a proposal's rows: each edit's row (rs_row) decided after the rows of
# the edits before it, in order
def rs_plan_rows(+o: Rp.Opts, eds: List<&2, Rp.Ed>) -> List<&2, Rp.Row>:
  rs_plan.go(eds, o, [])

# Rollback (R5)
# -------------

# R5: the rollback edit of the row at index i: an applied row with a
# before is restored, by an update when it has an after, else by a create;
# an applied row with an after and no before is deleted; others: none
def rs_pick(w: Rp.Was, i: Nat) -> List<&2, Rp.Pick>:
  match w:
    case Rp.Was{applied, before, after}:
      match applied:
        case False{}:
          []
        case True{}:
          match before:
            case True{}:
              match after:
                case True{}:
                  [Rp.Pick{i, Rp.AUpdate{}}]
                case False{}:
                  [Rp.Pick{i, Rp.ACreate{}}]
            case False{}:
              match after:
                case True{}:
                  [Rp.Pick{i, Rp.ADelete{}}]
                case False{}:
                  []

def rs_back.go(was: List<&2, Rp.Was>, +i: Nat, acc: List<&2, Rp.Pick>) -> List<&2, Rp.Pick>:
  match was:
    case Nil{}:
      acc
    case w <> t:
      rs_back.go(t, 1n+i, List.append(&2, Rp.Pick, rs_pick(w, i), acc))

# R5: a result's rollback edits: each row's (rs_pick, its index i) put
# before those of the rows before it, so the last row's come first
def rs_back_picks(was: List<&2, Rp.Was>) -> List<&2, Rp.Pick>:
  rs_back.go(was, 0n, [])

# Laws
# ----

# LAW refine_plan_plan_rows (R4): every proposal's rows are, edit by edit
# in order, the row of the edit after the rows of the edits before it: an
# invalid edit (Rp.check with the edit's Rp.ids id) a row with R4's
# action and kind and the message; a valid one refused by the first of
# R4's refusals that applies (a baseline change of an entry no earlier
# row wrote or removed, the factory opt-in, a kind the memory does not
# hold), else the action on the entry as the last earlier row that wrote
# or removed it left it (none: as stored)
# EXCLUDES: an earlier edit's write or removal ignored, a refused or
#   invalid row read as a write, a baseline change checked for an entry the
#   proposal already touched, the refusals in another order, a delete of a
#   factory refused while the opt-in is off, a row lost, added or moved
law refine_plan_plan_rows:
  for +o: Rp.Opts
  for +eds: List<&2, Rp.Ed>
  {rs_rows(Rp.plan(o, eds)) == rs_plan_rows(o, eds) : List<&2, Rp.Row>}

# LAW refine_plan_plan_lines (R4): every proposal's change lines are
# `<a> <kind>:<id>` of its rows that removed or wrote their entry, in order
# EXCLUDES: a refused or invalid row counted as a change, a change line in
#   another shape or order
law refine_plan_plan_lines:
  for +o: Rp.Opts
  for +eds: List<&2, Rp.Ed>
  {rs_changes(Rp.plan(o, eds)) == rs_lines(rs_rows(Rp.plan(o, eds))) : List<&2, String>}

# LAW refine_plan_back_whole (R5): every result's rollback has R5's texts
# with the result's id, and its edits are each applied row's restore (an
# update with an after, else a create, for a row with a before; a delete
# for a row with an after and no before; nothing else), last row first
# EXCLUDES: rows rolled back first first, an unapplied row reverted, a
#   restore by the wrong action, a created entry left, another row index,
#   another text
law refine_plan_back_whole:
  for +id: String
  for was: List<&2, Rp.Was>
  {Rp.back(id, was) == Rp.Back{String.append("Rollback refinement ", id), String.append("Restores continual harness state snapshots from refinement ", String.append(id, ".")), "Faulty refinement edits are reverted.", String.append("Rollback ", id), rs_back_picks(was)} : Rp.Back}
