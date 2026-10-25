# eukhe: the laws of area refine_plan: the model (bend/refine_plan.bend)

import Base
import ../../bend/refine_plan.bend as Rp

# (D1) The /refine planner's decisions
# ------------------------------------
# bend/refine_plan.bend, run as the compiled core by
# bend/ffi_refine_plan.bend (eukhe-bend rules/refine_plan.rs; asked by
# eukhe-core refinement/planner.rs when a /refine proposal is parsed,
# applied or rolled back and when its request is fitted to the model).
# Every input is free: any edit, entry facts, options, rows, text and
# numbers. Rust reads the JSON with serde and gives the facts: an edit's
# action, kind, id and title (absent: none), whether it has content, the
# string fields of its reference (a field absent or not a JSON string:
# none), each of its arguments' `dag` and `machine` keys as missing, null,
# an object or another value, whether its entry is stored (the state the
# proposal starts from), whether that stored entry differs from the
# planning baseline's (both serialized to JSON values, absent equals
# absent; false without a baseline), and whether the session's memory
# holds its kind (Rust `HarnessMemory::holds`; no kind: held).
#
# R1: the slug of a text with a fallback (Rust `slug`): the text trimmed
#     of whitespace and lowercased (Rust `str::to_lowercase`), then each
#     char that is an ASCII lowercase letter or digit kept and every other
#     char a `_` unless the slug so far ends with `_`; then the `_`s at
#     both ends trimmed, the first 80 chars kept; empty: the fallback.
#     (Lowercasing reaches an ASCII letter or digit from outside ASCII only
#     for U+0130, which lowercases to `i` and U+0307, and U+212A, which
#     lowercases to `k`; the trim changes nothing: whitespace turns to `_`
#     and is trimmed.)
# R2: an edit's computed id (Rust `apply_refinement_proposal`): its id;
#     else for a create the slug of its title (none: its kind's name) with
#     its kind's name the fallback (no kind: `memory`); else none. The ids
#     question answers the computed id of every edit, in order.
# R3: an edit's validation (Rust `validate_edit`, the TS messages; the
#     first that applies; <a> is the action's name `create`, `update` or
#     `delete`): no action `unsupported action`; no kind `unsupported
#     kind`; a prompt whose id or computed id is `base_system_prompt`
#     `base system prompt is not editable`; an update or delete without an
#     id `<a> requires id`; a create or update without a title or without
#     content `<a> requires title and content`; a skill create or update:
#     without arguments `<a> skill requires arguments`, without a
#     reference `<a> skill requires python reference`, a reference whose
#     type is not the string `python` `<a> skill reference.type must be
#     python`, without a non-empty import or python_import string `<a>
#     skill requires python import`, without a non-empty callable or
#     call_pattern string `<a> skill requires callable or call_pattern`;
#     a factory create, or a factory update with arguments, with both a
#     `dag` and a `machine` that are neither missing nor null `pass either
#     dag or machine form, not both`, else when the `machine` (neither
#     missing nor null; else the `dag`) is not an object `factory entry
#     requires a dag or machine object in arguments`; else valid.
# R4: a proposal's apply (Rust `apply_refinement_proposal`), each edit in
#     order, its id the computed id (none: empty): an invalid edit is a row
#     with its action (none: create), its kind (none: memory), the id and
#     the validation message, not applied, no before. A valid edit's entry
#     is the one of its kind and id as the earlier edits of the proposal
#     left it (an earlier written or removed entry: the last such edit's
#     result; else the stored entry): with a baseline given, an entry no
#     earlier edit wrote or removed that differs from the baseline's
#     refuses `entry changed during refinement planning`; else a factory
#     create or update while the factory opt-in is off refuses `the
#     factory is disabled; run /factory on to enable it`; else a kind the
#     session's memory does not hold refuses `eukhe's memory is the chat:
#     say it in your reply`; else a delete of no entry refuses `entry not
#     found` and of an entry removes it; a create of an entry refuses
#     `entry already exists` and of no entry writes it; an update of no
#     entry refuses `entry not found` and of an entry writes it. A refusal
#     after validation shows the entry before it (none when there is no
#     entry). The change lines: for each removed or written row, `<a>
#     <kind>:<id>`, in order.
# R5: a result's rollback (Rust `rollback_proposal`): its rows last first,
#     applied ones only: a row with a before is restored by an update
#     when the row has an after, else by a create; a row without a before
#     but with an after is deleted; others are skipped. Its summary
#     `Rollback refinement <id>`, rationale `Restores continual harness
#     state snapshots from refinement <id>.`, expected outcome `Faulty
#     refinement edits are reverted.`, each edit's reason `Rollback <id>`
#     (<id> the result's id).
# R6: a proposal's texts (Rust `normalize_refinement_proposal`): the
#     summary, rationale and expected outcome given as JSON strings, else
#     `Refined continual harness state`, the empty text, the empty text.
# R7: a JSON candidate is cut off (Rust `is_incomplete_json`): scanning
#     its chars, outside a string a `"` opens one, `{` or `[` opens a
#     bracket and `}` or `]` closes one (the count may go below zero);
#     inside a string a `\` escapes the next char and an unescaped `"`
#     closes it; cut off when the scan ends inside a string or with more
#     brackets opened than closed.
# R8: a refinement request's fit (Rust `refinement_request`; lengths in
#     UTF-8 bytes, one token each): the reserve is the system prompt's
#     length plus 1024, the budget the context window less (floored at 0)
#     the least of the max tokens, the output reserve and half the window
#     (rounded down). When the reserve plus the full prompt's length is
#     over the budget and the conversation is not empty, a binary search
#     over the conversation tail's length: low 0, high the conversation's
#     length; while low < high the middle (low + high + 1) / 2 (rounded
#     down) is measured: a prompt within the budget sets low to it, else
#     high to it less one; then the prompt of low is the final one. The
#     max tokens: the least of the max tokens and the window less (floored
#     at 0) the reserve plus the final prompt's length; 0 refuses
#     `Refinement prompt leaves no room for output in the model's context
#     window; retry with a smaller request.` The core answers one step of
#     this walk at a time: given where the walk is and the length of the
#     prompt Rust built and measured, the next length to build (and where
#     the walk then is), the max tokens, or the refusal. Rust saturates
#     every number at 99,999,999,999,999.

# Spec helpers
# ------------

# Names
# -----

def rp_verb_name(v: Rp.Verb) -> String:
  match v:
    case Rp.ACreate{}:
      "create"
    case Rp.AUpdate{}:
      "update"
    case Rp.ADelete{}:
      "delete"

def rp_comp_name(c: Rp.Comp) -> String:
  match c:
    case Rp.KPrompt{}:
      "prompt"
    case Rp.KMemory{}:
      "memory"
    case Rp.KSkill{}:
      "skill"
    case Rp.KSubagent{}:
      "subagent"
    case Rp.KFactory{}:
      "factory"

def rp_comp_eq(a: Rp.Comp, b: Rp.Comp) -> Bool:
  String.eq(rp_comp_name(a), rp_comp_name(b))

# Slug
# ----

def rp_slug.put.at(alnum: Bool, upper: Bool, dotted: Bool, kelvin: Bool, +c: Char, +r: String) -> String:
  match alnum:
    case True{}:
      SCon{c, r}
    case False{}:
      match upper:
        case True{}:
          SCon{Char.to_lower(c), r}
        case False{}:
          match dotted:
            case True{}:
              SCon{'i', SCon{'_', r}}
            case False{}:
              match kelvin:
                case True{}:
                  SCon{'k', r}
                case False{}:
                  SCon{'_', r}

# each char lowercased, then every char not an ASCII lowercase letter or
# digit a `_` (U+0130 lowercases to `i` and U+0307, U+212A to `k`)
def rp_slug.marks(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      rp_slug.put.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, rp_slug.marks(t))

def rp_slug.squeeze.at(dup: Bool, c: Char, r: String) -> String:
  match dup:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# every run of `_` one `_`
def rp_slug.squeeze(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      rp_slug.squeeze.at(Bool.and(Char.is_eq(c, '_'), String.starts_with(t, "_")), c, rp_slug.squeeze(t))

def rp_slug.lead.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `_`s
def rp_slug.lead(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      rp_slug.lead.at(Char.is_eq(c, '_'), c, t, rp_slug.lead(t))

def rp_slug.pick(e: Bool, s: String, fb: String) -> String:
  match e:
    case True{}:
      fb
    case False{}:
      s

# the slug of a title: marked, squeezed, `_` trimmed at both ends, its
# first 80 chars; the fallback when empty
def rp_slug(raw: String, fb: String) -> String:
  +t = String.take(String.reverse(rp_slug.lead(String.reverse(rp_slug.lead(rp_slug.squeeze(rp_slug.marks(raw)))))), 80n)
  rp_slug.pick(String.is_empty(t), t, fb)

# Ids
# ---

def rp_is_create(m: Maybe<&2, Rp.Verb>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case Rp.ACreate{}:
          True{}
        case Rp.AUpdate{}:
          False{}
        case Rp.ADelete{}:
          False{}

def rp_comp_or_memory(m: Maybe<&2, Rp.Comp>) -> Rp.Comp:
  match m:
    case None{}:
      Rp.KMemory{}
    case Some{c}:
      c

def rp_computed.at(create: Bool, title: Maybe<&2, String>, +name: String) -> Maybe<&2, String>:
  match create:
    case True{}:
      Some{rp_slug(Maybe.default(&2, String, title, name), name)}
    case False{}:
      None{}

# the id an edit names: its id, else a create's slug of its title (none:
# its kind's name), the kind's name the fallback (no kind: memory)
def rp_computed(e: Rp.Ed) -> Maybe<&2, String>:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      Maybe.or(&2, String, id, rp_computed.at(rp_is_create(verb), title, rp_comp_name(rp_comp_or_memory(comp))))

# the id of every edit
def rp_ids(eds: List<&2, Rp.Ed>) -> List<&2, Maybe<&2, String>>:
  match eds:
    case Nil{}:
      Nil{}
    case e <> t:
      rp_computed(e) <> rp_ids(t)

# Validation
# ----------

def rp_first(b: Bool, msg: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{msg}
    case False{}:
      r

def rp_is_text(m: Maybe<&2, String>, x: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      String.eq(y, x)

def rp_filled(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      Bool.not(String.is_empty(y))

def rp_is_comp(c: Rp.Comp, d: Rp.Comp) -> Bool:
  rp_comp_eq(c, d)

def rp_is_verb(v: Rp.Verb, w: Rp.Verb) -> Bool:
  String.eq(rp_verb_name(v), rp_verb_name(w))

def rp_skill.fields(+vn: String, r: Rp.Pyref) -> Maybe<&2, String>:
  match r:
    case Rp.Pyref{ty, imp, pyimp, call, pat}:
      rp_first(Bool.not(rp_is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), rp_first(Bool.not(Bool.or(rp_filled(imp), rp_filled(pyimp))), String.concat([vn, " skill requires python import"]), rp_first(Bool.not(Bool.or(rp_filled(call), rp_filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})))

def rp_skill.ref(+vn: String, m: Maybe<&2, Rp.Pyref>) -> Maybe<&2, String>:
  match m:
    case None{}:
      Some{String.concat([vn, " skill requires python reference"])}
    case Some{r}:
      rp_skill.fields(vn, r)

# a skill create or update: arguments, a python reference with an import
# and a callable
def rp_skill(+vn: String, args: Maybe<&2, Rp.Args>, m: Maybe<&2, Rp.Pyref>) -> Maybe<&2, String>:
  rp_first(Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"]), rp_skill.ref(vn, m))

def rp_present(v: Rp.Val) -> Bool:
  match v:
    case Rp.VMissing{}:
      False{}
    case Rp.VNull{}:
      False{}
    case Rp.VObject{}:
      True{}
    case Rp.VOther{}:
      True{}

def rp_is_object(v: Rp.Val) -> Bool:
  match v:
    case Rp.VMissing{}:
      False{}
    case Rp.VNull{}:
      False{}
    case Rp.VObject{}:
      True{}
    case Rp.VOther{}:
      False{}

def rp_spec_object(m: Bool, dag: Rp.Val, machine: Rp.Val) -> Bool:
  match m:
    case True{}:
      rp_is_object(machine)
    case False{}:
      rp_is_object(dag)

def rp_factory.keys(+dag: Rp.Val, +machine: Rp.Val) -> Maybe<&2, String>:
  rp_first(Bool.and(rp_present(dag), rp_present(machine)), "pass either dag or machine form, not both", rp_first(Bool.not(rp_spec_object(rp_present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{}))

# a factory create, or an update with arguments: one spec form, an object
def rp_factory(args: Maybe<&2, Rp.Args>) -> Maybe<&2, String>:
  match args:
    case None{}:
      rp_factory.keys(Rp.VMissing{}, Rp.VMissing{})
    case Some{a}:
      match a:
        case Rp.Args{dag, machine}:
          rp_factory.keys(dag, machine)

def rp_when(b: Bool, m: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      m
    case False{}:
      r

# the first rule an action and kind break, in Rust's order
def rp_rules(+v: Rp.Verb, +c: Rp.Comp, +id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, m: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> Maybe<&2, String>:
  +vn = rp_verb_name(v)
  +edit = Bool.not(rp_is_verb(v, Rp.ADelete{}))
  rp_first(Bool.and(rp_is_comp(c, Rp.KPrompt{}), Bool.or(rp_is_text(id, "base_system_prompt"), rp_is_text(cid, "base_system_prompt"))), "base system prompt is not editable", rp_first(Bool.and(Bool.not(rp_is_verb(v, Rp.ACreate{})), Maybe.is_none(&2, String, id)), String.concat([vn, " requires id"]), rp_first(Bool.and(edit, Bool.not(Bool.and(titled, content))), String.concat([vn, " requires title and content"]), rp_when(Bool.and(edit, rp_is_comp(c, Rp.KSkill{})), rp_skill(vn, args, m), rp_when(Bool.and(edit, Bool.and(rp_is_comp(c, Rp.KFactory{}), Bool.or(rp_is_verb(v, Rp.ACreate{}), Maybe.is_some(&2, Rp.Args, args)))), rp_factory(args), None{})))))

def rp_check.at(+v: Rp.Verb, +c: Rp.Comp, r: Maybe<&2, String>) -> Rp.Check:
  match r:
    case None{}:
      Rp.COk{v, c}
    case Some{msg}:
      Rp.CBad{msg}

def rp_check.comp(+v: Rp.Verb, m: Maybe<&2, Rp.Comp>, +id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, p: Maybe<&2, Rp.Pyref>, args: Maybe<&2, Rp.Args>) -> Rp.Check:
  match m:
    case None{}:
      Rp.CBad{"unsupported kind"}
    case Some{+c}:
      rp_check.at(v, c, rp_rules(v, c, id, cid, titled, content, p, args))

def rp_check.verb(m: Maybe<&2, Rp.Verb>, k: Maybe<&2, Rp.Comp>, id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, p: Maybe<&2, Rp.Pyref>, args: Maybe<&2, Rp.Args>) -> Rp.Check:
  match m:
    case None{}:
      Rp.CBad{"unsupported action"}
    case Some{v}:
      rp_check.comp(v, k, id, cid, titled, content, p, args)

# an edit's validation, its computed id given (TS-mirrored messages)
def rp_check(e: Rp.Ed, cid: Maybe<&2, String>) -> Rp.Check:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      rp_check.verb(verb, comp, id, cid, Maybe.is_some(&2, String, title), content, pyref, args)

# Plan
# ----

def rp_lookup.at(hit: Bool, p: Bool, r: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      r

def rp_lookup.touch(t: Rp.Touch, +c: Rp.Comp, +id: String, r: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match t:
    case Rp.Touch{tc, tid, p}:
      rp_lookup.at(Bool.and(rp_comp_eq(tc, c), String.eq(tid, id)), p, r)

# whether the latest earlier edit of the entry left it present (none: no
# earlier edit wrote or removed it)
def rp_lookup(ts: List<&2, Rp.Touch>, +c: Rp.Comp, +id: String) -> Maybe<&2, Bool>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      rp_lookup.touch(t, c, id, rp_lookup(rest, c, id))

def rp_out.first(b: Bool, msg: String, r: Rp.Out) -> Rp.Out:
  match b:
    case True{}:
      Rp.ORefused{msg}
    case False{}:
      r

def rp_out.final(v: Rp.Verb, +p: Bool) -> Rp.Out:
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

# a valid edit's outcome: a baseline change, the factory opt-in, the
# session's memory, then the entry's presence
def rp_decide(o: Rp.Opts, e: Rp.Ed, +v: Rp.Verb, +c: Rp.Comp, +look: Maybe<&2, Bool>) -> Rp.Out:
  match o:
    case Rp.Opts{factory, baseline}:
      match e:
        case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
          rp_out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", rp_out.first(Bool.and(rp_is_comp(c, Rp.KFactory{}), Bool.and(Bool.not(rp_is_verb(v, Rp.ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", rp_out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", rp_out.final(v, Maybe.default(&2, Bool, look, exists)))))

def rp_invalid_verb.at(comp: Maybe<&2, Rp.Comp>, verb: Maybe<&2, Rp.Verb>) -> Rp.Verb:
  match comp:
    case None{}:
      Rp.ACreate{}
    case Some{c}:
      match verb:
        case None{}:
          Rp.ACreate{}
        case Some{v}:
          v

# an invalid edit's action: create without a kind, else its action (none:
# create)
def rp_invalid_verb(e: Rp.Ed) -> Rp.Verb:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      rp_invalid_verb.at(comp, verb)

def rp_comp_of(e: Rp.Ed) -> Rp.Comp:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      rp_comp_or_memory(comp)

def rp_row.at(+o: Rp.Opts, +e: Rp.Ed, +ts: List<&2, Rp.Touch>, +id: String, k: Rp.Check) -> Rp.Row:
  match k:
    case Rp.CBad{msg}:
      Rp.Row{rp_invalid_verb(e), rp_comp_of(e), id, Rp.OInvalid{msg}}
    case Rp.COk{+v, +c}:
      Rp.Row{v, c, id, rp_decide(o, e, v, c, rp_lookup(ts, c, id))}

# an edit's row, the earlier edits' writes and removals given
def rp_row(+o: Rp.Opts, +e: Rp.Ed, +ts: List<&2, Rp.Touch>) -> Rp.Row:
  rp_row.at(o, e, ts, Maybe.default(&2, String, rp_computed(e), ""), rp_check(e, rp_computed(e)))

def rp_touch.out(x: Rp.Out, +c: Rp.Comp, +id: String, ts: List<&2, Rp.Touch>) -> List<&2, Rp.Touch>:
  match x:
    case Rp.OInvalid{m}:
      ts
    case Rp.ORefused{m}:
      ts
    case Rp.ORemoved{}:
      Rp.Touch{c, id, False{}} <> ts
    case Rp.OWritten{}:
      Rp.Touch{c, id, True{}} <> ts

# the writes and removals after a row
def rp_touch(r: Rp.Row, ts: List<&2, Rp.Touch>) -> List<&2, Rp.Touch>:
  match r:
    case Rp.Row{v, c, id, x}:
      rp_touch.out(x, c, id, ts)

def rp_plan.rows(+o: Rp.Opts, eds: List<&2, Rp.Ed>, +ts: List<&2, Rp.Touch>) -> List<&2, Rp.Row>:
  match eds:
    case Nil{}:
      Nil{}
    case +e <> t:
      rp_row(o, e, ts) <> rp_plan.rows(o, t, rp_touch(rp_row(o, e, ts), ts))

def rp_change.out(x: Rp.Out, v: Rp.Verb, c: Rp.Comp, id: String, r: List<&2, String>) -> List<&2, String>:
  match x:
    case Rp.OInvalid{m}:
      r
    case Rp.ORefused{m}:
      r
    case Rp.ORemoved{}:
      String.concat([rp_verb_name(v), " ", rp_comp_name(c), ":", id]) <> r
    case Rp.OWritten{}:
      String.concat([rp_verb_name(v), " ", rp_comp_name(c), ":", id]) <> r

def rp_change(w: Rp.Row, r: List<&2, String>) -> List<&2, String>:
  match w:
    case Rp.Row{v, c, id, x}:
      rp_change.out(x, v, c, id, r)

# the change line of every applied row: `<action> <kind>:<id>`
def rp_changes(rows: List<&2, Rp.Row>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case w <> t:
      rp_change(w, rp_changes(t))

# a proposal's rows and change lines
def rp_plan(+o: Rp.Opts, eds: List<&2, Rp.Ed>) -> Rp.Plan:
  +rows = rp_plan.rows(o, eds, [])
  Rp.Plan{rows, rp_changes(rows)}

# Rollback
# --------

def rp_back.restore(after: Bool) -> Rp.Verb:
  match after:
    case True{}:
      Rp.AUpdate{}
    case False{}:
      Rp.ACreate{}

def rp_back.pick.at(applied: Bool, before: Bool, +after: Bool, at: Nat) -> List<&2, Rp.Pick>:
  match applied:
    case False{}:
      []
    case True{}:
      match before:
        case True{}:
          [Rp.Pick{at, rp_back.restore(after)}]
        case False{}:
          match after:
            case True{}:
              [Rp.Pick{at, Rp.ADelete{}}]
            case False{}:
              []

def rp_back.pick(w: Rp.Was, at: Nat) -> List<&2, Rp.Pick>:
  match w:
    case Rp.Was{applied, before, after}:
      rp_back.pick.at(applied, before, after, at)

def rp_back.fwd(was: List<&2, Rp.Was>, +at: Nat) -> List<&2, Rp.Pick>:
  match was:
    case Nil{}:
      Nil{}
    case w <> t:
      List.append(&2, Rp.Pick, rp_back.pick(w, at), rp_back.fwd(t, 1n+at))

# the rollback of a result: its applied rows last first, a stored before
# restored (updated when the row wrote an after, else created), a written
# entry without a before deleted
def rp_back(+id: String, was: List<&2, Rp.Was>) -> Rp.Back:
  Rp.Back{String.concat(["Rollback refinement ", id]), String.concat(["Restores continual harness state snapshots from refinement ", id, "."]), "Faulty refinement edits are reverted.", String.concat(["Rollback ", id]), List.reverse(&2, Rp.Pick, rp_back.fwd(was, 0n))}

# Texts
# -----

# a proposal's texts: each string given, else its default
def rp_norm(s: Maybe<&2, String>, r: Maybe<&2, String>, o: Maybe<&2, String>) -> Rp.Texts:
  Rp.Texts{Maybe.default(&2, String, s, "Refined continual harness state"), Maybe.default(&2, String, r, ""), Maybe.default(&2, String, o, "")}

# Truncation
# ----------

def rp_scan.code(+c: Char, x: U32) -> Bool:
  U32.is_eq(Char.to_u32(c), x)

def rp_scan.out(ins: Bool, +bs: Bool, +q: Bool, op: Bool, cl: Bool, +o: Nat, +k: Nat) -> Rp.Scan:
  match ins:
    case True{}:
      match bs:
        case True{}:
          Rp.Scan{True{}, True{}, o, k}
        case False{}:
          match q:
            case True{}:
              Rp.Scan{False{}, False{}, o, k}
            case False{}:
              Rp.Scan{True{}, False{}, o, k}
    case False{}:
      match q:
        case True{}:
          Rp.Scan{True{}, False{}, o, k}
        case False{}:
          match op:
            case True{}:
              Rp.Scan{False{}, False{}, 1n+o, k}
            case False{}:
              match cl:
                case True{}:
                  Rp.Scan{False{}, False{}, o, 1n+k}
                case False{}:
                  Rp.Scan{False{}, False{}, o, k}

def rp_scan.at(esc: Bool, +ins: Bool, +c: Char, +o: Nat, +k: Nat) -> Rp.Scan:
  match esc:
    case True{}:
      Rp.Scan{ins, False{}, o, k}
    case False{}:
      rp_scan.out(ins, rp_scan.code(c, 92), rp_scan.code(c, 34), Bool.or(rp_scan.code(c, 123), rp_scan.code(c, 91)), Bool.or(rp_scan.code(c, 125), rp_scan.code(c, 93)), o, k)

# the scan after a char
def rp_scan.step(st: Rp.Scan, +c: Char) -> Rp.Scan:
  match st:
    case Rp.Scan{ins, esc, o, k}:
      rp_scan.at(esc, ins, c, o, k)

def rp_scan(s: String, st: Rp.Scan) -> Rp.Scan:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      rp_scan(t, rp_scan.step(st, c))

def rp_scan.done(st: Rp.Scan) -> Bool:
  match st:
    case Rp.Scan{ins, esc, o, k}:
      Bool.or(ins, Nat.is_gt(o, k))

# whether a JSON candidate ends mid-value: in a string, or more brackets
# opened than closed (outside strings; a backslash escapes the next char)
def rp_incomplete(text: String) -> Bool:
  rp_scan.done(rp_scan(text, Rp.Scan{False{}, False{}, 0n, 0n}))

# Fit
# ---

def rp_fit.room.at(z: Bool, m: Nat) -> Rp.Step:
  match z:
    case True{}:
      Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."}
    case False{}:
      Rp.TOk{m}

def rp_fit.room(+m: Nat) -> Rp.Step:
  rp_fit.room.at(Nat.is_eq(m, 0n), m)

def rp_fit.probe.at(b: Bool, +low: Nat, +high: Nat) -> Rp.Step:
  match b:
    case True{}:
      +mid = Nat.div(Nat.add(Nat.add(low, high), 1n), 2n)
      Rp.TTry{mid, Rp.SProbe{low, high, mid}}
    case False{}:
      Rp.TTry{low, Rp.SFinal{}}

# the next length the binary search measures, or the final one
def rp_fit.probe(+low: Nat, +high: Nat) -> Rp.Step:
  rp_fit.probe.at(Nat.is_lt(low, high), low, high)

def rp_fit.full(trim: Bool, conv: Nat, r: Rp.Step) -> Rp.Step:
  match trim:
    case True{}:
      rp_fit.probe(0n, conv)
    case False{}:
      r

def rp_fit.narrow(fits: Bool, low: Nat, +high: Nat, +len: Nat) -> Rp.Step:
  match fits:
    case True{}:
      rp_fit.probe(len, high)
    case False{}:
      rp_fit.probe(low, Nat.sub(len, 1n))

def rp_fit.at(st: Rp.Search, +conv: Nat, +plen: Nat, +sysr: Nat, +budget: Nat, +mx: Nat, +cw: Nat) -> Rp.Step:
  match st:
    case Rp.SFull{}:
      rp_fit.full(Bool.and(Bool.not(Nat.is_le(Nat.add(sysr, plen), budget)), Bool.not(Nat.is_eq(conv, 0n))), conv, rp_fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen)))))
    case Rp.SProbe{low, high, len}:
      rp_fit.narrow(Nat.is_le(Nat.add(sysr, plen), budget), low, high, len)
    case Rp.SFinal{}:
      rp_fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen))))

# the fit of a refinement request: the window, the conversation's length,
# where the search is and the length of the prompt it measured (lengths in
# UTF-8 bytes, one token each)
def rp_fit(w: Rp.Win, conv: Nat, st: Rp.Search, plen: Nat) -> Rp.Step:
  match w:
    case Rp.Win{+cw, +mx, res, sys}:
      rp_fit.at(st, conv, plen, Nat.add(sys, 1024n), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n))), mx, cw)

# Example helpers
# ---------------

# an edit with an action, a kind, an id, a title and content, a reference
# and arguments, stored or not, held
def rp_ex(v: Rp.Verb, c: Rp.Comp, id: Maybe<&2, String>, p: Maybe<&2, Rp.Pyref>, a: Maybe<&2, Rp.Args>, stored: Bool) -> Rp.Ed:
  Rp.Ed{Some{v}, Some{c}, id, Some{"T"}, True{}, p, a, stored, False{}, True{}}

# Laws: the model
# ---------------

# LAW refine_plan_slug_spec (R1): every title slugs to the spec's
# EXCLUDES: a char kept that is not an ASCII lowercase letter or digit, an
#   uppercase letter not lowered, a run of `_` kept, a `_` left at an end,
#   another length cap, the fallback for a non-empty slug
law refine_plan_slug_spec:
  for +raw: String
  for +fb: String
  {Rp.slug(raw, fb) == rp_slug(raw, fb) : String}

# LAW refine_plan_ids_spec (R2): every edit's computed id is the spec's
# EXCLUDES: a slug for an update or delete, a slug over a given id, a
#   title slugged without the kind's name as its fallback, an edit lost or
#   reordered
law refine_plan_ids_spec:
  for +eds: List<&2, Rp.Ed>
  {Rp.ids(eds) == rp_ids(eds) : List<&2, Maybe<&2, String>>}

# LAW refine_plan_check_spec (R3): every edit validates to the spec's
# message, or to its action and kind
# EXCLUDES: a rule skipped or checked in another order, a changed message,
#   a null spec key read as given, an update without arguments refused, a
#   delete held to a create's rules
law refine_plan_check_spec:
  for +e: Rp.Ed
  for +cid: Maybe<&2, String>
  {Rp.check(e, cid) == rp_check(e, cid) : Rp.Check}

# LAW refine_plan_plan_spec (R2-R4): every proposal plans to the spec's
# rows and change lines
# EXCLUDES: an earlier edit's write or removal ignored, a baseline change
#   checked for an entry the proposal already touched, the gates in another
#   order, a delete of a factory refused while the opt-in is off, a refused
#   or invalid row counted as a change, a change line in another shape
law refine_plan_plan_spec:
  for +o: Rp.Opts
  for +eds: List<&2, Rp.Ed>
  {Rp.plan(o, eds) == rp_plan(o, eds) : Rp.Plan}

# LAW refine_plan_back_spec (R5): every result rolls back to the spec's
# edits and texts
# EXCLUDES: rows rolled back first first, an unapplied row reverted, a
#   restore by the wrong action, a created entry left, another row index
law refine_plan_back_spec:
  for +id: String
  for +was: List<&2, Rp.Was>
  {Rp.back(id, was) == rp_back(id, was) : Rp.Back}

# LAW refine_plan_norm_spec (R6): every proposal's texts are the spec's
# EXCLUDES: another default, a default over a given text
law refine_plan_norm_spec:
  for +s: Maybe<&2, String>
  for +r: Maybe<&2, String>
  for +o: Maybe<&2, String>
  {Rp.norm(s, r, o) == rp_norm(s, r, o) : Rp.Texts}

# LAW refine_plan_incomplete_spec (R7): every candidate scans to the spec's
# answer
# EXCLUDES: a bracket counted inside a string, an escaped quote closing a
#   string, extra closers read as open brackets, a closed candidate called
#   cut off
law refine_plan_incomplete_spec:
  for +text: String
  {Rp.incomplete(text) == rp_incomplete(text) : Bool}

# LAW refine_plan_fit_spec (R8): every step of the fit is the spec's
# EXCLUDES: another reserve or budget, the middle rounded down, a bound
#   moved the wrong way, a trim of an empty conversation, max tokens past
#   the window, a zero answered as room
law refine_plan_fit_spec:
  for +w: Rp.Win
  for +conv: Nat
  for +st: Rp.Search
  for +plen: Nat
  {Rp.fit(w, conv, st, plen) == rp_fit(w, conv, st, plen) : Rp.Step}

# LAW refine_plan_slug_example (R1): anchor: Rust's slugs
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_slug_example:
  {[Rp.slug(" Hi, Yo! ", "m"), Rp.slug("\u{130}x", "m"), Rp.slug("_-_", "fb"), Rp.slug("\u{212A}A9", "z"), Rp.slug("a\u{E9}b", "z")] == ["hi_yo", "i_x", "fb", "ka9", "a_b"] : List<&2, String>}

# LAW refine_plan_ids_example (R2): anchor: an id kept, a create's title
# slugged, a title-less create named by its kind, an update without an id
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_ids_example:
  {Rp.ids([rp_ex(Rp.ACreate{}, Rp.KMemory{}, Some{"m1"}, None{}, None{}, False{}), rp_ex(Rp.ACreate{}, Rp.KSkill{}, None{}, None{}, None{}, False{}), Rp.Ed{Some{Rp.ACreate{}}, None{}, None{}, None{}, False{}, None{}, None{}, False{}, False{}, True{}}, rp_ex(Rp.AUpdate{}, Rp.KSkill{}, None{}, None{}, None{}, False{})]) == [Some{"m1"}, Some{"t"}, Some{"memory"}, None{}] : List<&2, Maybe<&2, String>>}

# LAW refine_plan_check_example (R3): anchor: Rust's validation tests
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_check_example:
  {[Rp.check(Rp.Ed{None{}, Some{Rp.KMemory{}}, Some{"m"}, Some{"t"}, True{}, None{}, None{}, False{}, False{}, True{}}, Some{"m"}), Rp.check(rp_ex(Rp.AUpdate{}, Rp.KPrompt{}, Some{"base_system_prompt"}, None{}, None{}, False{}), Some{"base_system_prompt"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KSkill{}, None{}, None{}, None{}, False{}), Some{"t"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KSkill{}, None{}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VMissing{}}}, False{}), Some{"t"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KSkill{}, None{}, Some{Rp.Pyref{Some{"python"}, Some{"p.m"}, None{}, Some{"run"}, None{}}}, Some{Rp.Args{Rp.VMissing{}, Rp.VMissing{}}}, False{}), Some{"t"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KSkill{}, None{}, Some{Rp.Pyref{Some{"shell"}, Some{"p.m"}, None{}, Some{"run"}, None{}}}, Some{Rp.Args{Rp.VMissing{}, Rp.VMissing{}}}, False{}), Some{"t"}), Rp.check(rp_ex(Rp.AUpdate{}, Rp.KMemory{}, None{}, None{}, None{}, False{}), None{})] == [Rp.CBad{"unsupported action"}, Rp.CBad{"base system prompt is not editable"}, Rp.CBad{"create skill requires arguments"}, Rp.CBad{"create skill requires python reference"}, Rp.COk{Rp.ACreate{}, Rp.KSkill{}}, Rp.CBad{"create skill reference.type must be python"}, Rp.CBad{"update requires id"}] : List<&2, Rp.Check>}

# LAW refine_plan_factory_example (R3): anchor: Rust's factory spec tests
# (a dag, a machine, both, neither, a non-object machine, no arguments, a
# delete, an update without arguments, a dag with a null machine)
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_factory_example:
  {[Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VObject{}, Rp.VMissing{}}}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VObject{}}}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VObject{}, Rp.VObject{}}}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VMissing{}}}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VOther{}}}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, None{}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.ADelete{}, Rp.KFactory{}, Some{"f"}, None{}, None{}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.AUpdate{}, Rp.KFactory{}, Some{"f"}, None{}, None{}, False{}), Some{"f"}), Rp.check(rp_ex(Rp.AUpdate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VObject{}, Rp.VNull{}}}, False{}), Some{"f"})] == [Rp.COk{Rp.ACreate{}, Rp.KFactory{}}, Rp.COk{Rp.ACreate{}, Rp.KFactory{}}, Rp.CBad{"pass either dag or machine form, not both"}, Rp.CBad{"factory entry requires a dag or machine object in arguments"}, Rp.CBad{"factory entry requires a dag or machine object in arguments"}, Rp.CBad{"factory entry requires a dag or machine object in arguments"}, Rp.COk{Rp.ADelete{}, Rp.KFactory{}}, Rp.COk{Rp.AUpdate{}, Rp.KFactory{}}, Rp.COk{Rp.AUpdate{}, Rp.KFactory{}}] : List<&2, Rp.Check>}

# LAW refine_plan_plan_example (R4): anchor: Rust's apply tests (a create,
# a duplicate create, an update and a delete of it, a factory while the
# opt-in is off, a memory in a chat-memory session, a subagent)
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_plan_example:
  {Rp.plan(Rp.Opts{False{}, False{}}, [rp_ex(Rp.ACreate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ACreate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.AUpdate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ADelete{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ADelete{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VObject{}}}, False{}), rp_ex(Rp.ADelete{}, Rp.KFactory{}, Some{"g"}, None{}, None{}, True{}), Rp.Ed{Some{Rp.ACreate{}}, Some{Rp.KPrompt{}}, Some{"p"}, Some{"T"}, True{}, None{}, None{}, False{}, False{}, False{}}, rp_ex(Rp.ACreate{}, Rp.KSubagent{}, Some{"m"}, None{}, None{}, False{})]) == Rp.Plan{[Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "m", Rp.OWritten{}}, Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "m", Rp.ORefused{"entry already exists"}}, Rp.Row{Rp.AUpdate{}, Rp.KMemory{}, "m", Rp.OWritten{}}, Rp.Row{Rp.ADelete{}, Rp.KMemory{}, "m", Rp.ORemoved{}}, Rp.Row{Rp.ADelete{}, Rp.KMemory{}, "m", Rp.ORefused{"entry not found"}}, Rp.Row{Rp.ACreate{}, Rp.KFactory{}, "f", Rp.ORefused{"the factory is disabled; run /factory on to enable it"}}, Rp.Row{Rp.ADelete{}, Rp.KFactory{}, "g", Rp.ORemoved{}}, Rp.Row{Rp.ACreate{}, Rp.KPrompt{}, "p", Rp.ORefused{"eukhe's memory is the chat: say it in your reply"}}, Rp.Row{Rp.ACreate{}, Rp.KSubagent{}, "m", Rp.OWritten{}}], ["create memory:m", "update memory:m", "delete memory:m", "delete factory:g", "create subagent:m"]} : Rp.Plan}

# LAW refine_plan_baseline_example (R4): anchor: with a baseline, an entry
# changed since planning refuses until the proposal itself writes it; an
# invalid edit's row keeps its action and kind, a kind-less one is a
# memory create
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_baseline_example:
  {Rp.plan(Rp.Opts{True{}, True{}}, [Rp.Ed{Some{Rp.AUpdate{}}, Some{Rp.KSkill{}}, Some{"s"}, Some{"T"}, True{}, None{}, None{}, True{}, True{}, True{}}, Rp.Ed{Some{Rp.ACreate{}}, Some{Rp.KMemory{}}, Some{"m"}, Some{"T"}, True{}, None{}, None{}, False{}, True{}, True{}}, Rp.Ed{Some{Rp.AUpdate{}}, Some{Rp.KMemory{}}, Some{"m"}, Some{"T"}, True{}, None{}, None{}, False{}, True{}, True{}}, Rp.Ed{Some{Rp.ADelete{}}, None{}, Some{"x"}, None{}, False{}, None{}, None{}, False{}, False{}, True{}}]) == Rp.Plan{[Rp.Row{Rp.AUpdate{}, Rp.KSkill{}, "s", Rp.OInvalid{"update skill requires arguments"}}, Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "m", Rp.ORefused{"entry changed during refinement planning"}}, Rp.Row{Rp.AUpdate{}, Rp.KMemory{}, "m", Rp.ORefused{"entry changed during refinement planning"}}, Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "x", Rp.OInvalid{"unsupported kind"}}], []} : Rp.Plan}

# LAW refine_plan_back_example (R5): anchor: a rollback's edits and texts
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_back_example:
  {Rp.back("r1", [Rp.Was{True{}, False{}, True{}}, Rp.Was{True{}, True{}, True{}}, Rp.Was{False{}, True{}, True{}}, Rp.Was{True{}, True{}, False{}}, Rp.Was{True{}, False{}, False{}}]) == Rp.Back{"Rollback refinement r1", "Restores continual harness state snapshots from refinement r1.", "Faulty refinement edits are reverted.", "Rollback r1", [Rp.Pick{3n, Rp.ACreate{}}, Rp.Pick{1n, Rp.AUpdate{}}, Rp.Pick{0n, Rp.ADelete{}}]} : Rp.Back}

# LAW refine_plan_norm_example (R6): anchor: Rust's defaults
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_norm_example:
  {[Rp.norm(None{}, None{}, None{}), Rp.norm(Some{"s"}, Some{"r"}, Some{"o"})] == [Rp.Texts{"Refined continual harness state", "", ""}, Rp.Texts{"s", "r", "o"}] : List<&2, Rp.Texts>}

# LAW refine_plan_incomplete_example (R7): anchor: a reply cut in a string,
# a closed one, a brace inside a string, an escaped quote, closers first
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_incomplete_example:
  {[Rp.incomplete("{\"a\":[{\"b\":\"cr"), Rp.incomplete("{\"a\":[]}"), Rp.incomplete("{\"}\""), Rp.incomplete("\"\\\""), Rp.incomplete("]{"), Rp.incomplete("[\"\\\\\"")] == [True{}, False{}, True{}, True{}, False{}, True{}] : List<&2, Bool>}

# LAW refine_plan_fit_example (R8): anchor: a prompt that fits, a trim
# started, a probe that fits and one that does not, the last probe, the
# final prompt, no room
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_fit_example:
  {[Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 0n, Rp.SFull{}, 500n), Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 40n, Rp.SFull{}, 1100n), Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 40n, Rp.SProbe{0n, 40n, 20n}, 1000n), Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 40n, Rp.SProbe{20n, 40n, 30n}, 1020n), Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 40n, Rp.SProbe{20n, 21n, 21n}, 1000n), Rp.fit(Rp.Win{2100n, 100n, 64n, 0n}, 40n, Rp.SFinal{}, 1000n), Rp.fit(Rp.Win{1000n, 100n, 64n, 0n}, 0n, Rp.SFull{}, 10n)] == [Rp.TOk{100n}, Rp.TTry{20n, Rp.SProbe{0n, 40n, 20n}}, Rp.TTry{30n, Rp.SProbe{20n, 40n, 30n}}, Rp.TTry{25n, Rp.SProbe{20n, 29n, 25n}}, Rp.TTry{21n, Rp.SFinal{}}, Rp.TOk{76n}, Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."}] : List<&2, Rp.Step>}
