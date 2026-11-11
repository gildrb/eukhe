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
# R1: the slug of a text with a fallback (the pre-port Rust `slug`,
#     eukhe-core refinement/planner.rs at 74b32a993^): the text trimmed
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
# R3: an edit's validation (the pre-port Rust `validate_edit`,
#     planner.rs at 74b32a993^, with the TS messages; the first that
#     applies; <a> is the action's name `create`, `update` or
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
#     with its action (none, or an edit without a kind: create), its kind (none: memory), the id and
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
#
# Laws: R1 refine_plan_slug_words; R2 refine_plan_ids_split,
# refine_plan_id_given, refine_plan_id_create, refine_plan_id_none; R3
# refine_plan_check_rules (this file); R4 refine_plan_plan_rows,
# refine_plan_plan_lines; R5 refine_plan_back_whole (plan.bend); R7
# refine_plan_incomplete_lex; R8 refine_plan_fit_final_room,
# refine_plan_fit_final_no_room, refine_plan_fit_full_keeps,
# refine_plan_fit_full_trims, refine_plan_fit_probe_up,
# refine_plan_fit_probe_up_last, refine_plan_fit_probe_down,
# refine_plan_fit_probe_down_last (walk.bend); R9 the entry laws
# (entry.bend). R6 is a default per text: no law beyond
# refine_plan_norm_example and the entry's. The *_example laws below are
# anchors, not coverage.

# Spec helpers
# ------------

# Names (R3's <a> and R4's change lines: the action's and the kind's name)
# -------------------------------------------------------------------------

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

# R2: a kind's name; no kind: memory
def rs_kind_name(m: Maybe<&2, Rp.Comp>) -> String:
  match m:
    case None{}:
      "memory"
    case Some{c}:
      rp_comp_name(c)

# Slug (R1)
# ---------
# The slug is written in one pass as words: a word is a run of slug chars
# (ASCII lowercase letters and digits, after lowercasing), and one `_` is
# written between two words, never at an end; then the first 80 chars,
# the fallback when no word.

# What one char of a title gives the slug
type RsCh is Data:
  RsKeep{c: Char}
  RsCut{}
  RsKeepCut{c: Char}

# R1's lowercase table, row by row
def rs_ch.at(alnum: Bool, upper: Bool, dotted: Bool, kelvin: Bool, c: Char) -> RsCh:
  match alnum:
    case True{}:
      # R1: an ASCII lowercase letter or digit is a slug char
      RsKeep{c}
    case False{}:
      match upper:
        case True{}:
          # R1: an ASCII uppercase letter lowercases to a slug char
          RsKeep{Char.to_lower(c)}
        case False{}:
          match dotted:
            case True{}:
              # R1: U+0130 lowercases to `i` (a slug char), then U+0307 (a cut)
              RsKeepCut{'i'}
            case False{}:
              match kelvin:
                case True{}:
                  # R1: U+212A lowercases to `k`
                  RsKeep{'k'}
                case False{}:
                  # R1: every other char is a cut
                  RsCut{}

def rs_ch(+c: Char) -> RsCh:
  rs_ch.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c)

# Where the writer is: no word written yet, in a word, past a cut that
# follows a word
type RsAt is Data:
  RsStart{}
  RsIn{}
  RsGap{}

# a slug char written: after a cut that follows a word, `_` first
def rs_slug.word(at: RsAt, c: Char, r: String) -> String:
  match at:
    case RsStart{}:
      SCon{c, r}
    case RsIn{}:
      SCon{c, r}
    case RsGap{}:
      SCon{'_', SCon{c, r}}

def rs_slug.put(k: RsCh, at: RsAt, r: String) -> String:
  match k:
    case RsKeep{c}:
      rs_slug.word(at, c, r)
    case RsCut{}:
      r
    case RsKeepCut{c}:
      rs_slug.word(at, c, r)

def rs_slug.next(k: RsCh, at: RsAt) -> RsAt:
  match k:
    case RsKeep{c}:
      RsIn{}
    case RsKeepCut{c}:
      RsGap{}
    case RsCut{}:
      match at:
        case RsStart{}:
          RsStart{}
        case RsIn{}:
          RsGap{}
        case RsGap{}:
          RsGap{}

# the words of a title joined by one `_` each
def rs_slug.go(s: String, +at: RsAt) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      +k = rs_ch(c)
      rs_slug.put(k, at, rs_slug.go(t, rs_slug.next(k, at)))

def rs_slug.or(t: String, fb: String) -> String:
  match t:
    case SNil{}:
      fb
    case SCon{h, r}:
      SCon{h, r}

# R1: the title's words joined by `_`, its first 80 chars; none: the
# fallback
def rs_slug(raw: String, fb: String) -> String:
  rs_slug.or(String.take(rs_slug.go(raw, RsStart{}), 80n), fb)

# Validation (R3)
# ----------------

def rs_is_create(v: Rp.Verb) -> Bool:
  match v:
    case Rp.ACreate{}:
      True{}
    case Rp.AUpdate{}:
      False{}
    case Rp.ADelete{}:
      False{}

def rs_is_delete(v: Rp.Verb) -> Bool:
  match v:
    case Rp.ACreate{}:
      False{}
    case Rp.AUpdate{}:
      False{}
    case Rp.ADelete{}:
      True{}

def rs_is_prompt(c: Rp.Comp) -> Bool:
  match c:
    case Rp.KPrompt{}:
      True{}
    case Rp.KMemory{}:
      False{}
    case Rp.KSkill{}:
      False{}
    case Rp.KSubagent{}:
      False{}
    case Rp.KFactory{}:
      False{}

def rs_is_skill(c: Rp.Comp) -> Bool:
  match c:
    case Rp.KPrompt{}:
      False{}
    case Rp.KMemory{}:
      False{}
    case Rp.KSkill{}:
      True{}
    case Rp.KSubagent{}:
      False{}
    case Rp.KFactory{}:
      False{}

def rs_is_factory(c: Rp.Comp) -> Bool:
  match c:
    case Rp.KPrompt{}:
      False{}
    case Rp.KMemory{}:
      False{}
    case Rp.KSkill{}:
      False{}
    case Rp.KSubagent{}:
      False{}
    case Rp.KFactory{}:
      True{}

# a string field that is the text x
def rs_named(m: Maybe<&2, String>, x: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      String.eq(y, x)

# a string field that holds a non-empty string
def rs_filled(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      Bool.not(String.is_empty(y))

# a reference whose type is the string `python`
def rs_ref_python(p: Maybe<&2, Rp.Pyref>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Rp.Pyref{ty, imp, pyimp, call, pat}:
          rs_named(ty, "python")

# a reference with a non-empty import or python_import
def rs_ref_import(p: Maybe<&2, Rp.Pyref>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Rp.Pyref{ty, imp, pyimp, call, pat}:
          Bool.or(rs_filled(imp), rs_filled(pyimp))

# a reference with a non-empty callable or call_pattern
def rs_ref_callable(p: Maybe<&2, Rp.Pyref>) -> Bool:
  match p:
    case None{}:
      False{}
    case Some{r}:
      match r:
        case Rp.Pyref{ty, imp, pyimp, call, pat}:
          Bool.or(rs_filled(call), rs_filled(pat))

# a factory spec key given: neither missing nor JSON null
def rs_given(v: Rp.Val) -> Bool:
  match v:
    case Rp.VMissing{}:
      False{}
    case Rp.VNull{}:
      False{}
    case Rp.VObject{}:
      True{}
    case Rp.VOther{}:
      True{}

# arguments with both a dag and a machine given
def rs_both(a: Maybe<&2, Rp.Args>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Rp.Args{dag, machine}:
          Bool.and(rs_given(dag), rs_given(machine))

# a factory spec key that is a JSON object
def rs_object(v: Rp.Val) -> Bool:
  match v:
    case Rp.VMissing{}:
      False{}
    case Rp.VNull{}:
      False{}
    case Rp.VObject{}:
      True{}
    case Rp.VOther{}:
      False{}

# arguments whose spec form is an object: the machine when given, else
# the dag
def rs_spec_object(a: Maybe<&2, Rp.Args>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      match x:
        case Rp.Args{dag, machine}:
          match machine:
            case Rp.VMissing{}:
              rs_object(dag)
            case Rp.VNull{}:
              rs_object(dag)
            case Rp.VObject{}:
              True{}
            case Rp.VOther{}:
              False{}

# a rule of R3: whether the edit breaks it, and its message
type RsRule is Data:
  RsRule{broken: Bool, msg: String}

def rs_first.at(r: RsRule, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match r:
    case RsRule{b, m}:
      match b:
        case True{}:
          Some{m}
        case False{}:
          rest

# the message of the first rule broken
def rs_first(rs: List<&2, RsRule>) -> Maybe<&2, String>:
  match rs:
    case Nil{}:
      None{}
    case r <> t:
      rs_first.at(r, rs_first(t))

# R3's rules of an edit with an action and a kind, in R3's order, each
# with its message (<a> the action's name):
#   R3: a prompt whose id or computed id is base_system_prompt
#   R3: an update or delete without an id: `<a> requires id`
#   R3: a create or update without a title or without content
#   R3: a skill create or update without arguments
#   R3: ... without a reference
#   R3: ... a reference whose type is not the string python
#   R3: ... without a non-empty import or python_import
#   R3: ... without a non-empty callable or call_pattern
#   R3: a factory create, or update with arguments: both a dag and a
#       machine given (neither missing nor null)
#   R3: ... the machine (given; else the dag) not an object
def rs_rules(+v: Rp.Verb, +c: Rp.Comp, +id: Maybe<&2, String>, cid: Maybe<&2, String>, title: Maybe<&2, String>, content: Bool, +p: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> List<&2, RsRule>:
  +vn = rp_verb_name(v)
  +edit = Bool.not(rs_is_delete(v))
  +sk = Bool.and(edit, rs_is_skill(c))
  +fa = Bool.and(edit, Bool.and(rs_is_factory(c), Bool.or(rs_is_create(v), Maybe.is_some(&2, Rp.Args, args))))
  [RsRule{Bool.and(rs_is_prompt(c), Bool.or(rs_named(id, "base_system_prompt"), rs_named(cid, "base_system_prompt"))), "base system prompt is not editable"}, RsRule{Bool.and(Bool.not(rs_is_create(v)), Maybe.is_none(&2, String, id)), String.concat([vn, " requires id"])}, RsRule{Bool.and(edit, Bool.not(Bool.and(Maybe.is_some(&2, String, title), content))), String.concat([vn, " requires title and content"])}, RsRule{Bool.and(sk, Maybe.is_none(&2, Rp.Args, args)), String.concat([vn, " skill requires arguments"])}, RsRule{Bool.and(sk, Maybe.is_none(&2, Rp.Pyref, p)), String.concat([vn, " skill requires python reference"])}, RsRule{Bool.and(sk, Bool.not(rs_ref_python(p))), String.concat([vn, " skill reference.type must be python"])}, RsRule{Bool.and(sk, Bool.not(rs_ref_import(p))), String.concat([vn, " skill requires python import"])}, RsRule{Bool.and(sk, Bool.not(rs_ref_callable(p))), String.concat([vn, " skill requires callable or call_pattern"])}, RsRule{Bool.and(fa, rs_both(args)), "pass either dag or machine form, not both"}, RsRule{Bool.and(fa, Bool.not(rs_spec_object(args))), "factory entry requires a dag or machine object in arguments"}]

def rs_check.at(+v: Rp.Verb, +c: Rp.Comp, m: Maybe<&2, String>) -> Rp.Check:
  match m:
    case None{}:
      Rp.COk{v, c}
    case Some{x}:
      Rp.CBad{x}

def rs_check.verb(m: Maybe<&2, Rp.Verb>, k: Maybe<&2, Rp.Comp>, +id: Maybe<&2, String>, +cid: Maybe<&2, String>, +title: Maybe<&2, String>, +content: Bool, +p: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> Rp.Check:
  match m:
    case None{}:
      Rp.CBad{"unsupported action"}
    case Some{+v}:
      match k:
        case None{}:
          Rp.CBad{"unsupported kind"}
        case Some{+c}:
          rs_check.at(v, c, rs_first(rs_rules(v, c, id, cid, title, content, p, args)))

# R3: an edit's validation, its computed id given: no action, no kind,
# then the first of R3's rules it breaks; none: valid, with its action and
# kind
def rs_check(e: Rp.Ed, +cid: Maybe<&2, String>) -> Rp.Check:
  match e:
    case Rp.Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      rs_check.verb(verb, comp, id, cid, title, content, pyref, args)

# Example helpers
# ---------------

# an edit with an action, a kind, an id, a title and content, a reference
# and arguments, stored or not, held
def rp_ex(v: Rp.Verb, c: Rp.Comp, id: Maybe<&2, String>, p: Maybe<&2, Rp.Pyref>, a: Maybe<&2, Rp.Args>, stored: Bool) -> Rp.Ed:
  Rp.Ed{Some{v}, Some{c}, id, Some{"T"}, True{}, p, a, stored, False{}, True{}}

# Laws: the model
# ---------------

# LAW refine_plan_slug_words (R1): every title slugs to its words (runs of
# ASCII lowercase letters and digits after R1's lowercasing) joined by one
# `_` each, its first 80 chars; no word: the fallback
# EXCLUDES: a char kept that is not an ASCII lowercase letter or digit, an
#   uppercase letter not lowered, a run of cuts written as more than one
#   `_`, a `_` left at an end, another length cap, the fallback for a
#   title with a word
law refine_plan_slug_words:
  for +raw: String
  for +fb: String
  {Rp.slug(raw, fb) == rs_slug(raw, fb) : String}

# LAW refine_plan_ids_split (R2): the ids of edits xs then ys are the ids
# of xs then the ids of ys: each edit's id is its own, in order
# EXCLUDES: an edit lost, added or reordered, an id that depends on
#   another edit
law refine_plan_ids_split:
  for +xs: List<&2, Rp.Ed>
  for +ys: List<&2, Rp.Ed>
  {Rp.ids(List.append(&2, Rp.Ed, xs, ys)) == List.append(&2, Maybe<&2, String>, Rp.ids(xs), Rp.ids(ys)) : List<&2, Maybe<&2, String>>}

# LAW refine_plan_id_given (R2): an edit with an id x, whatever its action,
# kind and other facts, has the id x
# EXCLUDES: a slug over a given id, an id dropped for an update or delete
law refine_plan_id_given:
  for v: Maybe<&2, Rp.Verb>
  for c: Maybe<&2, Rp.Comp>
  for +x: String
  for t: Maybe<&2, String>
  for content: Bool
  for p: Maybe<&2, Rp.Pyref>
  for a: Maybe<&2, Rp.Args>
  for ex: Bool
  for df: Bool
  for hd: Bool
  {Rp.ids([Rp.Ed{v, c, Some{x}, t, content, p, a, ex, df, hd}]) == [Some{x}] : List<&2, Maybe<&2, String>>}

# LAW refine_plan_id_create (R2): a create without an id has the R1 slug
# (rs_slug, pinned by refine_plan_slug_words) of its title, else of its
# kind's name, with its kind's name the fallback (no kind: memory)
# EXCLUDES: a title slugged without the kind's name as its fallback, a
#   title-less create without an id, another default kind
law refine_plan_id_create:
  for +c: Maybe<&2, Rp.Comp>
  for +t: Maybe<&2, String>
  for content: Bool
  for p: Maybe<&2, Rp.Pyref>
  for a: Maybe<&2, Rp.Args>
  for ex: Bool
  for df: Bool
  for hd: Bool
  {Rp.ids([Rp.Ed{Some{Rp.ACreate{}}, c, None{}, t, content, p, a, ex, df, hd}]) == [Some{rs_slug(Maybe.default(&2, String, t, rs_kind_name(c)), rs_kind_name(c))}] : List<&2, Maybe<&2, String>>}

# LAW refine_plan_id_none (R2): an edit without an id that is not a create
# (no action, an update, a delete) has no id
# EXCLUDES: a slug for an update or delete, an id for an edit without an
#   action
law refine_plan_id_none:
  for +c: Maybe<&2, Rp.Comp>
  for +t: Maybe<&2, String>
  for +content: Bool
  for +p: Maybe<&2, Rp.Pyref>
  for +a: Maybe<&2, Rp.Args>
  for +ex: Bool
  for +df: Bool
  for +hd: Bool
  {[Rp.ids([Rp.Ed{None{}, c, None{}, t, content, p, a, ex, df, hd}]), Rp.ids([Rp.Ed{Some{Rp.AUpdate{}}, c, None{}, t, content, p, a, ex, df, hd}]), Rp.ids([Rp.Ed{Some{Rp.ADelete{}}, c, None{}, t, content, p, a, ex, df, hd}])] == [[None{}], [None{}], [None{}]] : List<&2, List<&2, Maybe<&2, String>>>}

# LAW refine_plan_check_rules (R3): every edit, its computed id given,
# validates to `unsupported action` without an action, `unsupported kind`
# without a kind, else to the message of the first of R3's rules it breaks
# (rs_rules, R3's list in order), else valid with its action and kind
# EXCLUDES: a rule skipped or checked in another order, a changed message,
#   a null spec key read as given, an update without arguments refused, a
#   delete held to a create's rules
law refine_plan_check_rules:
  for +e: Rp.Ed
  for +cid: Maybe<&2, String>
  {Rp.check(e, cid) == rs_check(e, cid) : Rp.Check}

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
# opt-in is off, a prompt note the session's memory does not hold, a
# subagent)
# EXCLUDES: a spec that drifts from the Rust it replaced
law refine_plan_plan_example:
  {Rp.plan(Rp.Opts{False{}, False{}}, [rp_ex(Rp.ACreate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ACreate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.AUpdate{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ADelete{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ADelete{}, Rp.KMemory{}, Some{"m"}, None{}, None{}, False{}), rp_ex(Rp.ACreate{}, Rp.KFactory{}, Some{"f"}, None{}, Some{Rp.Args{Rp.VMissing{}, Rp.VObject{}}}, False{}), rp_ex(Rp.ADelete{}, Rp.KFactory{}, Some{"g"}, None{}, None{}, True{}), Rp.Ed{Some{Rp.ACreate{}}, Some{Rp.KPrompt{}}, Some{"p"}, Some{"T"}, True{}, None{}, None{}, False{}, False{}, False{}}, rp_ex(Rp.ACreate{}, Rp.KSubagent{}, Some{"m"}, None{}, None{}, False{})]) == Rp.Plan{[Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "m", Rp.OWritten{}}, Rp.Row{Rp.ACreate{}, Rp.KMemory{}, "m", Rp.ORefused{"entry already exists"}}, Rp.Row{Rp.AUpdate{}, Rp.KMemory{}, "m", Rp.OWritten{}}, Rp.Row{Rp.ADelete{}, Rp.KMemory{}, "m", Rp.ORemoved{}}, Rp.Row{Rp.ADelete{}, Rp.KMemory{}, "m", Rp.ORefused{"entry not found"}}, Rp.Row{Rp.ACreate{}, Rp.KFactory{}, "f", Rp.ORefused{"the factory is disabled; run /factory on to enable it"}}, Rp.Row{Rp.ADelete{}, Rp.KFactory{}, "g", Rp.ORemoved{}}, Rp.Row{Rp.ACreate{}, Rp.KPrompt{}, "p", Rp.ORefused{"eukhe's memory is the chat: say it in your reply"}}, Rp.Row{Rp.ACreate{}, Rp.KSubagent{}, "m", Rp.OWritten{}}], ["create memory:m", "update memory:m", "delete memory:m", "delete factory:g", "create subagent:m"]} : Rp.Plan}

# LAW refine_plan_baseline_example (R4): anchor: with a baseline, an entry
# changed since planning refuses every edit of it; an invalid edit's row
# keeps its action and kind, a kind-less one is a memory create
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
