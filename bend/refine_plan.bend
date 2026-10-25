# refine_plan: the decisions of the /refine planner (Rust: eukhe-bend
# rules/refine_plan.rs; asked by eukhe-core refinement/planner.rs): the id
# an edit names (its slug), the validation of an edit with its messages,
# which edit of a proposal applies (the edits before it seen), the change
# lines of a result, the edits that roll a result back, the default texts
# of a proposal, whether a model reply was cut off mid-JSON, and the fit of
# a refinement request into the model's context window.
#
# Rust reads the JSON (serde) and gives the facts: per edit its action,
# kind, id, title, whether it has content, the string fields of its skill
# reference, the shape of its factory spec keys (missing, null, object,
# other), whether its entry is stored (the state before the proposal),
# whether that entry changed since the planning baseline, and whether the
# session's memory holds its kind. Rust keeps the state maps and mutates
# them as the plan says, builds the written entry, and stamps the clock.
# Pure: no IO, no @unsafe.

import Base

# An edit's action
type Verb is Data:
  ACreate{}
  AUpdate{}
  ADelete{}

# A continual harness component
type Comp is Data:
  KPrompt{}
  KMemory{}
  KSkill{}
  KSubagent{}
  KFactory{}

# A factory spec key's JSON value
type Val is Data:
  VMissing{}
  VNull{}
  VObject{}
  VOther{}

# The string fields of a skill reference: type, import, python_import,
# callable, call_pattern (none: absent or not a JSON string)
type Pyref is Data:
  Pyref{ty: Maybe<&2, String>, imp: Maybe<&2, String>, pyimp: Maybe<&2, String>, call: Maybe<&2, String>, pat: Maybe<&2, String>}

# The factory spec keys of an edit's arguments
type Args is Data:
  Args{dag: Val, machine: Val}

# One proposed edit and the facts of its entry
type Ed is Data:
  Ed{verb: Maybe<&2, Verb>, comp: Maybe<&2, Comp>, id: Maybe<&2, String>, title: Maybe<&2, String>, content: Bool, pyref: Maybe<&2, Pyref>, args: Maybe<&2, Args>, exists: Bool, differs: Bool, held: Bool}

# An edit's validation: its message, or its action and kind
type Check is Data:
  CBad{msg: String}
  COk{verb: Verb, comp: Comp}

# The options of an apply: the factory opt-in, a planning baseline given
type Opts is Data:
  Opts{factory: Bool, baseline: Bool}

# An entry an earlier edit of the proposal wrote (present) or removed
type Touch is Data:
  Touch{comp: Comp, id: String, present: Bool}

# What an edit does: refused before the state is read (invalid), refused
# with the stored entry shown, the entry removed, the entry written
type Out is Data:
  OInvalid{msg: String}
  ORefused{msg: String}
  ORemoved{}
  OWritten{}

# One edit's row of the result
type Row is Data:
  Row{verb: Verb, comp: Comp, id: String, out: Out}

# A proposal's rows and change lines
type Plan is Data:
  Plan{rows: List<&2, Row>, changes: List<&2, String>}

# A row of the result rolled back: applied, with a before, with an after
type Was is Data:
  Was{applied: Bool, before: Bool, after: Bool}

# A rollback edit: the row it reverts and its action
type Pick is Data:
  Pick{at: Nat, verb: Verb}

# A rollback proposal
type Back is Data:
  Back{summary: String, rationale: String, outcome: String, reason: String, picks: List<&2, Pick>}

# A proposal's texts
type Texts is Data:
  Texts{summary: String, rationale: String, outcome: String}

# The JSON truncation scan: in a string, after a backslash in it, the
# opening and closing brackets seen
type Scan is Data:
  Scan{ins: Bool, esc: Bool, opens: Nat, closes: Nat}

# A model's window: context window, max output tokens, output reserve,
# system prompt length
type Win is Data:
  Win{window: Nat, max: Nat, reserve: Nat, system: Nat}

# Where the fit search is: the full prompt measured, a trimmed one
# measured (the bounds and its length), the final prompt measured
type Search is Data:
  SFull{}
  SProbe{low: Nat, high: Nat, len: Nat}
  SFinal{}

# The fit's next step: measure the prompt of a conversation tail, the
# output tokens, no room
type Step is Data:
  TTry{len: Nat, next: Search}
  TOk{max: Nat}
  TNo{text: String}

# Names
# -----

def verb_name(v: Verb) -> String:
  match v:
    case ACreate{}:
      "create"
    case AUpdate{}:
      "update"
    case ADelete{}:
      "delete"

def comp_name(c: Comp) -> String:
  match c:
    case KPrompt{}:
      "prompt"
    case KMemory{}:
      "memory"
    case KSkill{}:
      "skill"
    case KSubagent{}:
      "subagent"
    case KFactory{}:
      "factory"

def comp_eq(a: Comp, b: Comp) -> Bool:
  String.eq(comp_name(a), comp_name(b))

# Slug
# ----

def slug.put.at(alnum: Bool, upper: Bool, dotted: Bool, kelvin: Bool, +c: Char, +r: String) -> String:
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
def slug.marks(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      slug.put.at(Bool.or(Char.is_lower(c), Char.is_digit(c)), Char.is_upper(c), U32.is_eq(Char.to_u32(c), 304), U32.is_eq(Char.to_u32(c), 8490), c, slug.marks(t))

def slug.squeeze.at(dup: Bool, c: Char, r: String) -> String:
  match dup:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# every run of `_` one `_`
def slug.squeeze(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      slug.squeeze.at(Bool.and(Char.is_eq(c, '_'), String.starts_with(t, "_")), c, slug.squeeze(t))

def slug.lead.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `_`s
def slug.lead(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      slug.lead.at(Char.is_eq(c, '_'), c, t, slug.lead(t))

def slug.pick(e: Bool, s: String, fb: String) -> String:
  match e:
    case True{}:
      fb
    case False{}:
      s

# the slug of a title: marked, squeezed, `_` trimmed at both ends, its
# first 80 chars; the fallback when empty
def slug(raw: String, fb: String) -> String:
  +t = String.take(String.reverse(slug.lead(String.reverse(slug.lead(slug.squeeze(slug.marks(raw)))))), 80n)
  slug.pick(String.is_empty(t), t, fb)

# Ids
# ---

def is_create(m: Maybe<&2, Verb>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      match v:
        case ACreate{}:
          True{}
        case AUpdate{}:
          False{}
        case ADelete{}:
          False{}

def comp_or_memory(m: Maybe<&2, Comp>) -> Comp:
  match m:
    case None{}:
      KMemory{}
    case Some{c}:
      c

def computed.at(create: Bool, title: Maybe<&2, String>, +name: String) -> Maybe<&2, String>:
  match create:
    case True{}:
      Some{slug(Maybe.default(&2, String, title, name), name)}
    case False{}:
      None{}

# the id an edit names: its id, else a create's slug of its title (none:
# its kind's name), the kind's name the fallback (no kind: memory)
def computed(e: Ed) -> Maybe<&2, String>:
  match e:
    case Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      Maybe.or(&2, String, id, computed.at(is_create(verb), title, comp_name(comp_or_memory(comp))))

# the id of every edit
def ids(eds: List<&2, Ed>) -> List<&2, Maybe<&2, String>>:
  match eds:
    case Nil{}:
      Nil{}
    case e <> t:
      computed(e) <> ids(t)

# Validation
# ----------

def first(b: Bool, msg: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{msg}
    case False{}:
      r

def is_text(m: Maybe<&2, String>, x: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      String.eq(y, x)

def filled(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      Bool.not(String.is_empty(y))

def is_comp(c: Comp, d: Comp) -> Bool:
  comp_eq(c, d)

def is_verb(v: Verb, w: Verb) -> Bool:
  String.eq(verb_name(v), verb_name(w))

def skill.fields(+vn: String, r: Pyref) -> Maybe<&2, String>:
  match r:
    case Pyref{ty, imp, pyimp, call, pat}:
      first(Bool.not(is_text(ty, "python")), String.concat([vn, " skill reference.type must be python"]), first(Bool.not(Bool.or(filled(imp), filled(pyimp))), String.concat([vn, " skill requires python import"]), first(Bool.not(Bool.or(filled(call), filled(pat))), String.concat([vn, " skill requires callable or call_pattern"]), None{})))

def skill.ref(+vn: String, m: Maybe<&2, Pyref>) -> Maybe<&2, String>:
  match m:
    case None{}:
      Some{String.concat([vn, " skill requires python reference"])}
    case Some{r}:
      skill.fields(vn, r)

# a skill create or update: arguments, a python reference with an import
# and a callable
def skill(+vn: String, args: Maybe<&2, Args>, m: Maybe<&2, Pyref>) -> Maybe<&2, String>:
  first(Maybe.is_none(&2, Args, args), String.concat([vn, " skill requires arguments"]), skill.ref(vn, m))

def present(v: Val) -> Bool:
  match v:
    case VMissing{}:
      False{}
    case VNull{}:
      False{}
    case VObject{}:
      True{}
    case VOther{}:
      True{}

def is_object(v: Val) -> Bool:
  match v:
    case VMissing{}:
      False{}
    case VNull{}:
      False{}
    case VObject{}:
      True{}
    case VOther{}:
      False{}

def spec_object(m: Bool, dag: Val, machine: Val) -> Bool:
  match m:
    case True{}:
      is_object(machine)
    case False{}:
      is_object(dag)

def factory.keys(+dag: Val, +machine: Val) -> Maybe<&2, String>:
  first(Bool.and(present(dag), present(machine)), "pass either dag or machine form, not both", first(Bool.not(spec_object(present(machine), dag, machine)), "factory entry requires a dag or machine object in arguments", None{}))

# a factory create, or an update with arguments: one spec form, an object
def factory(args: Maybe<&2, Args>) -> Maybe<&2, String>:
  match args:
    case None{}:
      factory.keys(VMissing{}, VMissing{})
    case Some{a}:
      match a:
        case Args{dag, machine}:
          factory.keys(dag, machine)

def when(b: Bool, m: Maybe<&2, String>, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      m
    case False{}:
      r

# the first rule an action and kind break, in Rust's order
def rules(+v: Verb, +c: Comp, +id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, m: Maybe<&2, Pyref>, +args: Maybe<&2, Args>) -> Maybe<&2, String>:
  +vn = verb_name(v)
  +edit = Bool.not(is_verb(v, ADelete{}))
  first(Bool.and(is_comp(c, KPrompt{}), Bool.or(is_text(id, "base_system_prompt"), is_text(cid, "base_system_prompt"))), "base system prompt is not editable", first(Bool.and(Bool.not(is_verb(v, ACreate{})), Maybe.is_none(&2, String, id)), String.concat([vn, " requires id"]), first(Bool.and(edit, Bool.not(Bool.and(titled, content))), String.concat([vn, " requires title and content"]), when(Bool.and(edit, is_comp(c, KSkill{})), skill(vn, args, m), when(Bool.and(edit, Bool.and(is_comp(c, KFactory{}), Bool.or(is_verb(v, ACreate{}), Maybe.is_some(&2, Args, args)))), factory(args), None{})))))

def check.at(+v: Verb, +c: Comp, r: Maybe<&2, String>) -> Check:
  match r:
    case None{}:
      COk{v, c}
    case Some{msg}:
      CBad{msg}

def check.comp(+v: Verb, m: Maybe<&2, Comp>, +id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, p: Maybe<&2, Pyref>, args: Maybe<&2, Args>) -> Check:
  match m:
    case None{}:
      CBad{"unsupported kind"}
    case Some{+c}:
      check.at(v, c, rules(v, c, id, cid, titled, content, p, args))

def check.verb(m: Maybe<&2, Verb>, k: Maybe<&2, Comp>, id: Maybe<&2, String>, cid: Maybe<&2, String>, titled: Bool, content: Bool, p: Maybe<&2, Pyref>, args: Maybe<&2, Args>) -> Check:
  match m:
    case None{}:
      CBad{"unsupported action"}
    case Some{v}:
      check.comp(v, k, id, cid, titled, content, p, args)

# an edit's validation, its computed id given (TS-mirrored messages)
def check(e: Ed, cid: Maybe<&2, String>) -> Check:
  match e:
    case Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      check.verb(verb, comp, id, cid, Maybe.is_some(&2, String, title), content, pyref, args)

# Plan
# ----

def lookup.at(hit: Bool, p: Bool, r: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      r

def lookup.touch(t: Touch, +c: Comp, +id: String, r: Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match t:
    case Touch{tc, tid, p}:
      lookup.at(Bool.and(comp_eq(tc, c), String.eq(tid, id)), p, r)

# whether the latest earlier edit of the entry left it present (none: no
# earlier edit wrote or removed it)
def lookup(ts: List<&2, Touch>, +c: Comp, +id: String) -> Maybe<&2, Bool>:
  match ts:
    case Nil{}:
      None{}
    case t <> rest:
      lookup.touch(t, c, id, lookup(rest, c, id))

def out.first(b: Bool, msg: String, r: Out) -> Out:
  match b:
    case True{}:
      ORefused{msg}
    case False{}:
      r

def out.final(v: Verb, +p: Bool) -> Out:
  match v:
    case ACreate{}:
      match p:
        case True{}:
          ORefused{"entry already exists"}
        case False{}:
          OWritten{}
    case AUpdate{}:
      match p:
        case True{}:
          OWritten{}
        case False{}:
          ORefused{"entry not found"}
    case ADelete{}:
      match p:
        case True{}:
          ORemoved{}
        case False{}:
          ORefused{"entry not found"}

# a valid edit's outcome: a baseline change, the factory opt-in, the
# session's memory, then the entry's presence
def decide(o: Opts, e: Ed, +v: Verb, +c: Comp, +look: Maybe<&2, Bool>) -> Out:
  match o:
    case Opts{factory, baseline}:
      match e:
        case Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
          out.first(Bool.and(baseline, Bool.and(Maybe.is_none(&2, Bool, look), differs)), "entry changed during refinement planning", out.first(Bool.and(is_comp(c, KFactory{}), Bool.and(Bool.not(is_verb(v, ADelete{})), Bool.not(factory))), "the factory is disabled; run /factory on to enable it", out.first(Bool.not(held), "eukhe's memory is the chat: say it in your reply", out.final(v, Maybe.default(&2, Bool, look, exists)))))

def invalid_verb.at(comp: Maybe<&2, Comp>, verb: Maybe<&2, Verb>) -> Verb:
  match comp:
    case None{}:
      ACreate{}
    case Some{c}:
      match verb:
        case None{}:
          ACreate{}
        case Some{v}:
          v

# an invalid edit's action: create without a kind, else its action (none:
# create)
def invalid_verb(e: Ed) -> Verb:
  match e:
    case Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      invalid_verb.at(comp, verb)

def comp_of(e: Ed) -> Comp:
  match e:
    case Ed{verb, comp, id, title, content, pyref, args, exists, differs, held}:
      comp_or_memory(comp)

def row.at(+o: Opts, +e: Ed, +ts: List<&2, Touch>, +id: String, k: Check) -> Row:
  match k:
    case CBad{msg}:
      Row{invalid_verb(e), comp_of(e), id, OInvalid{msg}}
    case COk{+v, +c}:
      Row{v, c, id, decide(o, e, v, c, lookup(ts, c, id))}

# an edit's row, the earlier edits' writes and removals given
def row(+o: Opts, +e: Ed, +ts: List<&2, Touch>) -> Row:
  row.at(o, e, ts, Maybe.default(&2, String, computed(e), ""), check(e, computed(e)))

def touch.out(x: Out, +c: Comp, +id: String, ts: List<&2, Touch>) -> List<&2, Touch>:
  match x:
    case OInvalid{m}:
      ts
    case ORefused{m}:
      ts
    case ORemoved{}:
      Touch{c, id, False{}} <> ts
    case OWritten{}:
      Touch{c, id, True{}} <> ts

# the writes and removals after a row
def touch(r: Row, ts: List<&2, Touch>) -> List<&2, Touch>:
  match r:
    case Row{v, c, id, x}:
      touch.out(x, c, id, ts)

def plan.rows(+o: Opts, eds: List<&2, Ed>, +ts: List<&2, Touch>) -> List<&2, Row>:
  match eds:
    case Nil{}:
      Nil{}
    case +e <> t:
      row(o, e, ts) <> plan.rows(o, t, touch(row(o, e, ts), ts))

def change.out(x: Out, v: Verb, c: Comp, id: String, r: List<&2, String>) -> List<&2, String>:
  match x:
    case OInvalid{m}:
      r
    case ORefused{m}:
      r
    case ORemoved{}:
      String.concat([verb_name(v), " ", comp_name(c), ":", id]) <> r
    case OWritten{}:
      String.concat([verb_name(v), " ", comp_name(c), ":", id]) <> r

def change(w: Row, r: List<&2, String>) -> List<&2, String>:
  match w:
    case Row{v, c, id, x}:
      change.out(x, v, c, id, r)

# the change line of every applied row: `<action> <kind>:<id>`
def changes(rows: List<&2, Row>) -> List<&2, String>:
  match rows:
    case Nil{}:
      Nil{}
    case w <> t:
      change(w, changes(t))

# a proposal's rows and change lines
def plan(+o: Opts, eds: List<&2, Ed>) -> Plan:
  +rows = plan.rows(o, eds, [])
  Plan{rows, changes(rows)}

# Rollback
# --------

def back.restore(after: Bool) -> Verb:
  match after:
    case True{}:
      AUpdate{}
    case False{}:
      ACreate{}

def back.pick.at(applied: Bool, before: Bool, +after: Bool, at: Nat) -> List<&2, Pick>:
  match applied:
    case False{}:
      []
    case True{}:
      match before:
        case True{}:
          [Pick{at, back.restore(after)}]
        case False{}:
          match after:
            case True{}:
              [Pick{at, ADelete{}}]
            case False{}:
              []

def back.pick(w: Was, at: Nat) -> List<&2, Pick>:
  match w:
    case Was{applied, before, after}:
      back.pick.at(applied, before, after, at)

def back.fwd(was: List<&2, Was>, +at: Nat) -> List<&2, Pick>:
  match was:
    case Nil{}:
      Nil{}
    case w <> t:
      List.append(&2, Pick, back.pick(w, at), back.fwd(t, 1n+at))

# the rollback of a result: its applied rows last first, a stored before
# restored (updated when the row wrote an after, else created), a written
# entry without a before deleted
def back(+id: String, was: List<&2, Was>) -> Back:
  Back{String.concat(["Rollback refinement ", id]), String.concat(["Restores continual harness state snapshots from refinement ", id, "."]), "Faulty refinement edits are reverted.", String.concat(["Rollback ", id]), List.reverse(&2, Pick, back.fwd(was, 0n))}

# Texts
# -----

# a proposal's texts: each string given, else its default
def norm(s: Maybe<&2, String>, r: Maybe<&2, String>, o: Maybe<&2, String>) -> Texts:
  Texts{Maybe.default(&2, String, s, "Refined continual harness state"), Maybe.default(&2, String, r, ""), Maybe.default(&2, String, o, "")}

# Truncation
# ----------

def scan.code(+c: Char, x: U32) -> Bool:
  U32.is_eq(Char.to_u32(c), x)

def scan.out(ins: Bool, +bs: Bool, +q: Bool, op: Bool, cl: Bool, +o: Nat, +k: Nat) -> Scan:
  match ins:
    case True{}:
      match bs:
        case True{}:
          Scan{True{}, True{}, o, k}
        case False{}:
          match q:
            case True{}:
              Scan{False{}, False{}, o, k}
            case False{}:
              Scan{True{}, False{}, o, k}
    case False{}:
      match q:
        case True{}:
          Scan{True{}, False{}, o, k}
        case False{}:
          match op:
            case True{}:
              Scan{False{}, False{}, 1n+o, k}
            case False{}:
              match cl:
                case True{}:
                  Scan{False{}, False{}, o, 1n+k}
                case False{}:
                  Scan{False{}, False{}, o, k}

def scan.at(esc: Bool, +ins: Bool, +c: Char, +o: Nat, +k: Nat) -> Scan:
  match esc:
    case True{}:
      Scan{ins, False{}, o, k}
    case False{}:
      scan.out(ins, scan.code(c, 92), scan.code(c, 34), Bool.or(scan.code(c, 123), scan.code(c, 91)), Bool.or(scan.code(c, 125), scan.code(c, 93)), o, k)

# the scan after a char
def scan.step(st: Scan, +c: Char) -> Scan:
  match st:
    case Scan{ins, esc, o, k}:
      scan.at(esc, ins, c, o, k)

def scan(s: String, st: Scan) -> Scan:
  match s:
    case SNil{}:
      st
    case SCon{+c, t}:
      scan(t, scan.step(st, c))

def scan.done(st: Scan) -> Bool:
  match st:
    case Scan{ins, esc, o, k}:
      Bool.or(ins, Nat.is_gt(o, k))

# whether a JSON candidate ends mid-value: in a string, or more brackets
# opened than closed (outside strings; a backslash escapes the next char)
def incomplete(text: String) -> Bool:
  scan.done(scan(text, Scan{False{}, False{}, 0n, 0n}))

# Fit
# ---

def fit.room.at(z: Bool, m: Nat) -> Step:
  match z:
    case True{}:
      TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."}
    case False{}:
      TOk{m}

def fit.room(+m: Nat) -> Step:
  fit.room.at(Nat.is_eq(m, 0n), m)

def fit.probe.at(b: Bool, +low: Nat, +high: Nat) -> Step:
  match b:
    case True{}:
      +mid = Nat.div(Nat.add(Nat.add(low, high), 1n), 2n)
      TTry{mid, SProbe{low, high, mid}}
    case False{}:
      TTry{low, SFinal{}}

# the next length the binary search measures, or the final one
def fit.probe(+low: Nat, +high: Nat) -> Step:
  fit.probe.at(Nat.is_lt(low, high), low, high)

def fit.full(trim: Bool, conv: Nat, r: Step) -> Step:
  match trim:
    case True{}:
      fit.probe(0n, conv)
    case False{}:
      r

def fit.narrow(fits: Bool, low: Nat, +high: Nat, +len: Nat) -> Step:
  match fits:
    case True{}:
      fit.probe(len, high)
    case False{}:
      fit.probe(low, Nat.sub(len, 1n))

def fit.at(st: Search, +conv: Nat, +plen: Nat, +sysr: Nat, +budget: Nat, +mx: Nat, +cw: Nat) -> Step:
  match st:
    case SFull{}:
      fit.full(Bool.and(Bool.not(Nat.is_le(Nat.add(sysr, plen), budget)), Bool.not(Nat.is_eq(conv, 0n))), conv, fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen)))))
    case SProbe{low, high, len}:
      fit.narrow(Nat.is_le(Nat.add(sysr, plen), budget), low, high, len)
    case SFinal{}:
      fit.room(Nat.min(mx, Nat.sub(cw, Nat.add(sysr, plen))))

# the fit of a refinement request: the window, the conversation's length,
# where the search is and the length of the prompt it measured (lengths in
# UTF-8 bytes, one token each)
def fit(w: Win, conv: Nat, st: Search, plen: Nat) -> Step:
  match w:
    case Win{+cw, +mx, res, sys}:
      fit.at(st, conv, plen, Nat.add(sys, 1024n), Nat.sub(cw, Nat.min(Nat.min(mx, res), Nat.div(cw, 2n))), mx, cw)
