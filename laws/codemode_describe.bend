# eukhe: the laws of area codemode_describe

import Base
import ../bend/codemode_describe.bend as Dsc
import ../bend/ffi_codemode_describe.bend as FDsc
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# LAWS (R1-R6): the code mode tool's description and its `codemode` system
# prompt section (bend/codemode_describe.bend, the port of eukhe-durable
# codemode/describe.rs `namespace_of`, `select_catalog`, `codemode_section`
# and `codemode_description`). Each law is an open claim about
# Dsc.space_of, Dsc.select, Dsc.section or Dsc.description; PROOF.bend
# proves them (as CodemodeDescribe.<law>) with the lemmas of
# proof/codemode_describe/.
#
# The host gives each tool as its name and the UTF-16 length of its
# rendered section (heading, description and declaration, rendered by the
# host), each namespace as its name, its name in lowercase (Rust
# `to_lowercase`), its prefix and its description trimmed ("" when none),
# and the budget in tokens.
#
# R1: a tool's namespace is the one with the longest prefix its name starts
#     with (by length; of two prefixes of one name the longer in chars is
#     the longer in UTF-16 units), the first of equally long ones; none when
#     no prefix fits.
# R2: the tools form groups: the tools of no namespace, then one group per
#     namespace name in the order its first tool comes (namespaces of one
#     name are one group, with the first such tool's namespace); each group
#     keeps its tools in tool order.
# R3: after the tools of no namespace, the namespace groups go by name:
#     lowercase names compared first, then the names themselves in reverse
#     (so lowercase before uppercase); groups of equal order keep theirs.
# R4: a tool costs its section's UTF-16 length divided by 4, rounded up.
#     The tools shown fit the budget: each group's queue is its tools by
#     cost (ties in tool order); in each round, every group still in, in
#     group order, places the head of its queue when its cost is at most the
#     budget left (which falls by that cost) and stays in while its queue
#     has tools; a group whose head does not fit drops out at once. Rounds
#     go on while a group is in (at most one more than the tools). A tool is
#     shown when a tool of its name was placed.
# R5: the section (none without tools) is, joined by blank lines ("\n\n"):
#     "Tools scripts can call (`await tools.<name>(args)`):"; for the tools
#     of no namespace, when there are any, "Some tools are not listed: find
#     them with `searchTools()`." when not all are shown, then their shown
#     sections in tool order; for each namespace group, "## <name>" then "
#     (tools not listed)" when none of its tools is shown, " (some tools not
#     listed)" when some are not, then "\n<description>" when it has one,
#     then its shown sections in tool order.
# R6: the description is the intro, the globals, the `models` section when
#     scripts get the models globals (with the default classifier's line
#     when the session resolves one), and the line saying where the tools
#     are listed, joined by blank lines (the models section and the
#     classifier's line by one newline); every text is restated below.

# Terms
# -----

def hit_one(on: Bool, +i: Nat, +n: Nat, rest: List<&2, Dsc.Hit>) -> List<&2, Dsc.Hit>:
  match on:
    case True{}:
      Dsc.Hit{i, n} <> rest
    case False{}:
      rest

# R1: the prefixes of ps (from index i) that name starts with, each with its
# index and length, in order
def hits_spec(ps: List<&2, String>, +name: String, +i: Nat) -> List<&2, Dsc.Hit>:
  match ps:
    case Nil{}:
      []
    case Con{+p, r}:
      hit_one(String.starts_with(name, p), i, String.length(p), hits_spec(r, name, 1n+i))

def longer_of(later: Bool, x: Dsc.Hit, y: Dsc.Hit) -> Dsc.Hit:
  match later:
    case True{}:
      y
    case False{}:
      x

def longest_first(x: Dsc.Hit, best: Maybe<&2, Dsc.Hit>) -> Dsc.Hit:
  match x:
    case Dsc.Hit{i, +n}:
      match best:
        case None{}:
          Dsc.Hit{i, n}
        case Some{y}:
          match y:
            case Dsc.Hit{j, +m}:
              longer_of(Nat.is_lt(n, m), Dsc.Hit{i, n}, Dsc.Hit{j, m})

# R1: the first of the longest
def longest_spec(hs: List<&2, Dsc.Hit>) -> Maybe<&2, Dsc.Hit>:
  match hs:
    case Nil{}:
      None{}
    case Con{h, r}:
      Some{longest_first(h, longest_spec(r))}

def hit_index(m: Maybe<&2, Dsc.Hit>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{h}:
      match h:
        case Dsc.Hit{i, n}:
          Some{i}

# R1: the namespace of the tool named name among the prefixes ps
def space_spec(+name: String, ps: List<&2, String>) -> Maybe<&2, Nat>:
  hit_index(longest_spec(hits_spec(ps, name, 0n)))

# R4: a tool's cost
def cost_spec(size: Nat) -> Nat:
  Nat.div(Nat.add(size, 3n), 4n)

def item_cost(x: Dsc.Item) -> Nat:
  match x:
    case Dsc.Item{t, c}:
      c

def item_tool(x: Dsc.Item) -> Nat:
  match x:
    case Dsc.Item{t, c}:
      t

def by_cost_at(first: Bool, x: Dsc.Item, h: Dsc.Item, t: List<&2, Dsc.Item>, later: List<&2, Dsc.Item>) -> List<&2, Dsc.Item>:
  match first:
    case True{}:
      x <> h <> t
    case False{}:
      h <> later

def by_cost_put(+x: Dsc.Item, xs: List<&2, Dsc.Item>) -> List<&2, Dsc.Item>:
  match xs:
    case Nil{}:
      [x]
    case Con{+h, +t}:
      by_cost_at(Nat.is_le(item_cost(x), item_cost(h)), x, h, t, by_cost_put(x, t))

# R4: a group's queue: its tools by cost, ties in tool order
def by_cost(xs: List<&2, Dsc.Item>) -> List<&2, Dsc.Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      by_cost_put(x, by_cost(r))

# R4: a group in the rounds: still in or out, and its queue left
type Live is Data:
  Live{on: Bool, queue: List<&2, Dsc.Item>}

# R4: after a round: the groups, the budget left, the tools placed, and
# whether a group is still in
type Turn is Data:
  Turn{groups: List<&2, Live>, left: Nat, placed: List<&2, Nat>, any: Bool}

def is_cons(xs: List<&2, Dsc.Item>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

# the first group's head fits the budget left (whether it is in or not)
def head_fits(fs: List<&2, Live>, +rem: Nat) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, r}:
      match f:
        case Live{on, q}:
          match q:
            case Nil{}:
              False{}
            case Con{x, t}:
              Nat.is_le(item_cost(x), rem)

# a group out, before the groups of round t
def out_before(q: List<&2, Dsc.Item>, t: Turn) -> Turn:
  match t:
    case Turn{fs, left, placed, any}:
      Turn{Live{False{}, q} <> fs, left, placed, any}

# a group that placed tool x and has rest left, before round t
def placed_before(+rest: List<&2, Dsc.Item>, x: Nat, t: Turn) -> Turn:
  match t:
    case Turn{fs, left, placed, any}:
      Turn{Live{is_cons(rest), rest} <> fs, left, x <> placed, Bool.or(is_cons(rest), any)}

# R4: one round over the groups fs (ok: the first group's head fits): a
# group out stays out; a group in places its head when it fits (the budget
# falls by its cost) and stays in while tools are left, else it drops out
def turn(fs: List<&2, Live>, ok: Bool, +rem: Nat) -> Turn:
  match fs:
    case Nil{}:
      Turn{[], rem, [], False{}}
    case Con{f, +r}:
      match f:
        case Live{on, q}:
          match on:
            case False{}:
              out_before(q, turn(r, head_fits(r, rem), rem))
            case True{}:
              match q:
                case Nil{}:
                  out_before([], turn(r, head_fits(r, rem), rem))
                case Con{+x, rest}:
                  match ok:
                    case True{}:
                      +rem2 = Nat.sub(rem, item_cost(x))
                      placed_before(rest, item_tool(x), turn(r, head_fits(r, rem2), rem2))
                    case False{}:
                      out_before(Con{x, rest}, turn(r, head_fits(r, rem), rem))

# R4: the tools placed in the rounds after round t, with fuel
def turns(fuel: Nat, t: Turn) -> List<&2, Nat>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match t:
        case Turn{+fs, +left, placed, any}:
          match any:
            case False{}:
              placed
            case True{}:
              List.append(&2, Nat, placed, turns(f, turn(fs, head_fits(fs, left), left)))

def lives(gs: List<&2, List<&2, Dsc.Item>>) -> List<&2, Live>:
  match gs:
    case Nil{}:
      []
    case Con{+g, r}:
      Live{is_cons(g), by_cost(g)} <> lives(r)

def any_on(fs: List<&2, Live>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{f, r}:
      match f:
        case Live{on, q}:
          Bool.or(on, any_on(r))

def count(gs: List<&2, List<&2, Dsc.Item>>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, r}:
      Nat.add(List.length(&2, Dsc.Item, g), count(r))

# R4: the tools placed for the groups gs under the budget
def select_spec(+gs: List<&2, List<&2, Dsc.Item>>, budget: Nat) -> List<&2, Nat>:
  +fs = lives(gs)
  turns(1n+count(gs), Turn{fs, budget, [], any_on(fs)})

def space_at(ss: List<&2, Dsc.Space>, n: Nat) -> Maybe<&2, Dsc.Space>:
  match ss:
    case Nil{}:
      None{}
    case Con{s, r}:
      match n:
        case 0n:
          Some{s}
        case 1n+k:
          space_at(r, k)

def prefixes_spec(ss: List<&2, Dsc.Space>) -> List<&2, String>:
  match ss:
    case Nil{}:
      []
    case Con{s, r}:
      match s:
        case Dsc.Space{n, k, p, a}:
          p <> prefixes_spec(r)

def space_found(m: Maybe<&2, Nat>, ss: List<&2, Dsc.Space>) -> Maybe<&2, Dsc.Space>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      space_at(ss, j)

# R1, R4: each tool (from index i) with its namespace and its cost
def tags_spec(ts: List<&2, Dsc.Tool>, +ss: List<&2, Dsc.Space>, +ps: List<&2, String>, +i: Nat) -> List<&2, Dsc.Tagged>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      match t:
        case Dsc.Tool{n, z}:
          Dsc.Tagged{space_found(space_spec(n, ps), ss), Dsc.Item{i, cost_spec(z)}} <> tags_spec(r, ss, ps, 1n+i)

def space_name(s: Dsc.Space) -> String:
  match s:
    case Dsc.Space{n, k, p, a}:
      n

def space_key(s: Dsc.Space) -> String:
  match s:
    case Dsc.Space{n, k, p, a}:
      k

def join_at(same: Bool, g: Dsc.Grp, x: Dsc.Item, r: List<&2, Dsc.Grp>, other: List<&2, Dsc.Grp>) -> List<&2, Dsc.Grp>:
  match same:
    case True{}:
      match g:
        case Dsc.Grp{s, its}:
          Dsc.Grp{s, List.append(&2, Dsc.Item, its, [x])} <> r
    case False{}:
      g <> other

def grp_named(g: Dsc.Grp, +s: Dsc.Space) -> Bool:
  match g:
    case Dsc.Grp{s2, its}:
      String.eq(space_name(s2), space_name(s))

# R2: x joins the group of namespace s's name, else a new last group
def join_spec(gs: List<&2, Dsc.Grp>, +s: Dsc.Space, +x: Dsc.Item) -> List<&2, Dsc.Grp>:
  match gs:
    case Nil{}:
      [Dsc.Grp{s, [x]}]
    case Con{+g, +r}:
      join_at(grp_named(g, s), g, x, r, join_spec(r, s, x))

def place_spec(m: Maybe<&2, Dsc.Space>, plain: List<&2, Dsc.Item>, named: List<&2, Dsc.Grp>, x: Dsc.Item) -> List<&2, Dsc.Item> & List<&2, Dsc.Grp>:
  match m:
    case None{}:
      (List.append(&2, Dsc.Item, plain, [x]), named)
    case Some{s}:
      (plain, join_spec(named, s, x))

def place_tag(acc: List<&2, Dsc.Item> & List<&2, Dsc.Grp>, x: Dsc.Tagged) -> List<&2, Dsc.Item> & List<&2, Dsc.Grp>:
  match acc:
    case (plain, named):
      match x:
        case Dsc.Tagged{m, it}:
          place_spec(m, plain, named, it)

# R2: the tools of no namespace, and the namespace groups in the order of
# their first tool
def groups_spec(xs: List<&2, Dsc.Tagged>, acc: List<&2, Dsc.Item> & List<&2, Dsc.Grp>) -> List<&2, Dsc.Item> & List<&2, Dsc.Grp>:
  match xs:
    case Nil{}:
      acc
    case Con{x, r}:
      groups_spec(r, place_tag(acc, x))

def first_tie(same: Bool, +a: Dsc.Space, +b: Dsc.Space) -> Bool:
  match same:
    case True{}:
      String.is_lt(space_name(b), space_name(a))
    case False{}:
      String.is_lt(space_key(a), space_key(b))

# R3: namespace a goes before namespace b
def first_spec(+a: Dsc.Space, +b: Dsc.Space) -> Bool:
  first_tie(String.eq(space_key(a), space_key(b)), a, b)

def grp_of(g: Dsc.Grp) -> Dsc.Space:
  match g:
    case Dsc.Grp{s, its}:
      s

def sorted_at(stays: Bool, g: Dsc.Grp, h: Dsc.Grp, t: List<&2, Dsc.Grp>, later: List<&2, Dsc.Grp>) -> List<&2, Dsc.Grp>:
  match stays:
    case True{}:
      g <> h <> t
    case False{}:
      h <> later

def sorted_put(+g: Dsc.Grp, gs: List<&2, Dsc.Grp>) -> List<&2, Dsc.Grp>:
  match gs:
    case Nil{}:
      [g]
    case Con{+h, +t}:
      sorted_at(Bool.not(first_spec(grp_of(h), grp_of(g))), g, h, t, sorted_put(g, t))

# R3: the groups in namespace order, groups of equal order keeping theirs
def sorted_spec(gs: List<&2, Dsc.Grp>) -> List<&2, Dsc.Grp>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      sorted_put(g, sorted_spec(r))

def tool_name_spec(ts: List<&2, Dsc.Tool>, n: Nat) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, r}:
      match t:
        case Dsc.Tool{name, z}:
          match n:
            case 0n:
              name
            case 1n+k:
              tool_name_spec(r, k)

def names_spec(+ts: List<&2, Dsc.Tool>, xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      tool_name_spec(ts, x) <> names_spec(ts, r)

def has_name(ns: List<&2, String>, +n: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.or(String.eq(x, n), has_name(r, n))

def shown_at(on: Bool, x: Dsc.Item, rest: List<&2, Dsc.Item>) -> List<&2, Dsc.Item>:
  match on:
    case True{}:
      x <> rest
    case False{}:
      rest

# R4: the tools of xs shown: a tool of the name of each was placed
def shown_spec(xs: List<&2, Dsc.Item>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> List<&2, Dsc.Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      match x:
        case Dsc.Item{+t, c}:
          shown_at(has_name(shown, tool_name_spec(ts, t)), Dsc.Item{t, c}, shown_spec(r, ts, shown))

def sects_spec(xs: List<&2, Dsc.Item>) -> List<&2, Dsc.Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      match x:
        case Dsc.Item{t, c}:
          Dsc.Sect{t} <> sects_spec(r)

def marker_at(all: Bool, none: Bool) -> String:
  match all:
    case True{}:
      ""
    case False{}:
      match none:
        case True{}:
          " (tools not listed)"
        case False{}:
          " (some tools not listed)"

def about_at(empty: Bool, about: String) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      String.append("\n", about)

# R5: a namespace's heading for v of its n tools shown
def heading_spec(s: Dsc.Space, +v: Nat, +n: Nat) -> String:
  match s:
    case Dsc.Space{name, k, p, +about}:
      String.concat(["## ", name, marker_at(Nat.is_eq(v, n), Nat.is_eq(v, 0n)), about_at(String.is_empty(about), about)])

def plain_head(all: Bool) -> List<&2, Dsc.Part>:
  match all:
    case True{}:
      []
    case False{}:
      [Dsc.Lit{"Some tools are not listed: find them with `searchTools()`."}]

# R5: the blocks of the tools of no namespace (none when there are none)
def plain_spec(xs: List<&2, Dsc.Item>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> List<&2, Dsc.Part>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +r}:
      +vs = shown_spec(Con{x, r}, ts, shown)
      List.append(&2, Dsc.Part, plain_head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))), sects_spec(vs))

# R5: the blocks of the namespace groups
def named_spec(gs: List<&2, Dsc.Grp>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> List<&2, Dsc.Part>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      match g:
        case Dsc.Grp{s, +its}:
          +vs = shown_spec(its, ts, shown)
          List.append(&2, Dsc.Part, Dsc.Lit{heading_spec(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> sects_spec(vs), named_spec(r, ts, shown))

def blank_rest(xs: List<&2, Dsc.Part>) -> List<&2, Dsc.Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Dsc.Lit{"\n\n"} <> x <> blank_rest(r)

# R5: blocks joined by blank lines
def joined_spec(xs: List<&2, Dsc.Part>) -> List<&2, Dsc.Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> blank_rest(r)

def items_of(gs: List<&2, Dsc.Grp>) -> List<&2, List<&2, Dsc.Item>>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      match g:
        case Dsc.Grp{s, its}:
          its <> items_of(r)

def section_of(pg: List<&2, Dsc.Item> & List<&2, Dsc.Grp>, +ts: List<&2, Dsc.Tool>, budget: Nat) -> List<&2, Dsc.Part>:
  match pg:
    case (+plain, named):
      +gs = sorted_spec(named)
      +shown = names_spec(ts, select_spec(plain <> items_of(gs), budget))
      joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, plain_spec(plain, ts, shown), named_spec(gs, ts, shown)))

# R1-R5: the section for the tools ts, the namespaces ss and the budget
def section_spec(+ts: List<&2, Dsc.Tool>, +ss: List<&2, Dsc.Space>, budget: Nat) -> Maybe<&2, List<&2, Dsc.Part>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+t, +r}:
      Some{section_of(groups_spec(tags_spec(Con{t, r}, ss, prefixes_spec(ss), 0n), ([], [])), Con{t, r}, budget)}

# R6: the texts of the description, restated from describe.rs and
# models.rs
def intro_spec() -> String:
  "Run JavaScript that calls other tools. The input is raw JavaScript (not JSON, no code fence), run as an async function body in a QuickJS sandbox: top-level `await` and `return` work. No Node, file system, network, or timers.\n- `await tools.<name>({ ...args })` resolves to a string, or an object if the tool's declaration says so, and rejects with an Error on failure. A tool whose declaration returns an object resolves on failure too when it returned that object; check its fields. Calls still running when the script ends are cancelled.\n- The script survives a restart: it resumes where it was, without running finished calls again.\n- Optional first line: `// @options: {\"max_output_tokens\": 10000, \"timeout_ms\": 60000}`"

def globals_spec() -> String:
  String.concat(["Globals:", "\n", "- `text(value)`, `image(dataUrlOrImageBlock)`, `console.log(...)`, and top-level `return` add output; `exit()` ends the script. With several text items, each starts with a `==> text N/M <==` line, and `console` lines follow the other output in one `<console_output>` block. `image()` also saves the image to a temp file and the result names its path.", "\n", "- `store(key, value)` and `load(key)` keep JSON values across codemode calls.", "\n", "- `ALL_TOOLS`, `await searchTools(query, { limit?, namespace? })`, `await describeTool(name)`, `await describeNamespace(name)`: find tools the `codemode` section does not list."])

def models_spec() -> String:
  String.concat(["`models` (all functions return promises):\n", "- `models.getModelsOfType(type, provider?)`, `models.getAvailableOfType(type, provider?)` (configured auth only), `models.getModelOfType(type, provider, id)`: the catalog; `type` is \"chat\", \"image\", or \"classifier\".\n", "- `models.classify(model, { state: { ... }, images?: [{ type: \"image\", data, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } })` resolves to `{ answers: { <id>: ... }, stopReason, errorMessage?, usage? }`.\n", "- `models.generateImages(model, { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data, mimeType }] })` resolves to `{ output: [image blocks], stopReason, errorMessage?, usage? }`; show each image with `image(block)`.\n", "At most 4 classify/generateImages calls run at once; more wait."])

def footer_spec() -> String:
  "The `codemode` section of the system prompt lists the tools scripts can call, by namespace, as far as space allows."

def models_part(on: Bool, classify: Bool) -> List<&2, String>:
  match on:
    case False{}:
      []
    case True{}:
      match classify:
        case False{}:
          [models_spec()]
        case True{}:
          [String.concat([models_spec(), "\n", "`models.classify(null, context)` uses the session's default classifier."])]

# R6: the description
def description_spec(on: Bool, classify: Bool) -> String:
  String.join(List.concat(&2, String, [[intro_spec(), globals_spec()], models_part(on, classify), [footer_spec()]]), "\n\n")

# Laws
# ----

# LAW codemode_describe_space_exact: a tool's namespace is the first of the namespaces with the longest prefix its name starts with, none when no prefix fits
# EXCLUDES: the shortest or the last longest prefix, a prefix the name does
#   not start with, an index off by one, `<=` for `<` between lengths
law codemode_describe_space_exact:
  for +name: String
  for +ps: List<&2, String>
  {Dsc.space_of(name, ps) == space_spec(name, ps) : Maybe<&2, Nat>}

# LAW codemode_describe_select_exact: the tools shown are R4's rounds: each group still in, in order, places its cheapest remaining tool (ties in tool order) when it fits the budget left and drops out at its first tool that does not; rounds go on while a group is in
# EXCLUDES: the budget exceeded, a group that skips a misfit and goes on, a
#   group dropped for another's misfit, a whole group placed before the
#   next group's first tool, the most expensive tool first, ties out of
#   tool order, a budget left that does not fall, rounds that stop early
law codemode_describe_select_exact:
  for +gs: List<&2, List<&2, Dsc.Item>>
  for budget: Nat
  {Dsc.select(gs, budget) == select_spec(gs, budget) : List<&2, Nat>}

# LAW codemode_describe_section_exact: the section is R1-R5's: the intro, the tools of no namespace with their marker, then each namespace group in name order with its heading, marker and description, each with its shown sections in tool order, joined by blank lines; none without tools
# EXCLUDES: groups in another order (uppercase first, insertion order), a
#   namespace group listed twice, a heading without its marker or with the
#   wrong one, a blank description shown, sections in cost order, a hidden
#   tool shown, a joint other than a blank line, a section for no tools
law codemode_describe_section_exact:
  for +ts: List<&2, Dsc.Tool>
  for +ss: List<&2, Dsc.Space>
  for budget: Nat
  {Dsc.section(ts, ss, budget) == section_spec(ts, ss, budget) : Maybe<&2, List<&2, Dsc.Part>>}

# LAW codemode_describe_description_exact: the description is R6's for each choice of the models globals and the default classifier
# EXCLUDES: the models section without the models globals, the classifier
#   line without a resolver or on its own paragraph, a changed word
law codemode_describe_description_exact:
  for on: Bool
  for classify: Bool
  {Dsc.description(on, classify) == description_spec(on, classify) : String}

# LAW codemode_describe_example: anchor: describe.rs's tests: the longest prefix, groups in name order with their descriptions, no budget, a partly listed namespace, a round-robin by cost under budgets 8 and 3, no tools
# EXCLUDES: a spec that is wrong on the shipped cases
law codemode_describe_example:
  {[Dsc.space_of("mcp__docs__search", ["mcp__", "mcp__docs__", "mcp__docs__"]), Dsc.space_of("mcp__x", ["mcp__", "mcp__docs__", "mcp__docs__"]), Dsc.space_of("read", ["mcp__", "mcp__docs__"])] == [Some{1n}, Some{0n}, None{}] : List<&2, Maybe<&2, Nat>>} &
  {Dsc.section([Dsc.Tool{"gh-issues", 100n}, Dsc.Tool{"read", 90n}, Dsc.Tool{"ab-x", 80n}], [Dsc.Space{"GitHub", "github", "gh-", "GitHub tools."}, Dsc.Space{"alpha", "alpha", "ab-", "Alpha tools"}, Dsc.Space{"empty", "empty", "zz-", ""}], 3000n) == Some{[Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"}, Dsc.Lit{"\n\n"}, Dsc.Sect{1n}, Dsc.Lit{"\n\n"}, Dsc.Lit{"## alpha\nAlpha tools"}, Dsc.Lit{"\n\n"}, Dsc.Sect{2n}, Dsc.Lit{"\n\n"}, Dsc.Lit{"## GitHub\nGitHub tools."}, Dsc.Lit{"\n\n"}, Dsc.Sect{0n}]} : Maybe<&2, List<&2, Dsc.Part>>} &
  {Dsc.section([Dsc.Tool{"gh-issues", 100n}, Dsc.Tool{"read", 90n}, Dsc.Tool{"ab-x", 80n}], [Dsc.Space{"GitHub", "github", "gh-", "GitHub tools."}, Dsc.Space{"alpha", "alpha", "ab-", "Alpha tools"}], 0n) == Some{[Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"}, Dsc.Lit{"\n\n"}, Dsc.Lit{"Some tools are not listed: find them with `searchTools()`."}, Dsc.Lit{"\n\n"}, Dsc.Lit{"## alpha (tools not listed)\nAlpha tools"}, Dsc.Lit{"\n\n"}, Dsc.Lit{"## GitHub (tools not listed)\nGitHub tools."}]} : Maybe<&2, List<&2, Dsc.Part>>} &
  {Dsc.section([Dsc.Tool{"gh-a", 160n}, Dsc.Tool{"gh-b", 300n}], [Dsc.Space{"GitHub", "github", "gh-", ""}], 40n) == Some{[Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"}, Dsc.Lit{"\n\n"}, Dsc.Lit{"## GitHub (some tools not listed)"}, Dsc.Lit{"\n\n"}, Dsc.Sect{0n}]} : Maybe<&2, List<&2, Dsc.Part>>} &
  {[Dsc.select([[Dsc.Item{0n, 5n}, Dsc.Item{1n, 1n}], [], [Dsc.Item{2n, 3n}, Dsc.Item{3n, 3n}]], 8n), Dsc.select([[Dsc.Item{0n, 5n}, Dsc.Item{1n, 1n}], [], [Dsc.Item{2n, 3n}, Dsc.Item{3n, 3n}]], 3n)] == [[1n, 2n, 3n], [1n]] : List<&2, List<&2, Nat>>} &
  {Dsc.section([], [Dsc.Space{"GitHub", "github", "gh-", ""}], 100n) == None{} : Maybe<&2, List<&2, Dsc.Part>>}

# LAWS (R7): the entry of the compiled Bend core
# (bend/ffi_codemode_describe.bend, called by crates/eukhe-durable
# codemode/describe.rs and call.rs through
# `eukhe_bend::rules::codemode_describe`). Each law is an open claim about
# FDsc.ffi, stated with spec spellers built only from the wire primitives
# of bend/wire.bend (their round trips: laws/wire.bend).
#
# R7: a request is a question: tag 0 the namespaces: a List of tool names
#     and a List of prefixes (Strings), answered with a List of Maybe<Nat>
#     (0 none, 1 then the index), one per name; tag 1 the section: a List
#     of tools (its name, a String, then its section's UTF-16 length, a
#     Nat), a List of namespaces (its name, its lowercase name, its prefix,
#     its description, Strings) and the budget (a Nat), answered with 0
#     (none) or 1 then a List of parts (0 then a text, a String; 1 then a
#     tool's index, a Nat); tag 2 the description: two Bools (the models
#     globals, a default classifier), answered with the text (a String).
#     Every input that is not exactly one request whose counts, numbers
#     and lengths fit the wire answers the error form "codemode_describe:
#     malformed request"; never a default.

# Spec spellers
# -------------

def spell_tool(t: Dsc.Tool, rest: String) -> String:
  match t:
    case Dsc.Tool{n, z}:
      Wr.put_str(n, Wr.put_nat(z, rest))

def spell_tools.items(ts: List<&2, Dsc.Tool>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case Con{t, r}:
      spell_tool(t, spell_tools.items(r, rest))

def spell_space(s: Dsc.Space, rest: String) -> String:
  match s:
    case Dsc.Space{n, k, p, a}:
      Wr.put_str(n, Wr.put_str(k, Wr.put_str(p, Wr.put_str(a, rest))))

def spell_spaces.items(ss: List<&2, Dsc.Space>, rest: String) -> String:
  match ss:
    case Nil{}:
      rest
    case Con{s, r}:
      spell_space(s, spell_spaces.items(r, rest))

# a request, then rest
def spell_req(q: FDsc.Req, rest: String) -> String:
  match q:
    case FDsc.QSpaces{+ns, ps}:
      Wr.put_nat(0n, LawsBase.wire_spell_strs(ns, LawsBase.wire_spell_strs(ps, rest)))
    case FDsc.QSection{+ts, +ss, b}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), spell_tools.items(ts, Wr.put_nat(List.length(&2, Dsc.Space, ss), spell_spaces.items(ss, Wr.put_nat(b, rest))))))
    case FDsc.QDescribe{m, c}:
      Wr.put_nat(2n, Wr.put_bool(m, Wr.put_bool(c, rest)))

def spell_mnats(xs: List<&2, Maybe<&2, Nat>>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, r}:
      match x:
        case None{}:
          Wr.put_nat(0n, spell_mnats(r, rest))
        case Some{n}:
          Wr.put_nat(1n, Wr.put_nat(n, spell_mnats(r, rest)))

def spell_parts(ps: List<&2, Dsc.Part>, rest: String) -> String:
  match ps:
    case Nil{}:
      rest
    case Con{p, r}:
      match p:
        case Dsc.Lit{t}:
          Wr.put_nat(0n, Wr.put_str(t, spell_parts(r, rest)))
        case Dsc.Sect{n}:
          Wr.put_nat(1n, Wr.put_nat(n, spell_parts(r, rest)))

def spell_section(m: Maybe<&2, List<&2, Dsc.Part>>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{+ps}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Part, ps), spell_parts(ps, "")))

def spaces_spec(ns: List<&2, String>, +ps: List<&2, String>) -> List<&2, Maybe<&2, Nat>>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Dsc.space_of(n, ps) <> spaces_spec(r, ps)

# the reply Rust reads: the spelled answer of the model
def spell_reply(q: FDsc.Req) -> String:
  match q:
    case FDsc.QSpaces{ns, ps}:
      +xs = spaces_spec(ns, ps)
      Wr.put_nat(List.length(&2, Maybe<&2, Nat>, xs), spell_mnats(xs, ""))
    case FDsc.QSection{ts, ss, b}:
      spell_section(Dsc.section(ts, ss, b))
    case FDsc.QDescribe{m, c}:
      Wr.put_str(Dsc.description(m, c), "")

def tool_fits(t: Dsc.Tool) -> Bool:
  match t:
    case Dsc.Tool{n, z}:
      Bool.and(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(z))

def tools_all(ts: List<&2, Dsc.Tool>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, r}:
      Bool.and(tool_fits(t), tools_all(r))

def space_fits(s: Dsc.Space) -> Bool:
  match s:
    case Dsc.Space{n, k, p, a}:
      Bool.and(Bool.and(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k))), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a))))

def spaces_all(ss: List<&2, Dsc.Space>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, r}:
      Bool.and(space_fits(s), spaces_all(r))

# every count, number and length of the request fits the wire
def req_fits(q: FDsc.Req) -> Bool:
  match q:
    case FDsc.QSpaces{ns, ps}:
      Bool.and(LawsBase.wire_strs_fit(ns), LawsBase.wire_strs_fit(ps))
    case FDsc.QSection{+ts, +ss, b}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, ts)), tools_all(ts)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), spaces_all(ss)), LawsBase.wire_fits(b)))
    case FDsc.QDescribe{m, c}:
      True{}

# LAW codemode_describe_ffi_answers: a spelled request whose numbers fit the wire answers the spelled answer of the model
# EXCLUDES: a fact misread (a size or a prefix swapped, a tag off by one),
#   an answer spelled with another tag, a question answered by another
#   model function
law codemode_describe_ffi_answers:
  for +q: FDsc.Req
  for h: {req_fits(q) == True{} : Bool}
  {FDsc.ffi(spell_req(q, "")) == spell_reply(q) : String}

# LAW codemode_describe_ffi_reads: the entry's decoder reads a spelled request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law codemode_describe_ffi_reads:
  for +q: FDsc.Req
  for +rest: String
  for h: {req_fits(q) == True{} : Bool}
  {FDsc.get_req(spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDsc.Req>}

# LAW codemode_describe_ffi_exact: every input the entry does not answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer made for input that is no request (an unknown tag,
#   a missing field, a Nat of 15 or more digits, a short string, input
#   left over)
law codemode_describe_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDsc.ffi(s)) == False{} : Bool}
  exs q: FDsc.Req
  {s == spell_req(q, "") : String} & {req_fits(q) == True{} : Bool}

# LAW codemode_describe_ffi_refuses: every error the entry answers is exactly "codemode_describe: malformed request"
# EXCLUDES: an error text that varies with the input, a second error form
law codemode_describe_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FDsc.ffi(s)) == True{} : Bool}
  {FDsc.ffi(s) == Wr.err("codemode_describe: malformed request") : String}

# LAW codemode_describe_ffi_example: anchor: the bytes Rust sends and reads: namespaces of two names, a partly listed namespace, no tools, an unknown tag, input left over
# EXCLUDES: another spelling of a fact or an answer
law codemode_describe_ffi_example:
  {[FDsc.ffi("0,2,5,mcp_x4,read2,4,mcp_2,zz"), FDsc.ffi("1,2,4,gh-a160,4,gh-b300,1,6,GitHub6,github3,gh-0,40,"), FDsc.ffi("1,0,0,5,"), FDsc.ffi("3,"), FDsc.ffi("2,FFx")] == ["2,1,0,0,", "1,5,0,52,Tools scripts can call (`await tools.<name>(args)`):0,2,\n\n0,33,## GitHub (some tools not listed)0,2,\n\n1,0,", "0,", Wr.err("codemode_describe: malformed request"), Wr.err("codemode_describe: malformed request")] : List<&2, String>}

