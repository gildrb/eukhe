# codemode_describe: the code mode tool's description and its `codemode`
# system prompt section (port of pi-durable `codemode/describe.ts`; the Rust
# host is crates/eukhe-durable/src/codemode/describe.rs). The section lists
# the tools scripts can call, grouped by namespace (a tool belongs to the
# namespace with the longest prefix its name starts with, the first of
# equally long ones; namespaces of one name are one group, shown with the
# first one's description): the tools of no namespace first, then the
# namespaces by name (case-insensitive first, then lowercase before
# uppercase). A tool's section costs its UTF-16 length divided by 4, rounded
# up, in tokens; the sections shown fit the budget: in each round every
# group still in places its cheapest remaining tool (ties in tool order),
# and a group whose next tool does not fit drops out while the others go
# on. A group's heading marks tools not shown. The host renders each tool's
# section (its heading, description and declaration) and gives its UTF-16
# length, and gives each namespace's lowercase name (Rust `to_lowercase`)
# and trimmed description; this model answers which sections show, in
# which order, and every other text of the section and of the description.
# Pure: no IO, no @unsafe. laws/codemode_describe.bend states its laws.

import Base
import ./codemode_models.bend as Cm

# Facts
# -----

# a tool: its name and the UTF-16 length of its rendered section
type Tool is Data:
  Tool{name: String, size: Nat}

# a namespace: its name, its name in lowercase, its prefix, its description
# trimmed ("" when none)
type Space is Data:
  Space{name: String, key: String, prefix: String, about: String}

# a part of the section's text: a text, or the rendered section of the
# tool at an index
type Part is Data:
  Lit{text: String}
  Sect{tool: Nat}

# A tool's namespace
# ------------------

# a prefix that a name starts with: its index and its length
type Hit is Data:
  Hit{i: Nat, n: Nat}

def best.at(later: Bool, i: Nat, n: Nat, j: Nat, m: Nat) -> Maybe<&2, Hit>:
  match later:
    case True{}:
      Some{Hit{j, m}}
    case False{}:
      Some{Hit{i, n}}

# a prefix at i of length n against the best later one: the later one only
# when it is strictly longer
def best.of(+i: Nat, +n: Nat, rest: Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match rest:
    case None{}:
      Some{Hit{i, n}}
    case Some{b}:
      match b:
        case Hit{j, +m}:
          best.at(Nat.is_lt(n, m), i, n, j, m)

def best.pick(hit: Bool, +i: Nat, +n: Nat, rest: Maybe<&2, Hit>) -> Maybe<&2, Hit>:
  match hit:
    case True{}:
      best.of(i, n, rest)
    case False{}:
      rest

# the index (from i) and length of the longest prefix of ps that name
# starts with, the first of equally long ones
def best(ps: List<&2, String>, +name: String, +i: Nat) -> Maybe<&2, Hit>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, r}:
      best.pick(String.starts_with(name, p), i, String.length(p), best(r, name, 1n+i))

def space.index(b: Maybe<&2, Hit>) -> Maybe<&2, Nat>:
  match b:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Hit{i, n}:
          Some{i}

# the namespace of the tool named name, by its index among the prefixes ps
# (two prefixes of one name: the longer in chars is the longer in UTF-16
# units, one being a prefix of the other)
def space_of(+name: String, ps: List<&2, String>) -> Maybe<&2, Nat>:
  space.index(best(ps, name, 0n))

# The groups
# ----------

# a tool of a group: its index and its cost
type Item is Data:
  Item{tool: Nat, cost: Nat}

# a namespace's group: its namespace and its tools in tool order
type Grp is Data:
  Grp{space: Space, items: List<&2, Item>}

# a tool with its namespace, if any
type Tagged is Data:
  Tagged{space: Maybe<&2, Space>, item: Item}

# a section's cost in tokens: its UTF-16 length divided by 4, rounded up
def cost(size: Nat) -> Nat:
  Nat.div(Nat.add(size, 3n), 4n)

def at(ss: List<&2, Space>, n: Nat) -> Maybe<&2, Space>:
  match ss:
    case Nil{}:
      None{}
    case Con{s, r}:
      match n:
        case 0n:
          Some{s}
        case 1n+k:
          at(r, k)

def prefixes(ss: List<&2, Space>) -> List<&2, String>:
  match ss:
    case Nil{}:
      []
    case Con{s, r}:
      match s:
        case Space{n, k, p, a}:
          p <> prefixes(r)

def find(m: Maybe<&2, Nat>, ss: List<&2, Space>) -> Maybe<&2, Space>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      at(ss, j)

# each tool (from index i) with its namespace and cost
def tagged(ts: List<&2, Tool>, +ss: List<&2, Space>, +ps: List<&2, String>, +i: Nat) -> List<&2, Tagged>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      match t:
        case Tool{n, z}:
          Tagged{find(space_of(n, ps), ss), Item{i, cost(z)}} <> tagged(r, ss, ps, 1n+i)

def name_of(s: Space) -> String:
  match s:
    case Space{n, k, p, a}:
      n

def same_name(g: Grp, +s: Space) -> Bool:
  match g:
    case Grp{s2, its}:
      String.eq(name_of(s2), name_of(s))

def put.sel(same: Bool, g: Grp, x: Item, r: List<&2, Grp>, other: List<&2, Grp>) -> List<&2, Grp>:
  match same:
    case True{}:
      match g:
        case Grp{s, its}:
          Grp{s, List.append(&2, Item, its, [x])} <> r
    case False{}:
      g <> other

# add x to the group of namespace s's name, else to a new last group
def put(gs: List<&2, Grp>, +s: Space, +x: Item) -> List<&2, Grp>:
  match gs:
    case Nil{}:
      [Grp{s, [x]}]
    case Con{+g, +r}:
      put.sel(same_name(g, s), g, x, r, put(r, s, x))

def step(m: Maybe<&2, Space>, plain: List<&2, Item>, named: List<&2, Grp>, x: Item) -> List<&2, Item> & List<&2, Grp>:
  match m:
    case None{}:
      (List.append(&2, Item, plain, [x]), named)
    case Some{s}:
      (plain, put(named, s, x))

def groups.step(acc: List<&2, Item> & List<&2, Grp>, x: Tagged) -> List<&2, Item> & List<&2, Grp>:
  match acc:
    case (plain, named):
      match x:
        case Tagged{m, it}:
          step(m, plain, named, it)

# the tools of no namespace, and the namespaces' groups in the order their
# first tool comes
def groups(xs: List<&2, Tagged>, acc: List<&2, Item> & List<&2, Grp>) -> List<&2, Item> & List<&2, Grp>:
  match xs:
    case Nil{}:
      acc
    case Con{x, r}:
      groups(r, groups.step(acc, x))

# The order of the groups
# -----------------------

def key_of(s: Space) -> String:
  match s:
    case Space{n, k, p, a}:
      k

def grp_space(g: Grp) -> Space:
  match g:
    case Grp{s, its}:
      s

def before.tie(same: Bool, +a: Space, +b: Space) -> Bool:
  match same:
    case True{}:
      String.is_lt(name_of(b), name_of(a))
    case False{}:
      String.is_lt(key_of(a), key_of(b))

# JS `localeCompare` as describe.rs approximates it: the lowercase names
# first, then the names reversed (lowercase before uppercase)
def before(+a: Space, +b: Space) -> Bool:
  before.tie(String.eq(key_of(a), key_of(b)), a, b)

def insert.sel(first: Bool, g: Grp, h: Grp, t: List<&2, Grp>, later: List<&2, Grp>) -> List<&2, Grp>:
  match first:
    case True{}:
      g <> h <> t
    case False{}:
      h <> later

def insert(+g: Grp, gs: List<&2, Grp>) -> List<&2, Grp>:
  match gs:
    case Nil{}:
      [g]
    case Con{+h, +t}:
      insert.sel(Bool.not(before(grp_space(h), grp_space(g))), g, h, t, insert(g, t))

# the groups in namespace order (a stable insertion sort)
def order(gs: List<&2, Grp>) -> List<&2, Grp>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      insert(g, order(r))

# The tools shown
# ---------------

def item_cost(x: Item) -> Nat:
  match x:
    case Item{t, c}:
      c

def item_tool(x: Item) -> Nat:
  match x:
    case Item{t, c}:
      t

def cheap.sel(first: Bool, x: Item, h: Item, t: List<&2, Item>, later: List<&2, Item>) -> List<&2, Item>:
  match first:
    case True{}:
      x <> h <> t
    case False{}:
      h <> later

def cheap.insert(+x: Item, xs: List<&2, Item>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      [x]
    case Con{+h, +t}:
      cheap.sel(Nat.is_le(item_cost(x), item_cost(h)), x, h, t, cheap.insert(x, t))

# a group's tools by cost, ties in tool order (a stable insertion sort)
def cheap(xs: List<&2, Item>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      cheap.insert(x, cheap(r))

# one round's result: the queues still in, the budget left, the tools
# placed
type Out is Data:
  Out{live: List<&2, List<&2, Item>>, left: Nat, placed: List<&2, Nat>}

# the queue's head fits the budget left
def fits(qs: List<&2, List<&2, Item>>, +rem: Nat) -> Bool:
  match qs:
    case Nil{}:
      False{}
    case Con{q, r}:
      match q:
        case Nil{}:
          False{}
        case Con{x, t}:
          Nat.is_le(item_cost(x), rem)

def round.keep(rest: List<&2, Item>, t: Nat, o: Out) -> Out:
  match rest:
    case Nil{}:
      match o:
        case Out{live, left, placed}:
          Out{live, left, t <> placed}
    case Con{h, u}:
      match o:
        case Out{live, left, placed}:
          Out{Con{h, u} <> live, left, t <> placed}

# one round over the queues qs (ok: the first queue's head fits rem): each
# queue places its head when it fits and stays in while it has tools left;
# a queue whose head does not fit drops out
def round(qs: List<&2, List<&2, Item>>, ok: Bool, +rem: Nat) -> Out:
  match qs:
    case Nil{}:
      Out{[], rem, []}
    case Con{q, +r}:
      match q:
        case Nil{}:
          round(r, fits(r, rem), rem)
        case Con{+x, rest}:
          match ok:
            case True{}:
              +rem2 = Nat.sub(rem, item_cost(x))
              round.keep(rest, item_tool(x), round(r, fits(r, rem2), rem2))
            case False{}:
              round(r, fits(r, rem), rem)

# rounds until no queue is in (fuel: one round per tool and one more)
def rounds(fuel: Nat, o: Out) -> List<&2, Nat>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match o:
        case Out{live, +left, placed}:
          match live:
            case Nil{}:
              placed
            case Con{+q, +r}:
              List.append(&2, Nat, placed, rounds(f, round(Con{q, r}, fits(Con{q, r}, left), left)))

def queues(gs: List<&2, List<&2, Item>>) -> List<&2, List<&2, Item>>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      match g:
        case Nil{}:
          queues(r)
        case Con{x, t}:
          cheap(Con{x, t}) <> queues(r)

def total(gs: List<&2, List<&2, Item>>) -> Nat:
  match gs:
    case Nil{}:
      0n
    case Con{g, r}:
      Nat.add(List.length(&2, Item, g), total(r))

# the tools shown (their indexes, in the order they are placed) for the
# groups gs (each its tools in tool order) under the budget: rounds until
# no queue is in, at most one per tool and one more (a round places a tool
# or ends every queue still in)
def select(+gs: List<&2, List<&2, Item>>, budget: Nat) -> List<&2, Nat>:
  rounds(1n+total(gs), Out{queues(gs), budget, []})

# The section
# -----------

def tool_name(ts: List<&2, Tool>, n: Nat) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, r}:
      match t:
        case Tool{name, z}:
          match n:
            case 0n:
              name
            case 1n+k:
              tool_name(r, k)

def names(+ts: List<&2, Tool>, xs: List<&2, Nat>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      tool_name(ts, x) <> names(ts, r)

# A set of names: the placed tools' names as a forest of their chars (first
# child, next sibling), so that each tool's name is looked up in time of
# its length, not of the number of tools placed. A node holds a char,
# whether a name ends at it, the forest of what follows it, and its next
# sibling.
type Tr is Data:
  TEnd{}
  TNode{c: Char, stop: Bool, down: Tr, next: Tr}

# the forest's first node holds c
def tr.hit(t: Tr, +c: Char) -> Bool:
  match t:
    case TEnd{}:
      False{}
    case TNode{d, s, w, n}:
      Char.is_eq(d, c)

# the forest of the one name c then r
def tr.chain(r: String, c: Char) -> Tr:
  match r:
    case SNil{}:
      TNode{c, True{}, TEnd{}, TEnd{}}
    case SCon{e, q}:
      TNode{c, False{}, tr.chain(q, e), TEnd{}}

# the forest t with the name c then r added (hit: tr.hit(t, c))
def tr.add(t: Tr, hit: Bool, +c: Char, r: String) -> Tr:
  match t:
    case TEnd{}:
      tr.chain(r, c)
    case TNode{d, s, +w, +n}:
      match hit:
        case True{}:
          match r:
            case SNil{}:
              TNode{d, True{}, w, n}
            case SCon{+e, q}:
              TNode{d, s, tr.add(w, tr.hit(w, e), e, q), n}
        case False{}:
          TNode{d, s, w, tr.add(n, tr.hit(n, c), c, r)}

# the forest t holds the name c then r (hit: tr.hit(t, c))
def tr.has(t: Tr, hit: Bool, +c: Char, r: String) -> Bool:
  match t:
    case TEnd{}:
      False{}
    case TNode{d, s, +w, +n}:
      match hit:
        case True{}:
          match r:
            case SNil{}:
              s
            case SCon{+e, q}:
              tr.has(w, tr.hit(w, e), e, q)
        case False{}:
          tr.has(n, tr.hit(n, c), c, r)

# a set of names: whether it holds "", and the forest of the others
type NSet is Data:
  NSet{empty: Bool, t: Tr}

def nset.add(s: NSet, x: String) -> NSet:
  match s:
    case NSet{e, +t}:
      match x:
        case SNil{}:
          NSet{True{}, t}
        case SCon{+c, r}:
          NSet{e, tr.add(t, tr.hit(t, c), c, r)}

def nset.has(s: NSet, x: String) -> Bool:
  match s:
    case NSet{e, +t}:
      match x:
        case SNil{}:
          e
        case SCon{+c, r}:
          tr.has(t, tr.hit(t, c), c, r)

# the set of the names ns
def nset.of(ns: List<&2, String>) -> NSet:
  match ns:
    case Nil{}:
      NSet{False{}, TEnd{}}
    case Con{x, r}:
      nset.add(nset.of(r), x)

def visible.sel(shown: Bool, x: Item, rest: List<&2, Item>) -> List<&2, Item>:
  match shown:
    case True{}:
      x <> rest
    case False{}:
      rest

# the name of the first tool of ts ("" when none)
def head_name(ts: List<&2, Tool>) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, r}:
      match t:
        case Tool{n, z}:
          n

# the tools from index t on: from cur (the tools from index pos on) when
# pos <= t, else from the start
def vis.here(ahead: Bool, cur: List<&2, Tool>, +ts: List<&2, Tool>, +pos: Nat, +t: Nat) -> List<&2, Tool>:
  match ahead:
    case True{}:
      List.drop(&2, Tool, cur, Nat.sub(t, pos))
    case False{}:
      List.drop(&2, Tool, ts, t)

# the tools of xs whose names the set holds; cur: the tools from index pos
# on (a group's tools come in tool order, so one walk over the tools finds
# all their names)
def vis(xs: List<&2, Item>, +ts: List<&2, Tool>, cur: List<&2, Tool>, +pos: Nat, +set: NSet) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      match x:
        case Item{+t, c}:
          +here = vis.here(Nat.is_le(pos, t), cur, ts, pos, t)
          visible.sel(nset.has(set, head_name(here)), Item{t, c}, vis(r, ts, here, t, set))

# the tools of xs shown: a tool is shown when a tool of its name was placed
def visible(xs: List<&2, Item>, +ts: List<&2, Tool>, shown: List<&2, String>) -> List<&2, Item>:
  vis(xs, ts, ts, 0n, nset.of(shown))

def sects(xs: List<&2, Item>) -> List<&2, Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      match x:
        case Item{t, c}:
          Sect{t} <> sects(r)

def intro_text() -> String:
  "Tools scripts can call (`await tools.<name>(args)`):"

def unlisted_text() -> String:
  "Some tools are not listed: find them with `searchTools()`."

def listing.none(none: Bool) -> String:
  match none:
    case True{}:
      " (tools not listed)"
    case False{}:
      " (some tools not listed)"

# what a namespace's heading says of its tools shown (v of n)
def listing.sel(all: Bool, +v: Nat) -> String:
  match all:
    case True{}:
      ""
    case False{}:
      listing.none(Nat.is_eq(v, 0n))

def listing(+v: Nat, +n: Nat) -> String:
  listing.sel(Nat.is_eq(v, n), v)

def about.sel(empty: Bool, about: String) -> String:
  match empty:
    case True{}:
      ""
    case False{}:
      String.append("\n", about)

# a namespace's heading: its name, the tools not shown, its description
def heading(s: Space, v: Nat, n: Nat) -> String:
  match s:
    case Space{name, k, p, +about}:
      String.concat(["## ", name, listing(v, n), about.sel(String.is_empty(about), about)])

def plain.head(all: Bool) -> List<&2, Part>:
  match all:
    case True{}:
      []
    case False{}:
      [Lit{unlisted_text()}]

# the blocks of the tools of no namespace (none when there are none)
def plain.blocks(xs: List<&2, Item>, +ts: List<&2, Tool>, +shown: List<&2, String>) -> List<&2, Part>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +r}:
      +vs = visible(Con{x, r}, ts, shown)
      List.append(&2, Part, plain.head(Nat.is_eq(List.length(&2, Item, vs), List.length(&2, Item, Con{x, r}))), sects(vs))

def grp.blocks(g: Grp, +ts: List<&2, Tool>, +shown: List<&2, String>) -> List<&2, Part>:
  match g:
    case Grp{s, +its}:
      +vs = visible(its, ts, shown)
      Lit{heading(s, List.length(&2, Item, vs), List.length(&2, Item, its))} <> sects(vs)

def grps.blocks(gs: List<&2, Grp>, +ts: List<&2, Tool>, +shown: List<&2, String>) -> List<&2, Part>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      List.append(&2, Part, grp.blocks(g, ts, shown), grps.blocks(r, ts, shown))

def sep.rest(xs: List<&2, Part>) -> List<&2, Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Lit{"\n\n"} <> x <> sep.rest(r)

# the blocks joined by blank lines
def sep(xs: List<&2, Part>) -> List<&2, Part>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      x <> sep.rest(r)

def grp_items(g: Grp) -> List<&2, Item>:
  match g:
    case Grp{s, its}:
      its

def grps_items(gs: List<&2, Grp>) -> List<&2, List<&2, Item>>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      grp_items(g) <> grps_items(r)

def section.of(pg: List<&2, Item> & List<&2, Grp>, +ts: List<&2, Tool>, +budget: Nat) -> List<&2, Part>:
  match pg:
    case (+plain, named):
      +ordered = order(named)
      +shown = names(ts, select(plain <> grps_items(ordered), budget))
      sep(Lit{intro_text()} <> List.append(&2, Part, plain.blocks(plain, ts, shown), grps.blocks(ordered, ts, shown)))

# the `codemode` section for the tools ts, the namespaces ss and the
# budget (tokens), as parts; none without tools
def section(+ts: List<&2, Tool>, +ss: List<&2, Space>, +budget: Nat) -> Maybe<&2, List<&2, Part>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+t, +r}:
      Some{section.of(groups(tagged(Con{t, r}, ss, prefixes(ss), 0n), ([], [])), Con{t, r}, budget)}

# The description
# ---------------

def intro() -> String:
  "Run JavaScript that calls other tools. The input is raw JavaScript (not JSON, no code fence), run as an async function body in a QuickJS sandbox: top-level `await` and `return` work. No Node, file system, network, or timers.\n- `await tools.<name>({ ...args })` resolves to a string, or an object if the tool's declaration says so, and rejects with an Error on failure. A tool whose declaration returns an object resolves on failure too when it returned that object; check its fields. Calls still running when the script ends are cancelled.\n- The script survives a restart: it resumes where it was, without running finished calls again.\n- Optional first line: `// @options: {\"max_output_tokens\": 10000, \"timeout_ms\": 60000}`"

def globals() -> String:
  "Globals:\n- `text(value)`, `image(dataUrlOrImageBlock)`, `console.log(...)`, and top-level `return` add output; `exit()` ends the script. With several text items, each starts with a `==> text N/M <==` line, and `console` lines follow the other output in one `<console_output>` block. `image()` also saves the image to a temp file and the result names its path.\n- `store(key, value)` and `load(key)` keep JSON values across codemode calls.\n- `ALL_TOOLS`, `await searchTools(query, { limit?, namespace? })`, `await describeTool(name)`, `await describeNamespace(name)`: find tools the `codemode` section does not list."

# the `models` part; it names the model calls that run at once as
# bend/codemode_models.bend's limit (the host runs them under it)
def models() -> String:
  String.concat(["`models` (all functions return promises):\n- `models.getModelsOfType(type, provider?)`, `models.getAvailableOfType(type, provider?)` (configured auth only), `models.getModelOfType(type, provider, id)`: the catalog; `type` is \"chat\", \"image\", or \"classifier\".\n- `models.classify(model, { state: { ... }, images?: [{ type: \"image\", data, mimeType }], questions: { <id>: { type: \"choice\", instructions, criteria: { <label>: <meaning> } } | { type: \"score\", instructions, criteria: [<lowest level>, ..., <highest level>] } | { type: \"bool\", instructions, criteria: { true: <meaning>, false: <meaning> } } } })` resolves to `{ answers: { <id>: ... }, stopReason, errorMessage?, usage? }`.\n- `models.generateImages(model, { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data, mimeType }] })` resolves to `{ output: [image blocks], stopReason, errorMessage?, usage? }`; show each image with `image(block)`.\nAt most ", Nat.show(Cm.max_calls()), " classify/generateImages calls run at once; more wait."])

def classifier() -> String:
  "`models.classify(null, context)` uses the session's default classifier."

def footer() -> String:
  "The `codemode` section of the system prompt lists the tools scripts can call, by namespace, as far as space allows."

def description.models(classify: Bool) -> String:
  match classify:
    case True{}:
      String.concat([models(), "\n", classifier(), "\n\n"])
    case False{}:
      String.append(models(), "\n\n")

def description.with(on: Bool, classify: Bool) -> String:
  match on:
    case True{}:
      String.append(description.models(classify), footer())
    case False{}:
      footer()

# the code mode tool's description: the script environment, its globals,
# the `models` globals when scripts get them (with the default classifier's
# line when the session resolves one), and where the tools are listed
def description(on: Bool, classify: Bool) -> String:
  String.concat([intro(), "\n\n", globals(), "\n\n", description.with(on, classify)])
