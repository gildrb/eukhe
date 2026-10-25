# eukhe: lemmas of the proofs of area codemode_describe: the section
#
# Each step of Dsc.section is the spec's step of laws/codemode_describe.bend
# that it ports: the tools with their namespaces (cds.tagged), the groups
# (cds.groups), their order (cds.order), the tools shown (cdsel.select of
# ../base.bend), the headings and markers (cds.heading), the blocks
# (cds.plain, cds.named) and the joint (cds.sep).

import Base
import ../../../bend/codemode_describe.bend as Dsc
import ../../../laws/codemode_describe.bend as CodemodeDescribe
import ../base.bend as LACd

# ---- the tools and their namespaces ----

def cds.at(ss: List<&2, Dsc.Space>, n: Nat) -> {Dsc.at(ss, n) == CodemodeDescribe.space_at(ss, n) : Maybe<&2, Dsc.Space>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, r}:
      match n:
        case 0n:
          {==}
        case 1n+k:
          cds.at(r, k)

def cds.prefixes(ss: List<&2, Dsc.Space>) -> {Dsc.prefixes(ss) == CodemodeDescribe.prefixes_spec(ss) : List<&2, String>}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +r}:
      match s:
        case Dsc.Space{n, k, p, a}:
          %cds.prefixes(r) : {p <> Dsc.prefixes(r) == p <> _ : List<&2, String>}
          {==}

def cds.find(m: Maybe<&2, Nat>, ss: List<&2, Dsc.Space>) -> {Dsc.find(m, ss) == CodemodeDescribe.space_found(m, ss) : Maybe<&2, Dsc.Space>}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      cds.at(ss, j)

def cds.tagged(ts: List<&2, Dsc.Tool>, +ss: List<&2, Dsc.Space>, +ps: List<&2, String>, +i: Nat) -> {Dsc.tagged(ts, ss, ps, i) == CodemodeDescribe.tags_spec(ts, ss, ps, i) : List<&2, Dsc.Tagged>}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, +r}:
      match t:
        case Dsc.Tool{+n, z}:
          %LACd.cd.space(n, ps) : {Dsc.tagged(Con{Dsc.Tool{n, z}, r}, ss, ps, i) == Dsc.Tagged{CodemodeDescribe.space_found(_, ss), Dsc.Item{i, CodemodeDescribe.cost_spec(z)}} <> CodemodeDescribe.tags_spec(r, ss, ps, 1n+i) : List<&2, Dsc.Tagged>}
          %cds.find(Dsc.space_of(n, ps), ss) : {Dsc.tagged(Con{Dsc.Tool{n, z}, r}, ss, ps, i) == Dsc.Tagged{_, Dsc.Item{i, CodemodeDescribe.cost_spec(z)}} <> CodemodeDescribe.tags_spec(r, ss, ps, 1n+i) : List<&2, Dsc.Tagged>}
          %cds.tagged(r, ss, ps, 1n+i) : {Dsc.tagged(Con{Dsc.Tool{n, z}, r}, ss, ps, i) == Dsc.Tagged{Dsc.find(Dsc.space_of(n, ps), ss), Dsc.Item{i, CodemodeDescribe.cost_spec(z)}} <> _ : List<&2, Dsc.Tagged>}
          {==}

# ---- the groups ----

def cds.join_at(b: Bool, g: Dsc.Grp, x: Dsc.Item, r: List<&2, Dsc.Grp>, o: List<&2, Dsc.Grp>) -> {Dsc.put.sel(b, g, x, r, o) == CodemodeDescribe.join_at(b, g, x, r, o) : List<&2, Dsc.Grp>}:
  match b:
    case True{}:
      match g:
        case Dsc.Grp{s, its}:
          {==}
    case False{}:
      {==}

def cds.put(gs: List<&2, Dsc.Grp>, +s: Dsc.Space, +x: Dsc.Item) -> {Dsc.put(gs, s, x) == CodemodeDescribe.join_spec(gs, s, x) : List<&2, Dsc.Grp>}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Dsc.Grp{s2, +its}:
          match s2:
            case Dsc.Space{+n2, +k2, +p2, +a2}:
              match s:
                case Dsc.Space{+n, +k, +p, +a}:
                  %cds.put(r, Dsc.Space{n, k, p, a}, x) : {Dsc.put.sel(String.eq(n2, n), Dsc.Grp{Dsc.Space{n2, k2, p2, a2}, its}, x, r, Dsc.put(r, Dsc.Space{n, k, p, a}, x)) == CodemodeDescribe.join_at(String.eq(n2, n), Dsc.Grp{Dsc.Space{n2, k2, p2, a2}, its}, x, r, _) : List<&2, Dsc.Grp>}
                  cds.join_at(String.eq(n2, n), Dsc.Grp{Dsc.Space{n2, k2, p2, a2}, its}, x, r, Dsc.put(r, Dsc.Space{n, k, p, a}, x))

# the groups are the spec's, from any start
def cds.groups(xs: List<&2, Dsc.Tagged>, +plain: List<&2, Dsc.Item>, +named: List<&2, Dsc.Grp>) -> {Dsc.groups(xs, (plain, named)) == CodemodeDescribe.groups_spec(xs, (plain, named)) : List<&2, Dsc.Item> & List<&2, Dsc.Grp>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case Dsc.Tagged{m, +it}:
          match m:
            case None{}:
              cds.groups(r, List.append(&2, Dsc.Item, plain, [it]), named)
            case Some{+s}:
              %cds.put(named, s, it) : {Dsc.groups(r, (plain, Dsc.put(named, s, it))) == CodemodeDescribe.groups_spec(r, (plain, _)) : List<&2, Dsc.Item> & List<&2, Dsc.Grp>}
              cds.groups(r, plain, Dsc.put(named, s, it))

# ---- the order of the groups ----

def cds.tie(e: Bool, n1: String, k1: String, p1: String, a1: String, n2: String, k2: String, p2: String, a2: String) -> {Dsc.before.tie(e, Dsc.Space{n1, k1, p1, a1}, Dsc.Space{n2, k2, p2, a2}) == CodemodeDescribe.first_tie(e, Dsc.Space{n1, k1, p1, a1}, Dsc.Space{n2, k2, p2, a2}) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def cds.before(a: Dsc.Space, b: Dsc.Space) -> {Dsc.before(a, b) == CodemodeDescribe.first_spec(a, b) : Bool}:
  match a:
    case Dsc.Space{n1, +k1, p1, a1}:
      match b:
        case Dsc.Space{n2, +k2, p2, a2}:
          cds.tie(String.eq(k1, k2), n1, k1, p1, a1, n2, k2, p2, a2)

def cds.sorted_at(b: Bool, g: Dsc.Grp, h: Dsc.Grp, t: List<&2, Dsc.Grp>, l: List<&2, Dsc.Grp>) -> {Dsc.insert.sel(b, g, h, t, l) == CodemodeDescribe.sorted_at(b, g, h, t, l) : List<&2, Dsc.Grp>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cds.insert(g: Dsc.Grp, gs: List<&2, Dsc.Grp>) -> {Dsc.insert(g, gs) == CodemodeDescribe.sorted_put(g, gs) : List<&2, Dsc.Grp>}:
  match g:
    case Dsc.Grp{+sg, +ig}:
      match gs:
        case Nil{}:
          {==}
        case Con{h, +t}:
          match h:
            case Dsc.Grp{+sh, +ih}:
              %cds.before(sh, sg) : {Dsc.insert.sel(Bool.not(Dsc.before(sh, sg)), Dsc.Grp{sg, ig}, Dsc.Grp{sh, ih}, t, Dsc.insert(Dsc.Grp{sg, ig}, t)) == CodemodeDescribe.sorted_at(Bool.not(_), Dsc.Grp{sg, ig}, Dsc.Grp{sh, ih}, t, CodemodeDescribe.sorted_put(Dsc.Grp{sg, ig}, t)) : List<&2, Dsc.Grp>}
              %cds.insert(Dsc.Grp{sg, ig}, t) : {Dsc.insert.sel(Bool.not(Dsc.before(sh, sg)), Dsc.Grp{sg, ig}, Dsc.Grp{sh, ih}, t, Dsc.insert(Dsc.Grp{sg, ig}, t)) == CodemodeDescribe.sorted_at(Bool.not(Dsc.before(sh, sg)), Dsc.Grp{sg, ig}, Dsc.Grp{sh, ih}, t, _) : List<&2, Dsc.Grp>}
              cds.sorted_at(Bool.not(Dsc.before(sh, sg)), Dsc.Grp{sg, ig}, Dsc.Grp{sh, ih}, t, Dsc.insert(Dsc.Grp{sg, ig}, t))

# the groups' order is the spec's
def cds.order(gs: List<&2, Dsc.Grp>) -> {Dsc.order(gs) == CodemodeDescribe.sorted_spec(gs) : List<&2, Dsc.Grp>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      %cds.order(r) : {Dsc.insert(g, Dsc.order(r)) == CodemodeDescribe.sorted_put(g, _) : List<&2, Dsc.Grp>}
      cds.insert(g, Dsc.order(r))

def cds.items(gs: List<&2, Dsc.Grp>) -> {Dsc.grps_items(gs) == CodemodeDescribe.items_of(gs) : List<&2, List<&2, Dsc.Item>>}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Dsc.Grp{s, +its}:
          %cds.items(r) : {its <> Dsc.grps_items(r) == its <> _ : List<&2, List<&2, Dsc.Item>>}
          {==}

# ---- the tools shown ----

def cds.tool_name(ts: List<&2, Dsc.Tool>, n: Nat) -> {Dsc.tool_name(ts, n) == CodemodeDescribe.tool_name_spec(ts, n) : String}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, r}:
      match t:
        case Dsc.Tool{name, z}:
          match n:
            case 0n:
              {==}
            case 1n+k:
              cds.tool_name(r, k)

def cds.names(+ts: List<&2, Dsc.Tool>, xs: List<&2, Nat>) -> {Dsc.names(ts, xs) == CodemodeDescribe.names_spec(ts, xs) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %cds.tool_name(ts, x) : {Dsc.tool_name(ts, x) <> Dsc.names(ts, r) == _ <> CodemodeDescribe.names_spec(ts, r) : List<&2, String>}
      %cds.names(ts, r) : {Dsc.tool_name(ts, x) <> Dsc.names(ts, r) == Dsc.tool_name(ts, x) <> _ : List<&2, String>}
      {==}

def cds.member(ns: List<&2, String>, +n: String) -> {Dsc.member(ns, n) == CodemodeDescribe.has_name(ns, n) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %cds.member(r, n) : {Bool.or(String.eq(x, n), Dsc.member(r, n)) == Bool.or(String.eq(x, n), _) : Bool}
      {==}

def cds.shown_at(b: Bool, x: Dsc.Item, r: List<&2, Dsc.Item>) -> {Dsc.visible.sel(b, x, r) == CodemodeDescribe.shown_at(b, x, r) : List<&2, Dsc.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cds.visible(xs: List<&2, Dsc.Item>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> {Dsc.visible(xs, ts, shown) == CodemodeDescribe.shown_spec(xs, ts, shown) : List<&2, Dsc.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case Dsc.Item{+t, +c}:
          %cds.tool_name(ts, t) : {Dsc.visible.sel(Dsc.member(shown, Dsc.tool_name(ts, t)), Dsc.Item{t, c}, Dsc.visible(r, ts, shown)) == CodemodeDescribe.shown_at(CodemodeDescribe.has_name(shown, _), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          %cds.member(shown, Dsc.tool_name(ts, t)) : {Dsc.visible.sel(Dsc.member(shown, Dsc.tool_name(ts, t)), Dsc.Item{t, c}, Dsc.visible(r, ts, shown)) == CodemodeDescribe.shown_at(_, Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          %cds.visible(r, ts, shown) : {Dsc.visible.sel(Dsc.member(shown, Dsc.tool_name(ts, t)), Dsc.Item{t, c}, Dsc.visible(r, ts, shown)) == CodemodeDescribe.shown_at(Dsc.member(shown, Dsc.tool_name(ts, t)), Dsc.Item{t, c}, _) : List<&2, Dsc.Item>}
          cds.shown_at(Dsc.member(shown, Dsc.tool_name(ts, t)), Dsc.Item{t, c}, Dsc.visible(r, ts, shown))

def cds.sects(xs: List<&2, Dsc.Item>) -> {Dsc.sects(xs) == CodemodeDescribe.sects_spec(xs) : List<&2, Dsc.Part>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case Dsc.Item{t, c}:
          %cds.sects(r) : {Dsc.Sect{t} <> Dsc.sects(r) == Dsc.Sect{t} <> _ : List<&2, Dsc.Part>}
          {==}

# ---- headings and blocks ----

def cds.none(c: Bool) -> {Dsc.listing.none(c) == CodemodeDescribe.marker_at(False{}, c) : String}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def cds.listing(b: Bool, +v: Nat) -> {Dsc.listing.sel(b, v) == CodemodeDescribe.marker_at(b, Nat.is_eq(v, 0n)) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      cds.none(Nat.is_eq(v, 0n))

def cds.about(e: Bool, a: String) -> {Dsc.about.sel(e, a) == CodemodeDescribe.about_at(e, a) : String}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# a namespace's heading is the spec's
def cds.heading(s: Dsc.Space, +v: Nat, +n: Nat) -> {Dsc.heading(s, v, n) == CodemodeDescribe.heading_spec(s, v, n) : String}:
  match s:
    case Dsc.Space{+name, k, p, +about}:
      %cds.listing(Nat.is_eq(v, n), v) : {String.concat(["## ", name, Dsc.listing(v, n), Dsc.about.sel(String.is_empty(about), about)]) == String.concat(["## ", name, _, CodemodeDescribe.about_at(String.is_empty(about), about)]) : String}
      %cds.about(String.is_empty(about), about) : {String.concat(["## ", name, Dsc.listing(v, n), Dsc.about.sel(String.is_empty(about), about)]) == String.concat(["## ", name, Dsc.listing(v, n), _]) : String}
      {==}

def cds.head(b: Bool) -> {Dsc.plain.head(b) == CodemodeDescribe.plain_head(b) : List<&2, Dsc.Part>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the blocks of the tools of no namespace are the spec's
def cds.plain(xs: List<&2, Dsc.Item>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> {Dsc.plain.blocks(xs, ts, shown) == CodemodeDescribe.plain_spec(xs, ts, shown) : List<&2, Dsc.Part>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +vs = Dsc.visible(Con{x, r}, ts, shown)
      %cds.visible(Con{x, r}, ts, shown) : {List.append(&2, Dsc.Part, Dsc.plain.head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))), Dsc.sects(vs)) == List.append(&2, Dsc.Part, CodemodeDescribe.plain_head(Nat.is_eq(List.length(&2, Dsc.Item, _), List.length(&2, Dsc.Item, Con{x, r}))), CodemodeDescribe.sects_spec(_)) : List<&2, Dsc.Part>}
      %cds.head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))) : {List.append(&2, Dsc.Part, Dsc.plain.head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))), Dsc.sects(vs)) == List.append(&2, Dsc.Part, _, CodemodeDescribe.sects_spec(vs)) : List<&2, Dsc.Part>}
      %cds.sects(vs) : {List.append(&2, Dsc.Part, Dsc.plain.head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))), Dsc.sects(vs)) == List.append(&2, Dsc.Part, Dsc.plain.head(Nat.is_eq(List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, Con{x, r}))), _) : List<&2, Dsc.Part>}
      {==}

# the blocks of the namespace groups are the spec's
def cds.named(gs: List<&2, Dsc.Grp>, +ts: List<&2, Dsc.Tool>, +shown: List<&2, String>) -> {Dsc.grps.blocks(gs, ts, shown) == CodemodeDescribe.named_spec(gs, ts, shown) : List<&2, Dsc.Part>}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +r}:
      match g:
        case Dsc.Grp{+s, +its}:
          +vs = Dsc.visible(its, ts, shown)
          %cds.visible(its, ts, shown) : {List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> Dsc.sects(vs), Dsc.grps.blocks(r, ts, shown)) == List.append(&2, Dsc.Part, Dsc.Lit{CodemodeDescribe.heading_spec(s, List.length(&2, Dsc.Item, _), List.length(&2, Dsc.Item, its))} <> CodemodeDescribe.sects_spec(_), CodemodeDescribe.named_spec(r, ts, shown)) : List<&2, Dsc.Part>}
          %cds.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its)) : {List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> Dsc.sects(vs), Dsc.grps.blocks(r, ts, shown)) == List.append(&2, Dsc.Part, Dsc.Lit{_} <> CodemodeDescribe.sects_spec(vs), CodemodeDescribe.named_spec(r, ts, shown)) : List<&2, Dsc.Part>}
          %cds.sects(vs) : {List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> Dsc.sects(vs), Dsc.grps.blocks(r, ts, shown)) == List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> _, CodemodeDescribe.named_spec(r, ts, shown)) : List<&2, Dsc.Part>}
          %cds.named(r, ts, shown) : {List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> Dsc.sects(vs), Dsc.grps.blocks(r, ts, shown)) == List.append(&2, Dsc.Part, Dsc.Lit{Dsc.heading(s, List.length(&2, Dsc.Item, vs), List.length(&2, Dsc.Item, its))} <> Dsc.sects(vs), _) : List<&2, Dsc.Part>}
          {==}

def cds.sep_rest(xs: List<&2, Dsc.Part>) -> {Dsc.sep.rest(xs) == CodemodeDescribe.blank_rest(xs) : List<&2, Dsc.Part>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %cds.sep_rest(r) : {Dsc.Lit{"\n\n"} <> x <> Dsc.sep.rest(r) == Dsc.Lit{"\n\n"} <> x <> _ : List<&2, Dsc.Part>}
      {==}

# the joint is the spec's
def cds.sep(xs: List<&2, Dsc.Part>) -> {Dsc.sep(xs) == CodemodeDescribe.joined_spec(xs) : List<&2, Dsc.Part>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %cds.sep_rest(r) : {x <> Dsc.sep.rest(r) == x <> _ : List<&2, Dsc.Part>}
      {==}

# ---- the section ----

def cds.of(pg: List<&2, Dsc.Item> & List<&2, Dsc.Grp>, +ts: List<&2, Dsc.Tool>, +budget: Nat) -> {Dsc.section.of(pg, ts, budget) == CodemodeDescribe.section_of(pg, ts, budget) : List<&2, Dsc.Part>}:
  match pg:
    case (+plain, +named):
      +gs = Dsc.order(named)
      +ws = {plain <> Dsc.grps_items(gs) : List<&2, List<&2, Dsc.Item>>}
      +shown = Dsc.names(ts, Dsc.select(ws, budget))
      +blocks = {Dsc.Lit{Dsc.intro_text()} <> List.append(&2, Dsc.Part, Dsc.plain.blocks(plain, ts, shown), Dsc.grps.blocks(gs, ts, shown)) : List<&2, Dsc.Part>}
      %cds.order(named) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, CodemodeDescribe.plain_spec(plain, ts, CodemodeDescribe.names_spec(ts, CodemodeDescribe.select_spec(plain <> CodemodeDescribe.items_of(_), budget))), CodemodeDescribe.named_spec(_, ts, CodemodeDescribe.names_spec(ts, CodemodeDescribe.select_spec(plain <> CodemodeDescribe.items_of(_), budget))))) : List<&2, Dsc.Part>}
      %cds.items(gs) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, CodemodeDescribe.plain_spec(plain, ts, CodemodeDescribe.names_spec(ts, CodemodeDescribe.select_spec(plain <> _, budget))), CodemodeDescribe.named_spec(gs, ts, CodemodeDescribe.names_spec(ts, CodemodeDescribe.select_spec(plain <> _, budget))))) : List<&2, Dsc.Part>}
      %LACd.cdsel.select(ws, budget) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, CodemodeDescribe.plain_spec(plain, ts, CodemodeDescribe.names_spec(ts, _)), CodemodeDescribe.named_spec(gs, ts, CodemodeDescribe.names_spec(ts, _)))) : List<&2, Dsc.Part>}
      %cds.names(ts, Dsc.select(ws, budget)) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, CodemodeDescribe.plain_spec(plain, ts, _), CodemodeDescribe.named_spec(gs, ts, _))) : List<&2, Dsc.Part>}
      %cds.plain(plain, ts, shown) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, _, CodemodeDescribe.named_spec(gs, ts, shown))) : List<&2, Dsc.Part>}
      %cds.named(gs, ts, shown) : {Dsc.sep(blocks) == CodemodeDescribe.joined_spec(Dsc.Lit{"Tools scripts can call (`await tools.<name>(args)`):"} <> List.append(&2, Dsc.Part, Dsc.plain.blocks(plain, ts, shown), _)) : List<&2, Dsc.Part>}
      cds.sep(blocks)

# the section is the spec's
def cds.section(+ts: List<&2, Dsc.Tool>, +ss: List<&2, Dsc.Space>, +budget: Nat) -> {Dsc.section(ts, ss, budget) == CodemodeDescribe.section_spec(ts, ss, budget) : Maybe<&2, List<&2, Dsc.Part>>}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +r}:
      +ps = Dsc.prefixes(ss)
      %cds.prefixes(ss) : {Some{Dsc.section.of(Dsc.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), ([], [])), Con{t, r}, budget)} == Some{CodemodeDescribe.section_of(CodemodeDescribe.groups_spec(CodemodeDescribe.tags_spec(Con{t, r}, ss, _, 0n), ([], [])), Con{t, r}, budget)} : Maybe<&2, List<&2, Dsc.Part>>}
      %cds.tagged(Con{t, r}, ss, ps, 0n) : {Some{Dsc.section.of(Dsc.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), ([], [])), Con{t, r}, budget)} == Some{CodemodeDescribe.section_of(CodemodeDescribe.groups_spec(_, ([], [])), Con{t, r}, budget)} : Maybe<&2, List<&2, Dsc.Part>>}
      %cds.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), [], []) : {Some{Dsc.section.of(Dsc.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), ([], [])), Con{t, r}, budget)} == Some{CodemodeDescribe.section_of(_, Con{t, r}, budget)} : Maybe<&2, List<&2, Dsc.Part>>}
      %cds.of(Dsc.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), ([], [])), Con{t, r}, budget) : {Some{Dsc.section.of(Dsc.groups(Dsc.tagged(Con{t, r}, ss, ps, 0n), ([], [])), Con{t, r}, budget)} == Some{_} : Maybe<&2, List<&2, Dsc.Part>>}
      {==}
