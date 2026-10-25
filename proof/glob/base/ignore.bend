# eukhe: lemmas of the proofs of glob_rules and glob_ignored: the code's
# rule lists, per-rule decisions and entry paths are the spec's.

import Base
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../bend/glob/queries.bend as GQuery
import ../../../laws/glob.bend as Glob
import ./query.bend as GQ

# Rules
# -----

def gr.rules(ks: List<&2, Nat>, +o: GItems.Opts, +ps: List<&2, String>, +ss: List<&2, String>) -> {GQuery.rules(ks, o, ps, ss) == Glob.sp_rules(ks, o, ps, ss) : List<&2, Bool>}:
  match ks:
    case Nil{}:
      {==}
    case +k <> +r:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GQuery.compile(o, List.take(&2, String, ps, k)), Glob.sp_compile(o, List.take(&2, String, ps, k)), GQ.gq.compile(o, List.take(&2, String, ps, k))) : {GQuery.hit_any(ss, _) <> GQuery.rules(r, o, List.drop(&2, String, ps, k), ss) == Glob.sp_rules(k <> r, o, ps, ss) : List<&2, Bool>}
      %Equal.sym(Bool, GQuery.hit_any(ss, Glob.sp_compile(o, List.take(&2, String, ps, k))), Glob.sp_hit(ss, Glob.sp_compile(o, List.take(&2, String, ps, k))), GQ.gq.hit(ss, Glob.sp_compile(o, List.take(&2, String, ps, k)))) : {_ <> GQuery.rules(r, o, List.drop(&2, String, ps, k), ss) == Glob.sp_rules(k <> r, o, ps, ss) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, GQuery.rules(r, o, List.drop(&2, String, ps, k), ss), Glob.sp_rules(r, o, List.drop(&2, String, ps, k), ss), gr.rules(r, o, List.drop(&2, String, ps, k), ss)) : {Glob.sp_hit(ss, Glob.sp_compile(o, List.take(&2, String, ps, k))) <> _ == Glob.sp_rules(k <> r, o, ps, ss) : List<&2, Bool>}
      {==}

# Ignore rules
# ------------

def gi2.after.k(b: Bool, t: String, r: List<&2, String>) -> {GQuery.after_slashes.k(b, t, r) == Glob.sp_suffixes.k(b, t, r) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gi2.after(s: String) -> {GQuery.after_slashes(s) == Glob.sp_suffixes(s) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          %Equal.sym(List<&2, String>, GQuery.after_slashes(t), Glob.sp_suffixes(t), gi2.after(t)) : {GQuery.after_slashes.k(U32.is_eq(x, 47), t, _) == Glob.sp_suffixes(SCon{Chr{x}, t}) : List<&2, String>}
          gi2.after.k(U32.is_eq(x, 47), t, Glob.sp_suffixes(t))

# a glob rule's match is the spec's
def gi2.gh(a: Bool, +o: GItems.Opts, +path: String, +p: String) -> {GQuery.glob_hit(a, path, GQuery.compile(o, [p])) == Glob.sp_glob_rule.hit(a, path, Glob.sp_compile(o, [p])) : Bool}:
  match a:
    case True{}:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GQuery.compile(o, [p]), Glob.sp_compile(o, [p]), GQ.gq.compile(o, [p])) : {GMatch.any_full(GItems.bytes(path), _) == Glob.sp_glob_rule.hit(True{}, path, Glob.sp_compile(o, [p])) : Bool}
      GQ.gq.any(GItems.bytes(path), Glob.sp_compile(o, [p]))
    case False{}:
      %Equal.sym(List<&2, List<&2, GItems.It>>, GQuery.compile(o, [p]), Glob.sp_compile(o, [p]), GQ.gq.compile(o, [p])) : {GQuery.hit_any(path <> GQuery.after_slashes(path), _) == Glob.sp_glob_rule.hit(False{}, path, Glob.sp_compile(o, [p])) : Bool}
      %Equal.sym(List<&2, String>, GQuery.after_slashes(path), Glob.sp_suffixes(path), gi2.after(path)) : {GQuery.hit_any(path <> _, Glob.sp_compile(o, [p])) == Glob.sp_glob_rule.hit(False{}, path, Glob.sp_compile(o, [p])) : Bool}
      GQ.gq.hit(path <> Glob.sp_suffixes(path), Glob.sp_compile(o, [p]))

def gi2.hit(h: Bool, n: Bool, +r: Bool, +s: Bool, ih: {r == s : Bool}) -> {GQuery.decide.hit(h, n, u => r) == Glob.sp_decide.k(Glob.sp_glob_rule.k(False{}, h, n), s) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      ih

def gi2.glob(skip: Bool, xs: List<&2, List<&2, GItems.It>>, a: Bool, n: Bool, +path: String, +hv: Bool, eh: {GQuery.glob_hit(a, path, xs) == hv : Bool}, +r: Bool, +s: Bool, ih: {r == s : Bool}) -> {GQuery.decide.glob(skip, xs, a, n, path, u => r) == Glob.sp_decide.k(Glob.sp_glob_rule.k(skip, hv, n), s) : Bool}:
  match skip:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, GQuery.glob_hit(a, path, xs), hv, eh) : {GQuery.decide.hit(_, n, u => r) == Glob.sp_decide.k(Glob.sp_glob_rule.k(False{}, hv, n), s) : Bool}
      gi2.hit(hv, n, r, s, ih)

def gi2.all(b: Bool, +r: Bool, +s: Bool, ih: {r == s : Bool}) -> {GQuery.decide.all(b, u => r) == Glob.sp_decide.k(Glob.sp_prefix_rule(b), s) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def gi2.g(-c: Nat, +d: Bool, +a: Bool, +n: Bool, +p: String, +path: String, +dir: Bool, +r: Bool, +s: Bool, ih: {r == s : Bool}) -> {GQuery.decide.glob(Bool.and(d, Bool.not(dir)), GQuery.compile(GItems.Opts{True{}, False{}}, [p]), a, n, path, u => r) == Glob.sp_decide.k(Glob.sp_glob_rule.k(Bool.and(d, Bool.not(dir)), Glob.sp_glob_rule.hit(a, path, Glob.sp_compile(GItems.Opts{True{}, False{}}, [p])), n), s) : Bool}:
  gi2.glob(Bool.and(d, Bool.not(dir)), GQuery.compile(GItems.Opts{True{}, False{}}, [p]), a, n, path, Glob.sp_glob_rule.hit(a, path, Glob.sp_compile(GItems.Opts{True{}, False{}}, [p])), gi2.gh(a, GItems.Opts{True{}, False{}}, path, p), r, s, ih)

# one rule's decision is the spec's
def gi2.rule(c: Nat, +p: String, +path: String, +dir: Bool, +r: Bool, +s: Bool, ih: {r == s : Bool}) -> {GQuery.decide.r(GQuery.ir(p, c), path, dir, u => r) == Glob.sp_decide.k(Glob.sp_rule(c, p, path, dir), s) : Bool}:
  match c:
    case 0n:
      gi2.g(0n, False{}, False{}, False{}, p, path, dir, r, s, ih)
    case 1n:
      gi2.g(1n, False{}, True{}, False{}, p, path, dir, r, s, ih)
    case 2n:
      gi2.g(2n, False{}, False{}, True{}, p, path, dir, r, s, ih)
    case 3n:
      gi2.g(3n, False{}, True{}, True{}, p, path, dir, r, s, ih)
    case 4n:
      gi2.g(4n, True{}, False{}, False{}, p, path, dir, r, s, ih)
    case 5n:
      gi2.g(5n, True{}, True{}, False{}, p, path, dir, r, s, ih)
    case 6n:
      gi2.g(6n, True{}, False{}, True{}, p, path, dir, r, s, ih)
    case 7n:
      gi2.g(7n, True{}, True{}, True{}, p, path, dir, r, s, ih)
    case 8n:
      gi2.all(String.starts_with(path, p), r, s, ih)
    case 9n+k:
      ih

# the code's rules, from the spec's (text, code) pairs
def gi2.pmap(rs: List<&2, Glob.SpRule>) -> List<&2, GQuery.IR>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Glob.SpRule{p, c}:
          GQuery.ir(p, c) <> gi2.pmap(t)

def gi2.decide(rs: List<&2, Glob.SpRule>, +path: String, +dir: Bool) -> {GQuery.decide(gi2.pmap(rs), path, dir) == Glob.sp_decide(rs, path, dir) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case Glob.SpRule{+p, +c}:
          gi2.rule(c, p, path, dir, GQuery.decide(gi2.pmap(t), path, dir), Glob.sp_decide(t, path, dir), gi2.decide(t, path, dir))

def gi2.irs(ps: List<&2, String>, cs: List<&2, Nat>, acc: List<&2, Glob.SpRule>) -> {GQuery.irs(ps, cs, gi2.pmap(acc)) == gi2.pmap(Glob.sp_pairs(ps, cs, acc)) : List<&2, GQuery.IR>}:
  match ps cs:
    case Nil{} cs:
      {==}
    case p <> pr Nil{}:
      {==}
    case p <> pr c <> cr:
      gi2.irs(pr, cr, Glob.SpRule{p, c} <> acc)

def gi2.last(+x: U32, b: Bool) -> {GQuery.split_dir.last(Chr{x}, b) == (Glob.sp_path.last(Chr{x}, b), b) : String & Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gi2.one(c: Char) -> {GQuery.split_dir(SCon{c, SNil{}}) == (Glob.sp_path(SCon{c, SNil{}}), Glob.sp_dir(SCon{c, SNil{}})) : String & Bool}:
  match c:
    case Chr{+x}:
      gi2.last(x, U32.is_eq(x, 47))

# an entry's path and kind are the spec's
def gi2.split(e: String) -> {GQuery.split_dir(e) == (Glob.sp_path(e), Glob.sp_dir(e)) : String & Bool}:
  match e:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      match t:
        case SNil{}:
          gi2.one(c)
        case SCon{+x, +u}:
          %Equal.sym(String & Bool, GQuery.split_dir(SCon{x, u}), (Glob.sp_path(SCon{x, u}), Glob.sp_dir(SCon{x, u})), gi2.split(SCon{x, u})) : {GQuery.split_dir.cons(c, _) == (Glob.sp_path(SCon{c, SCon{x, u}}), Glob.sp_dir(SCon{c, SCon{x, u}})) : String & Bool}
          {==}

def gi2.go(es: List<&2, String>, +ps: List<&2, String>, +cs: List<&2, Nat>) -> {GQuery.ignored.go(es, gi2.pmap(Glob.sp_pairs(ps, cs, Nil{}))) == Glob.sp_ignored(ps, cs, es) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +r:
      +prs = Glob.sp_pairs(ps, cs, Nil{})
      %Equal.sym(String & Bool, GQuery.split_dir(e), (Glob.sp_path(e), Glob.sp_dir(e)), gi2.split(e)) : {GQuery.ignored.e(gi2.pmap(prs), _) <> GQuery.ignored.go(r, gi2.pmap(prs)) == Glob.sp_ignored(ps, cs, e <> r) : List<&2, Bool>}
      %Equal.sym(Bool, GQuery.decide(gi2.pmap(prs), Glob.sp_path(e), Glob.sp_dir(e)), Glob.sp_decide(prs, Glob.sp_path(e), Glob.sp_dir(e)), gi2.decide(prs, Glob.sp_path(e), Glob.sp_dir(e))) : {_ <> GQuery.ignored.go(r, gi2.pmap(prs)) == Glob.sp_ignored(ps, cs, e <> r) : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, GQuery.ignored.go(r, gi2.pmap(prs)), Glob.sp_ignored(ps, cs, r), gi2.go(r, ps, cs)) : {Glob.sp_decide(prs, Glob.sp_path(e), Glob.sp_dir(e)) <> _ == Glob.sp_ignored(ps, cs, e <> r) : List<&2, Bool>}
      {==}

# the code's ignore query is the spec's
def gi2.ignored(+ps: List<&2, String>, +cs: List<&2, Nat>, es: List<&2, String>) -> {GQuery.ignored(ps, cs, es) == Glob.sp_ignored(ps, cs, es) : List<&2, Bool>}:
  %Equal.sym(List<&2, GQuery.IR>, GQuery.irs(ps, cs, Nil{}), gi2.pmap(Glob.sp_pairs(ps, cs, Nil{})), gi2.irs(ps, cs, Nil{})) : {GQuery.ignored.go(es, _) == Glob.sp_ignored(ps, cs, es) : List<&2, Bool>}
  gi2.go(es, ps, cs)
