# eukhe: lemmas of the proofs of the ignore laws: the code's rule of a text
# and a code decides as sp_ig_rule (ig.rule), an entry spelled by
# sp_entry splits back to its path and kind (ig.split), the rule list
# grows last first (ig.irs_snoc) and pairs only the first texts and codes
# (ig.irs_take).

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../bend/glob/queries.bend as GQuery
import ../../../laws/glob.bend as Glob
import ./logic.bend as GL
import ./seq.bend as GS
import ./query.bend as GQ

# Rules
# -----

def ig.o() -> GItems.Opts:
  GItems.Opts{True{}, False{}}

# the text after some `/` of path: the search over those texts
def ig.after_k(+p: String, b: Bool, +t: String, -y: Bool, ih: {Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(t)) == y : Bool}) -> {Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes.k(b, t, GQuery.after_slashes(t))) == Bool.or(Bool.and(b, Glob.sp_ig_hit(p, t)), y) : Bool}:
  match b:
    case True{}:
      %ih : {Bool.or(Bool.or(Glob.sp_ig_hit(p, t), False{}), Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(t))) == Bool.or(Glob.sp_ig_hit(p, t), _) : Bool}
      %Equal.sym(Bool, Bool.or(Glob.sp_ig_hit(p, t), False{}), Glob.sp_ig_hit(p, t), GL.gl.or_false(Glob.sp_ig_hit(p, t))) : {Bool.or(_, Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(t))) == Bool.or(Glob.sp_ig_hit(p, t), Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(t))) : Bool}
      {==}
    case False{}:
      ih

def ig.after(+p: String, s: String) -> {Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(s)) == Glob.sp_ig_after(p, s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      match c:
        case Chr{+x}:
          ig.after_k(p, U32.is_eq(x, 47), t, Glob.sp_ig_after(p, t), ig.after(p, t))

# a glob rule's match: the whole path, or (not anchored) a text after `/`
def ig.hit(a: Bool, +p: String, +path: String) -> {GQuery.glob_hit(a, path, GQuery.compile(ig.o(), [p])) == Bool.or(Glob.sp_ig_hit(p, path), Bool.and(Bool.not(a), Glob.sp_ig_after(p, path))) : Bool}:
  match a:
    case True{}:
      +xs = GQuery.compile(ig.o(), [p])
      +bs = GItems.bytes(path)
      Equal.trans(Bool, GMatch.any_full(bs, xs), GS.gs.OL(bs, xs), Bool.or(Glob.sp_ig_hit(p, path), False{}), GS.gs.af(bs, xs), GQ.gq.pat(ig.o(), [p], path))
    case False{}:
      +xs = GQuery.compile(ig.o(), [p])
      +sx = {path <> GQuery.after_slashes(path) : List<&2, String>}
      %Equal.sym(Bool, GQuery.hit_any(sx, xs), Glob.sp_texts_hit(ig.o(), [p], sx), GQ.gq.texts(ig.o(), [p], sx)) : {_ == Bool.or(Glob.sp_ig_hit(p, path), Glob.sp_ig_after(p, path)) : Bool}
      %ig.after(p, path) : {Bool.or(Bool.or(Glob.sp_ig_hit(p, path), False{}), Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(path))) == Bool.or(Glob.sp_ig_hit(p, path), _) : Bool}
      %Equal.sym(Bool, Bool.or(Glob.sp_ig_hit(p, path), False{}), Glob.sp_ig_hit(p, path), GL.gl.or_false(Glob.sp_ig_hit(p, path))) : {Bool.or(_, Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(path))) == Bool.or(Glob.sp_ig_hit(p, path), Glob.sp_texts_hit(ig.o(), [p], GQuery.after_slashes(path))) : Bool}
      {==}

def ig.dh(x: Bool, n: Bool, +r: Bool) -> {GQuery.decide.hit(x, n, u => r) == Glob.sp_ig_pick(Glob.sp_ig_some(x, Bool.not(n)), r) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# a glob rule of anchored bit a, negated bit n, directory-only bit d
def ig.glob(+p: String, +path: String, d: Bool, dir: Bool, +r: Bool, +a: Bool, +n: Bool) -> {GQuery.decide.glob(Bool.and(d, Bool.not(dir)), GQuery.compile(ig.o(), [p]), a, n, path, u => r) == Glob.sp_ig_pick(Glob.sp_ig_some(Bool.and(Bool.not(Bool.and(d, Bool.not(dir))), Bool.or(Glob.sp_ig_hit(p, path), Bool.and(Bool.not(a), Glob.sp_ig_after(p, path)))), Bool.not(n)), r) : Bool}:
  match d dir:
    case False{} dir:
      +xs = GQuery.compile(ig.o(), [p])
      +h = Bool.or(Glob.sp_ig_hit(p, path), Bool.and(Bool.not(a), Glob.sp_ig_after(p, path)))
      %Equal.sym(Bool, GQuery.glob_hit(a, path, xs), h, ig.hit(a, p, path)) : {GQuery.decide.hit(_, n, u => r) == Glob.sp_ig_pick(Glob.sp_ig_some(h, Bool.not(n)), r) : Bool}
      ig.dh(h, n, r)
    case True{} True{}:
      +xs = GQuery.compile(ig.o(), [p])
      +h = Bool.or(Glob.sp_ig_hit(p, path), Bool.and(Bool.not(a), Glob.sp_ig_after(p, path)))
      %Equal.sym(Bool, GQuery.glob_hit(a, path, xs), h, ig.hit(a, p, path)) : {GQuery.decide.hit(_, n, u => r) == Glob.sp_ig_pick(Glob.sp_ig_some(h, Bool.not(n)), r) : Bool}
      ig.dh(h, n, r)
    case True{} False{}:
      {==}

def ig.all(x: Bool, +r: Bool) -> {GQuery.decide.all(x, u => r) == Glob.sp_ig_pick(Glob.sp_ig_some(x, True{}), r) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's rule of (p, c) decides as sp_ig_rule
def ig.rule(+p: String, c: Nat, +path: String, +dir: Bool, +r: Bool) -> {GQuery.decide.r(GQuery.ir(p, c), path, dir, u => r) == Glob.sp_ig_pick(Glob.sp_ig_rule(p, c, path, dir), r) : Bool}:
  match c:
    case 0n:
      ig.glob(p, path, False{}, dir, r, False{}, False{})
    case 1n:
      ig.glob(p, path, False{}, dir, r, True{}, False{})
    case 2n:
      ig.glob(p, path, False{}, dir, r, False{}, True{})
    case 3n:
      ig.glob(p, path, False{}, dir, r, True{}, True{})
    case 4n:
      ig.glob(p, path, True{}, dir, r, False{}, False{})
    case 5n:
      ig.glob(p, path, True{}, dir, r, True{}, False{})
    case 6n:
      ig.glob(p, path, True{}, dir, r, False{}, True{})
    case 7n:
      ig.glob(p, path, True{}, dir, r, True{}, True{})
    case 8n:
      ig.all(String.starts_with(path, p), r)
    case 9n+k:
      {==}

# Entries
# -------

def ig.last(c: Char, e: {U32.is_eq(Char.to_u32(c), 47) == False{} : Bool}) -> {GQuery.split_dir(SCon{c, SNil{}}) == (SCon{c, SNil{}}, False{}) : String & Bool}:
  match c:
    case Chr{x}:
      %Equal.sym(Bool, U32.is_eq(x, 47), False{}, e) : {GQuery.split_dir.last(Chr{x}, _) == (SCon{Chr{x}, SNil{}}, False{}) : String & Bool}
      {==}

# a file's path (not ending with `/`) splits back whole
def ig.file(s: String, h: {Glob.sp_ends_slash(s) == False{} : Bool}) -> {GQuery.split_dir(s) == (s, False{}) : String & Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      match t:
        case SNil{}:
          ig.last(c, h)
        case SCon{+d, +u}:
          %Equal.sym(String & Bool, GQuery.split_dir(SCon{d, u}), (SCon{d, u}, False{}), ig.file(SCon{d, u}, h)) : {GQuery.split_dir.cons(c, _) == (SCon{c, SCon{d, u}}, False{}) : String & Bool}
          {==}

# a directory's path then `/` splits back to the path
def ig.dir(s: String) -> {GQuery.split_dir(String.append(s, "/")) == (s, True{}) : String & Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      match t:
        case SNil{}:
          {==}
        case SCon{+d, +u}:
          %Equal.sym(String & Bool, GQuery.split_dir(String.append(SCon{d, u}, "/")), (SCon{d, u}, True{}), ig.dir(SCon{d, u})) : {GQuery.split_dir.cons(c, _) == (SCon{c, SCon{d, u}}, True{}) : String & Bool}
          {==}

def ig.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      GL.gl.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ig.split(+path: String, dir: Bool, h: {Bool.or(dir, Bool.not(Glob.sp_ends_slash(path))) == True{} : Bool}) -> {GQuery.split_dir(Glob.sp_entry(path, dir)) == (path, dir) : String & Bool}:
  match dir:
    case True{}:
      ig.dir(path)
    case False{}:
      ig.file(path, ig.not_t(Glob.sp_ends_slash(path), h))

# Rule lists
# ----------

def ig.irs_take(ps: List<&2, String>, cs: List<&2, Nat>, acc: List<&2, GQuery.IR>) -> {GQuery.irs(ps, cs, acc) == GQuery.irs(List.take(&2, String, ps, List.length(&2, Nat, cs)), List.take(&2, Nat, cs, List.length(&2, String, ps)), acc) : List<&2, GQuery.IR>}:
  match ps cs:
    case Nil{} cs:
      {==}
    case p <> pr Nil{}:
      {==}
    case +p <> pr +c <> cr:
      ig.irs_take(pr, cr, GQuery.ir(p, c) <> acc)

def ig.irs_snoc(ps: List<&2, String>, cs: List<&2, Nat>, +p: String, +c: Nat, acc: List<&2, GQuery.IR>, h: {Nat.is_eq(List.length(&2, String, ps), List.length(&2, Nat, cs)) == True{} : Bool}) -> {GQuery.irs(List.append(&2, String, ps, [p]), List.append(&2, Nat, cs, [c]), acc) == GQuery.ir(p, c) <> GQuery.irs(ps, cs, acc) : List<&2, GQuery.IR>}:
  match ps cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} c2 <> cr:
      GL.gl.ft({GQuery.irs(List.append(&2, String, Nil{}, [p]), List.append(&2, Nat, c2 <> cr, [c]), acc) == GQuery.ir(p, c) <> GQuery.irs(Nil{}, c2 <> cr, acc) : List<&2, GQuery.IR>}, h)
    case p2 <> pr Nil{}:
      GL.gl.ft({GQuery.irs(List.append(&2, String, p2 <> pr, [p]), List.append(&2, Nat, Nil{}, [c]), acc) == GQuery.ir(p, c) <> GQuery.irs(p2 <> pr, Nil{}, acc) : List<&2, GQuery.IR>}, h)
    case +p2 <> pr +c2 <> cr:
      ig.irs_snoc(pr, cr, p, c, GQuery.ir(p2, c2) <> acc, h)
