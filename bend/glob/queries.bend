# glob/queries: what Rust asks of bend/glob/ through bend/ffi_glob.bend:
# a pattern's error, pattern groups and rules against texts, gitignore
# style ignore rules over a directory listing, and the model allowlist.

import Base
import ./parse.bend as GParse
import ./items.bend as GItems
import ./match.bend as GMatch

# Queries
# -------

# the error of a pattern globset refuses
def check.r(r: Result<&2, &2, GParse.Err, GParse.Glob>) -> Maybe<&2, GParse.Err>:
  match r:
    case Fail{e}:
      Some{e}
    case Done{g}:
      None{}

def check(p: String) -> Maybe<&2, GParse.Err>:
  check.r(GParse.parse(p))

def compile.r(+o: GItems.Opts, r: Result<&2, &2, GParse.Err, GParse.Glob>, rest: List<&2, List<&2, GItems.It>>) -> List<&2, List<&2, GItems.It>>:
  match r:
    case Fail{e}:
      rest
    case Done{g}:
      List.append(&2, List<&2, GItems.It>, GItems.items(o, g), rest)

# the alternatives of every pattern globset accepts (a refused pattern
# matches nothing)
def compile(+o: GItems.Opts, ps: List<&2, String>) -> List<&2, List<&2, GItems.It>>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> r:
      compile.r(o, GParse.parse(p), compile(o, r))

# whether one of the texts ss matches one of the alternatives xs
def hit_any(ss: List<&2, String>, +xs: List<&2, List<&2, GItems.It>>) -> Bool:
  match ss:
    case Nil{}:
      False{}
    case s <> r:
      GMatch.or_else(GMatch.any_full(GItems.bytes(s), xs), u => hit_any(r, xs))

# the texts ss in groups of the sizes ks, in order: whether a pattern
# matches a text of each group (a group past the texts takes those left)
def groups(ks: List<&2, Nat>, +xs: List<&2, List<&2, GItems.It>>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      hit_any(List.take(&2, String, ss, k), xs) <> groups(r, xs, List.drop(&2, String, ss, k))

# each group of texts: whether one of the patterns ps matches one of its
# texts
def match_groups(+o: GItems.Opts, ps: List<&2, String>, ss: List<&2, String>, ks: List<&2, Nat>) -> List<&2, Bool>:
  groups(ks, compile(o, ps), ss)

# per rule of the sizes ks (its patterns in order: a rule past the
# patterns takes those left), whether one of its patterns matches one of
# the texts ss
def rules(ks: List<&2, Nat>, +o: GItems.Opts, +ps: List<&2, String>, +ss: List<&2, String>) -> List<&2, Bool>:
  match ks:
    case Nil{}:
      Nil{}
    case +k <> r:
      hit_any(ss, compile(o, List.take(&2, String, ps, k))) <> rules(r, o, List.drop(&2, String, ps, k), ss)

# Ignore rules
# ------------

# an ignore rule: a glob (literal separators) matched against the whole
# path (anchored) or any of its `/`-suffixes, negated (a match keeps the
# path), for directories only; every path under a prefix; a rule of an
# unknown code, which decides nothing
type IR is Data:
  IGlob{xs: List<&2, List<&2, GItems.It>>, anchored: Bool, negated: Bool, dir_only: Bool}
  IAll{prefix: String}
  ISkip{}

# the rule of the text p and the code c: 0-7 a glob (bit 1 anchored,
# bit 2 negated, bit 4 directories only), 8 every path under the prefix
# p, any other nothing
def ir(p: String, c: Nat) -> IR:
  match c:
    case 0n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), False{}, False{}, False{}}
    case 1n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), True{}, False{}, False{}}
    case 2n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), False{}, True{}, False{}}
    case 3n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), True{}, True{}, False{}}
    case 4n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), False{}, False{}, True{}}
    case 5n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), True{}, False{}, True{}}
    case 6n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), False{}, True{}, True{}}
    case 7n:
      IGlob{compile(GItems.Opts{True{}, False{}}, [p]), True{}, True{}, True{}}
    case 8n:
      IAll{p}
    case 9n+k:
      ISkip{}

# the rules of the texts ps and codes cs, paired in order (the shorter
# list ends them), last rule first
def irs(ps: List<&2, String>, cs: List<&2, Nat>, acc: List<&2, IR>) -> List<&2, IR>:
  match ps cs:
    case Nil{} cs:
      acc
    case p <> pr Nil{}:
      acc
    case p <> pr c <> cr:
      irs(pr, cr, ir(p, c) <> acc)

# the texts after each `/` of s
def after_slashes.k(sl: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match sl:
    case True{}:
      t <> rest
    case False{}:
      rest

def after_slashes(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, +t}:
      after_slashes.k(GParse.is_c(c, 47), t, after_slashes(t))

def glob_hit(anchored: Bool, +path: String, +xs: List<&2, List<&2, GItems.It>>) -> Bool:
  match anchored:
    case True{}:
      GMatch.any_full(GItems.bytes(path), xs)
    case False{}:
      hit_any(path <> after_slashes(path), xs)

def decide.hit(hit: Bool, negated: Bool, rest: Unit -> Bool) -> Bool:
  match hit:
    case True{}:
      Bool.not(negated)
    case False{}:
      rest(Unit{})

def decide.glob(skip: Bool, xs: List<&2, List<&2, GItems.It>>, anchored: Bool, negated: Bool, +path: String, rest: Unit -> Bool) -> Bool:
  match skip:
    case True{}:
      rest(Unit{})
    case False{}:
      decide.hit(glob_hit(anchored, path, xs), negated, rest)

def decide.all(under: Bool, rest: Unit -> Bool) -> Bool:
  match under:
    case True{}:
      True{}
    case False{}:
      rest(Unit{})

# rule r on the path (dir: a directory), else the rules after it
def decide.r(r: IR, +path: String, +dir: Bool, rest: Unit -> Bool) -> Bool:
  match r:
    case IGlob{xs, anchored, negated, dir_only}:
      decide.glob(Bool.and(dir_only, Bool.not(dir)), xs, anchored, negated, path, rest)
    case IAll{prefix}:
      decide.all(String.starts_with(path, prefix), rest)
    case ISkip{}:
      rest(Unit{})

# whether the rules rs (last rule first) ignore the path: the first rule
# that decides it, else not ignored
def decide(rs: List<&2, IR>, +path: String, +dir: Bool) -> Bool:
  match rs:
    case Nil{}:
      False{}
    case r <> t:
      decide.r(r, path, dir, u => decide(t, path, dir))

def split_dir.cons(+c: Char, r: String & Bool) -> String & Bool:
  match r:
    case (t, d):
      (SCon{c, t}, d)

def split_dir.last(+c: Char, sl: Bool) -> String & Bool:
  match sl:
    case True{}:
      ("", True{})
    case False{}:
      (SCon{c, SNil{}}, False{})

# an entry as Rust sends it: its path, a directory's with one `/` after
# it; the path without that `/`, and whether it is a directory
def split_dir(s: String) -> String & Bool:
  match s:
    case SNil{}:
      ("", False{})
    case SCon{+c, t}:
      match t:
        case SNil{}:
          split_dir.last(c, GParse.is_c(c, 47))
        case SCon{x, u}:
          split_dir.cons(c, split_dir(SCon{x, u}))

def ignored.e(+rs: List<&2, IR>, e: String & Bool) -> Bool:
  match e:
    case (+path, +dir):
      decide(rs, path, dir)

def ignored.go(es: List<&2, String>, +rs: List<&2, IR>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> r:
      ignored.e(rs, split_dir(e)) <> ignored.go(r, rs)

# for each entry, whether the ignore rules (the texts ps with the codes cs,
# in the order the ignore files give them) ignore it
def ignored(ps: List<&2, String>, cs: List<&2, Nat>, es: List<&2, String>) -> List<&2, Bool>:
  ignored.go(es, irs(ps, cs, Nil{}))

# The model allowlist
# -------------------

# Unicode White_Space (Rust `char::is_whitespace`, `str::trim`)
def ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def trim_start.k(w: Bool, c: Char, t: String, rest: String) -> String:
  match w:
    case True{}:
      rest
    case False{}:
      SCon{c, t}

# s without its leading white space
def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_start.k(ws(c), c, t, trim_start(t))

# s without its leading and trailing white space (Rust `str::trim`)
def trim(s: String) -> String:
  String.reverse(trim_start(String.reverse(trim_start(s))))

# s holds `*`, `?` or `[` (the allowlist's test for a glob)
def wild(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.or(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), U32.is_eq(x, 91))), wild(t))

def after_slash.k(sl: Bool, t: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match sl:
    case True{}:
      Some{t}
    case False{}:
      rest

# the text after the first `/` of s
def after_slash(s: String) -> Maybe<&2, String>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, +t}:
      after_slash.k(GParse.is_c(c, 47), t, after_slash(t))

def bare.k(s: String, m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      s
    case Some{t}:
      t

# the bare id of a selector: the text after its first `/` (prime-inference
# ids carry more slashes); the selector itself with none
def bare(+s: String) -> String:
  bare.k(s, after_slash(s))

def allow.g(r: Result<&2, &2, GParse.Err, GParse.Glob>, +sel: String) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{g}:
      hit_any([sel, bare(sel)], GItems.items(GItems.Opts{False{}, False{}}, g))

def allow.w(w: Bool, +sel: String, +p: String) -> Bool:
  match w:
    case True{}:
      allow.g(GParse.parse(p), sel)
    case False{}:
      Bool.or(String.eq(p, sel), String.eq(p, bare(sel)))

def allow.e(e: Bool, +sel: String, +p: String) -> Bool:
  match e:
    case True{}:
      False{}
    case False{}:
      allow.w(wild(p), sel, p)

def allow.t(+sel: String, +p: String) -> Bool:
  allow.e(String.is_empty(p), sel, p)

# one allowlist pattern (lowercase) against a selector (lowercase): its
# trimmed text, blank never matches; with `*`, `?` or `[` a glob (globset
# defaults: `*` crosses `/`; a refused glob matches nothing) of the whole
# selector or its bare id; else equal to one of them
def allow1(+sel: String, p: String) -> Bool:
  allow.t(sel, trim(p))

# whether the allowlist ps allows the selector (an empty list allows
# nothing)
def allowed(+sel: String, ps: List<&2, String>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> r:
      GMatch.or_else(allow1(sel, p), u => allowed(sel, r))
