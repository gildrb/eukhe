# eukhe.com's Neovim: path facts for the Oil laws
# ===============================================
#
# B.Path.dir/up/child against Laws.Spec.dir/parent/base, how a path
# splits into its folder and name, and which folders Tgt.real admits.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/text.bend as Tx
import ../buffers/real.bend as Rb
import ../screen/base.bend as Sb
import ./str.bend as Str

# Strings
# -------

def PathL.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(t, SNil{}), t, PathL.app_nil(t))

def PathL.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Equal.cong(String, String, x => SCon{h, x}, String.append(String.append(t, b), c), String.append(t, String.append(b, c)), PathL.app_assoc(t, b, c))

# reversing onto a is reversing, then a
def PathL.rev_go(s: String, a: String) -> {String.reverse.go(s, a) == String.append(String.reverse.go(s, SNil{}), a) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      +x = String.reverse.go(t, SNil{})
      +e1 = PathL.rev_go(t, SCon{h, a})
      +e2 = PathL.rev_go(t, SCon{h, SNil{}})
      +e3 = Equal.cong(String, String, y => String.append(y, a), String.reverse.go(t, SCon{h, SNil{}}), String.append(x, SCon{h, SNil{}}), e2)
      +e4 = Equal.trans(String, String.append(String.reverse.go(t, SCon{h, SNil{}}), a), String.append(String.append(x, SCon{h, SNil{}}), a), String.append(x, SCon{h, a}), e3, PathL.app_assoc(x, SCon{h, SNil{}}, a))
      Equal.trans(String, String.reverse.go(t, SCon{h, a}), String.append(x, SCon{h, a}), String.append(String.reverse.go(t, SCon{h, SNil{}}), a), e1, Equal.sym(String, String.append(String.reverse.go(t, SCon{h, SNil{}}), a), String.append(x, SCon{h, a}), e4))

def PathL.rev_snoc(+acc: String, +h: Char) -> {String.reverse(SCon{h, acc}) == String.append(String.reverse(acc), SCon{h, SNil{}}) : String}:
  PathL.rev_go(acc, SCon{h, SNil{}})

# when over two equal pairs of branches
def PathL.when_cong(b: Bool, -x1: String, -y1: String, -x2: String, -y2: String, e1: {x1 == y1 : String}, e2: {x2 == y2 : String}) -> {X.Bool.when(String, b, u => x1, u => x2) == X.Bool.when(String, b, u => y1, u => y2) : String}:
  match b:
    case True{}:
      e2
    case False{}:
      e1

# Path.dir
# --------

def PathL.dir_case(b: Bool, -t: String, -l1: String, -l2: String, -m: String, -n: String, -c: String, +e: {m == n : String}, ih_f: {l1 == Laws.Spec.dir.go(t, m, c) : String}, ih_t: {l2 == Laws.Spec.dir.go(t, m, m) : String}) -> {X.Bool.when(String, b, u => l1, u => l2) == Laws.Spec.dir.go(t, n, Bool.pick(String, b, n, c)) : String}:
  match b:
    case True{}:
      %e : {l2 == Laws.Spec.dir.go(t, _, _) : String}
      ih_t
    case False{}:
      %e : {l1 == Laws.Spec.dir.go(t, _, c) : String}
      ih_f

# Path.dir.go keeps reversed what Spec.dir.go keeps forward
def PathL.dir_go(s: String, +acc: String, +cut: String) -> {B.Path.dir.go(s, acc, cut) == Laws.Spec.dir.go(s, String.reverse(acc), String.reverse(cut)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      PathL.dir_case(Char.is_eq(h, '/'), t, B.Path.dir.go(t, SCon{h, acc}, cut), B.Path.dir.go(t, SCon{h, acc}, SCon{h, acc}), String.reverse(SCon{h, acc}), String.append(String.reverse(acc), SCon{h, SNil{}}), String.reverse(cut), PathL.rev_snoc(acc, h), PathL.dir_go(t, SCon{h, acc}, cut), PathL.dir_go(t, SCon{h, acc}, SCon{h, acc}))

def Path.dir_eq(+s: String) -> {B.Path.dir(s) == Laws.Spec.dir(s) : String}:
  PathL.dir_go(s, SNil{}, SNil{})

# Path.up
# -------

def PathL.up_cons(+h: Char, t: String, +acc: String, +cut: String, ih_f: {B.Path.up.go(t, SCon{h, acc}, cut) == B.Path.dir.go(Laws.Spec.drop_last(t), SCon{h, acc}, cut) : String}, ih_t: {B.Path.up.go(t, SCon{h, acc}, SCon{h, acc}) == B.Path.dir.go(Laws.Spec.drop_last(t), SCon{h, acc}, SCon{h, acc}) : String}) -> {B.Path.up.go(SCon{h, t}, acc, cut) == B.Path.dir.go(Laws.Spec.drop_last(SCon{h, t}), acc, cut) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{d, u}:
      PathL.when_cong(Char.is_eq(h, '/'), B.Path.up.go(SCon{d, u}, SCon{h, acc}, cut), B.Path.dir.go(Laws.Spec.drop_last(SCon{d, u}), SCon{h, acc}, cut), B.Path.up.go(SCon{d, u}, SCon{h, acc}, SCon{h, acc}), B.Path.dir.go(Laws.Spec.drop_last(SCon{d, u}), SCon{h, acc}, SCon{h, acc}), ih_f, ih_t)

# Path.up.go is Path.dir.go one character short
def PathL.up_go(s: String, +acc: String, +cut: String) -> {B.Path.up.go(s, acc, cut) == B.Path.dir.go(Laws.Spec.drop_last(s), acc, cut) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      PathL.up_cons(h, t, acc, cut, PathL.up_go(t, SCon{h, acc}, cut), PathL.up_go(t, SCon{h, acc}, SCon{h, acc}))

def Path.up_eq(+s: String) -> {B.Path.up(s) == Laws.Spec.parent(s) : String}:
  Equal.trans(String, B.Path.up(s), B.Path.dir(Laws.Spec.drop_last(s)), Laws.Spec.dir(Laws.Spec.drop_last(s)), PathL.up_go(s, SNil{}, SNil{}), Path.dir_eq(Laws.Spec.drop_last(s)))

# Folder and name
# ---------------

def PathL.split_inv(b: Bool, +seen: String, best: String, -cur: String, +h: Char, e: {seen == String.append(best, cur) : String}) -> {String.append(seen, SCon{h, SNil{}}) == String.append(Bool.pick(String, b, String.append(seen, SCon{h, SNil{}}), best), Bool.pick(String, b, "", String.append(cur, SCon{h, SNil{}}))) : String}:
  match b:
    case True{}:
      Equal.sym(String, String.append(String.append(seen, SCon{h, SNil{}}), SNil{}), String.append(seen, SCon{h, SNil{}}), PathL.app_nil(String.append(seen, SCon{h, SNil{}})))
    case False{}:
      %Equal.sym(String, seen, String.append(best, cur), e) : {String.append(_, SCon{h, SNil{}}) == String.append(best, String.append(cur, SCon{h, SNil{}})) : String}
      PathL.app_assoc(best, cur, SCon{h, SNil{}})

def PathL.split_go(s: String, +seen: String, +best: String, +cur: String, e: {seen == String.append(best, cur) : String}) -> {String.append(seen, s) == String.append(Laws.Spec.dir.go(s, seen, best), Laws.Spec.base.go(s, cur)) : String}:
  match s:
    case SNil{}:
      %Equal.sym(String, String.append(seen, SNil{}), seen, PathL.app_nil(seen)) : {_ == String.append(best, cur) : String}
      e
    case SCon{+h, +t}:
      +next = String.append(seen, SCon{h, SNil{}})
      +ih = PathL.split_go(t, next, Bool.pick(String, Char.is_eq(h, '/'), next, best), Bool.pick(String, Char.is_eq(h, '/'), "", String.append(cur, SCon{h, SNil{}})), PathL.split_inv(Char.is_eq(h, '/'), seen, best, cur, h, e))
      %PathL.app_assoc(seen, SCon{h, SNil{}}, t) : {_ == String.append(Laws.Spec.dir.go(t, next, Bool.pick(String, Char.is_eq(h, '/'), next, best)), Laws.Spec.base.go(t, Bool.pick(String, Char.is_eq(h, '/'), "", String.append(cur, SCon{h, SNil{}})))) : String}
      ih

def Path.dir_split(+s: String) -> {s == String.append(Laws.Spec.dir(s), Laws.Spec.base(s)) : String}:
  PathL.split_go(s, "", "", "", {==})

# Folder shape
# ------------

def PathL.is_dir_cons(c: Char, xt: String, +h: Char, ih: {B.Path.is_dir(String.append(xt, SCon{h, SNil{}})) == Char.is_eq(h, '/') : Bool}) -> {B.Path.is_dir(String.append(SCon{c, xt}, SCon{h, SNil{}})) == Char.is_eq(h, '/') : Bool}:
  match xt:
    case SNil{}:
      {==}
    case SCon{d, u}:
      ih

# a string ending in c is a folder's when c is "/"
def PathL.is_dir_snoc(x: String, +h: Char) -> {B.Path.is_dir(String.append(x, SCon{h, SNil{}})) == Char.is_eq(h, '/') : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{c, +xt}:
      PathL.is_dir_cons(c, xt, h, PathL.is_dir_snoc(xt, h))

def PathL.Shape(s: String) -> Type:
  {Bool.or(String.is_empty(s), B.Path.is_dir(s)) == True{} : Bool}

def PathL.shape_pick(+h: Char, +seen: String, -best: String, b: Bool, e: {Char.is_eq(h, '/') == b : Bool}, hb: PathL.Shape(best)) -> PathL.Shape(Bool.pick(String, b, String.append(seen, SCon{h, SNil{}}), best)):
  match b:
    case True{}:
      L.Or.r(String.is_empty(String.append(seen, SCon{h, SNil{}})), B.Path.is_dir(String.append(seen, SCon{h, SNil{}})), Equal.trans(Bool, B.Path.is_dir(String.append(seen, SCon{h, SNil{}})), Char.is_eq(h, '/'), True{}, PathL.is_dir_snoc(seen, h), e))
    case False{}:
      hb

def PathL.shape_go(s: String, +seen: String, +best: String, hb: PathL.Shape(best)) -> PathL.Shape(Laws.Spec.dir.go(s, seen, best)):
  match s:
    case SNil{}:
      hb
    case SCon{+h, t}:
      PathL.shape_go(t, String.append(seen, SCon{h, SNil{}}), Bool.pick(String, Char.is_eq(h, '/'), String.append(seen, SCon{h, SNil{}}), best), PathL.shape_pick(h, seen, best, Char.is_eq(h, '/'), {==}, hb))

def Path.dir_shape(+s: String) -> {Bool.or(String.is_empty(Laws.Spec.dir(s)), B.Path.is_dir(Laws.Spec.dir(s))) == True{} : Bool}:
  PathL.shape_go(s, "", "", {==})

# Parent
# ------

# the last character of s, as a string; "" for none
def PathL.last(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{h, SNil{}}:
      SCon{h, SNil{}}
    case SCon{h, t}:
      PathL.last(t)

def PathL.drop_cons(+h: Char, t: String, ih: {t == String.append(Laws.Spec.drop_last(t), PathL.last(t)) : String}) -> {SCon{h, t} == String.append(Laws.Spec.drop_last(SCon{h, t}), PathL.last(SCon{h, t})) : String}:
  match t:
    case SNil{}:
      {==}
    case SCon{d, u}:
      Equal.cong(String, String, x => SCon{h, x}, SCon{d, u}, String.append(Laws.Spec.drop_last(SCon{d, u}), PathL.last(SCon{d, u})), ih)

def PathL.drop_split(s: String) -> {s == String.append(Laws.Spec.drop_last(s), PathL.last(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      PathL.drop_cons(h, t, PathL.drop_split(t))

# what follows the parent folder in s
def Path.parent_rest(+s: String) -> String:
  String.append(Laws.Spec.base(Laws.Spec.drop_last(s)), PathL.last(s))

def Path.parent_split(+s: String) -> {s == String.append(Laws.Spec.parent(s), Path.parent_rest(s)) : String}:
  +dl = Laws.Spec.drop_last(s)
  +l = PathL.last(s)
  +e1 = Equal.cong(String, String, x => String.append(x, l), dl, String.append(Laws.Spec.dir(dl), Laws.Spec.base(dl)), Path.dir_split(dl))
  +e2 = Equal.trans(String, String.append(dl, l), String.append(String.append(Laws.Spec.dir(dl), Laws.Spec.base(dl)), l), String.append(Laws.Spec.dir(dl), String.append(Laws.Spec.base(dl), l)), e1, PathL.app_assoc(Laws.Spec.dir(dl), Laws.Spec.base(dl), l))
  Equal.trans(String, s, String.append(dl, l), String.append(Laws.Spec.dir(dl), String.append(Laws.Spec.base(dl), l)), PathL.drop_split(s), e2)

# Prefixes
# --------

def PathL.char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{+x}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, Tx.U32.cmp_refl(x)) : {Cmp.is_eq(_) == True{} : Bool}
      {==}

def PathL.spec_self(a: String, -r: String) -> {Laws.Spec.prefix(a, String.append(a, r)) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{+x, at}:
      L.And.intro(Char.is_eq(x, x), Laws.Spec.prefix(at, String.append(at, r)), PathL.char_refl(x), PathL.spec_self(at, r))

def Path.prefix_self(+a: String, +r: String) -> {X.Text.prefix(a, String.append(a, r)) == True{} : Bool}:
  Equal.trans(Bool, X.Text.prefix(a, String.append(a, r)), Laws.Spec.prefix(a, String.append(a, r)), True{}, Rb.Prefix.eq(a, String.append(a, r)), PathL.spec_self(a, r))

def PathL.spec_cut(a: String, -r: String, p: String, +h: {Laws.Spec.prefix(String.append(a, r), p) == True{} : Bool}) -> {Laws.Spec.prefix(a, p) == True{} : Bool}:
  match a p:
    case SNil{} _:
      {==}
    case SCon{x, at} SNil{}:
      L.Bool.false_true({Laws.Spec.prefix(SCon{x, at}, SNil{}) == True{} : Bool}, h)
    case SCon{+x, at} SCon{+y, pt}:
      L.And.intro(Char.is_eq(x, y), Laws.Spec.prefix(at, pt), L.And.l(Char.is_eq(x, y), Laws.Spec.prefix(String.append(at, r), pt), h), PathL.spec_cut(at, r, pt, L.And.r(Char.is_eq(x, y), Laws.Spec.prefix(String.append(at, r), pt), h)))

def PathL.prefix_cut(+a: String, +r: String, +p: String, h: {X.Text.prefix(String.append(a, r), p) == True{} : Bool}) -> {X.Text.prefix(a, p) == True{} : Bool}:
  +hs = Equal.trans(Bool, Laws.Spec.prefix(String.append(a, r), p), X.Text.prefix(String.append(a, r), p), True{}, Equal.sym(Bool, X.Text.prefix(String.append(a, r), p), Laws.Spec.prefix(String.append(a, r), p), Rb.Prefix.eq(String.append(a, r), p)), h)
  Equal.trans(Bool, X.Text.prefix(a, p), Laws.Spec.prefix(a, p), True{}, Rb.Prefix.eq(a, p), PathL.spec_cut(a, r, p, hs))

def PathL.or_imp(x: Bool, x2: Bool, -y: Bool, -y2: Bool, h: {Bool.or(x, y) == True{} : Bool}, fx: {x == True{} : Bool} -> {x2 == True{} : Bool}, fy: {y == True{} : Bool} -> {y2 == True{} : Bool}) -> {Bool.or(x2, y2) == True{} : Bool}:
  match x:
    case True{}:
      L.Or.l(x2, y2, fx({==}))
    case False{}:
      L.Or.r(x2, y2, fy(h))

def Path.under_cut(+a: String, +r: String, fs: List<&2, T.Buf>, h: {B.Files.under(String.append(a, r), fs) == True{} : Bool}) -> {B.Files.under(a, fs) == True{} : Bool}:
  match fs:
    case Nil{}:
      L.Bool.false_true({False{} == True{} : Bool}, h)
    case Con{T.Buf{+p, ls}, t}:
      PathL.or_imp(X.Text.prefix(String.append(a, r), p), X.Text.prefix(a, p), B.Files.under(String.append(a, r), t), B.Files.under(a, t), h, hx => PathL.prefix_cut(a, r, p, hx), hy => Path.under_cut(a, r, t, hy))

# Child
# -----

# whether s holds no "/"
def PathL.slashless(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{h, t}:
      Bool.and(Bool.not(Char.is_eq(h, '/')), PathL.slashless(t))

def PathL.none_step(b: Bool, -i: Nat, -x: Maybe<&2, Nat>, h1: {Bool.not(b) == True{} : Bool}, hx: {x == None{} : Maybe<&2, Nat>}) -> {X.Bool.when(Maybe<&2, Nat>, b, u => x, u => Some{i}) == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      L.Bool.false_true({Some{i} == None{} : Maybe<&2, Nat>}, h1)
    case False{}:
      hx

def PathL.slash_none(x: String, -n: Nat, -i: Nat, +h: {PathL.slashless(x) == True{} : Bool}) -> {B.Path.slash.go(x, n, i) == None{} : Maybe<&2, Nat>}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      PathL.none_step(Char.is_eq(c, '/'), i, B.Path.slash.go(t, n, 1n+i), L.And.l(Bool.not(Char.is_eq(c, '/')), PathL.slashless(t), h), PathL.slash_none(t, n, 1n+i, L.And.r(Bool.not(Char.is_eq(c, '/')), PathL.slashless(t), h)))

def PathL.sl_snoc(cur: String, +h: Char, +hc: {PathL.slashless(cur) == True{} : Bool}, e: {Char.is_eq(h, '/') == False{} : Bool}) -> {PathL.slashless(String.append(cur, SCon{h, SNil{}})) == True{} : Bool}:
  match cur:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(h, '/'), False{}, e) : {Bool.and(Bool.not(_), True{}) == True{} : Bool}
      {==}
    case SCon{+c, ct}:
      L.And.intro(Bool.not(Char.is_eq(c, '/')), PathL.slashless(String.append(ct, SCon{h, SNil{}})), L.And.l(Bool.not(Char.is_eq(c, '/')), PathL.slashless(ct), hc), PathL.sl_snoc(ct, h, L.And.r(Bool.not(Char.is_eq(c, '/')), PathL.slashless(ct), hc), e))

def PathL.sl_pick(+h: Char, cur: String, b: Bool, e: {Char.is_eq(h, '/') == b : Bool}, hc: {PathL.slashless(cur) == True{} : Bool}) -> {PathL.slashless(Bool.pick(String, b, "", String.append(cur, SCon{h, SNil{}}))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      PathL.sl_snoc(cur, h, hc, e)

def PathL.sl_base(s: String, +cur: String, hc: {PathL.slashless(cur) == True{} : Bool}) -> {PathL.slashless(Laws.Spec.base.go(s, cur)) == True{} : Bool}:
  match s:
    case SNil{}:
      hc
    case SCon{+h, t}:
      PathL.sl_base(t, Bool.pick(String, Char.is_eq(h, '/'), "", String.append(cur, SCon{h, SNil{}})), PathL.sl_pick(h, cur, Char.is_eq(h, '/'), {==}, hc))

# a path's name holds no "/", so Path.name keeps it whole
def PathL.name_base(+s: String) -> {B.Path.name(Laws.Spec.base(s)) == Laws.Spec.base(s) : String}:
  +e = PathL.slash_none(Laws.Spec.base(s), 0n, 0n, PathL.sl_base(s, "", {==}))
  %Equal.sym(Maybe<&2, Nat>, B.Path.slash.go(Laws.Spec.base(s), 0n, 0n), None{}, e) : {B.Path.name.at(Laws.Spec.base(s), _) == Laws.Spec.base(s) : String}
  {==}

def PathL.drop_zero(s: String) -> {X.Text.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def PathL.drop_app(d: String, +b: String) -> {X.Text.drop(String.append(d, b), Laws.Spec.chars(d)) == b : String}:
  match d:
    case SNil{}:
      PathL.drop_zero(b)
    case SCon{c, dt}:
      PathL.drop_app(dt, b)

def PathL.child_app(+d: String, +b: String, hb: {B.Path.name(b) == b : String}) -> {B.Path.child(d, String.append(d, b)) == b : String}:
  %Equal.sym(Bool, X.Text.prefix(d, String.append(d, b)), True{}, Path.prefix_self(d, b)) : {X.Bool.when(String, _, u => "", u => B.Path.name(X.Text.drop(String.append(d, b), X.Text.len(d)))) == b : String}
  %Equal.sym(Nat, X.Text.len(d), Laws.Spec.chars(d), Tx.Chars.eq(d)) : {B.Path.name(X.Text.drop(String.append(d, b), _)) == b : String}
  %Equal.sym(String, X.Text.drop(String.append(d, b), Laws.Spec.chars(d)), b, PathL.drop_app(d, b)) : {B.Path.name(_) == b : String}
  hb

def Path.child_base(+s: String) -> {B.Path.child(B.Path.dir(s), s) == Laws.Spec.base(s) : String}:
  %Equal.sym(String, B.Path.dir(s), Laws.Spec.dir(s), Path.dir_eq(s)) : {B.Path.child(_, s) == Laws.Spec.base(s) : String}
  %Equal.sym(String, s, String.append(Laws.Spec.dir(s), Laws.Spec.base(s)), Path.dir_split(s)) : {B.Path.child(Laws.Spec.dir(s), _) == Laws.Spec.base(s) : String}
  PathL.child_app(Laws.Spec.dir(s), Laws.Spec.base(s), PathL.name_base(s))

# Real folders
# ------------

def PathL.len_go(fs: List<&2, T.Buf>, +acc: Nat) -> {B.Files.len.go(fs, acc) == Nat.add(acc, Laws.Spec.nfiles(fs)) : Nat}:
  match fs:
    case Nil{}:
      L.Nat.add_zero(acc)
    case Con{b, t}:
      Equal.trans(Nat, B.Files.len.go(t, 1n+acc), 1n+Nat.add(acc, Laws.Spec.nfiles(t)), Nat.add(acc, 1n+Laws.Spec.nfiles(t)), PathL.len_go(t, 1n+acc), L.Nat.add_succ(acc, Laws.Spec.nfiles(t)))

def PathL.max_zero(n: Nat) -> {Nat.max(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a folder that is a prefix of the path of a file held holds a file
def PathL.under_mem(fs: List<&2, T.Buf>, i: Nat, +d: String, hi: {Nat.is_lt(i, Laws.Spec.nfiles(fs)) == True{} : Bool}, hp: {X.Text.prefix(d, B.Buf.path(B.Files.at(fs, i))) == True{} : Bool}) -> {B.Files.under(d, fs) == True{} : Bool}:
  match fs i:
    case Nil{} 0n:
      L.Bool.false_true({B.Files.under(d, Nil{}) == True{} : Bool}, hi)
    case Nil{} 1n+q:
      L.Bool.false_true({B.Files.under(d, Nil{}) == True{} : Bool}, hi)
    case Con{T.Buf{+p, ls}, t} 0n:
      L.Or.l(X.Text.prefix(d, p), B.Files.under(d, t), hp)
    case Con{T.Buf{p, ls}, t} 1n+q:
      L.Or.r(X.Text.prefix(d, p), B.Files.under(d, t), PathL.under_mem(t, q, d, hi, hp))

def PathL.real_shape(x: Bool, y: Bool, -z: Bool, h: {Bool.or(x, y) == True{} : Bool}, hz: {z == True{} : Bool}) -> {Bool.or(x, Bool.and(y, z)) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      L.And.intro(y, z, h, hz)

def PathL.prefix_dir(+p: String) -> {X.Text.prefix(Laws.Spec.dir(p), p) == True{} : Bool}:
  %Equal.sym(String, p, String.append(Laws.Spec.dir(p), Laws.Spec.base(p)), Path.dir_split(p)) : {X.Text.prefix(Laws.Spec.dir(p), _) == True{} : Bool}
  Path.prefix_self(Laws.Spec.dir(p), Laws.Spec.base(p))

def PathL.real_dir_go(+fs: List<&2, T.Buf>, +i: Nat, hi: {Nat.is_lt(i, Laws.Spec.nfiles(fs)) == True{} : Bool}) -> {B.Tgt.real(fs, T.Dir{B.Path.dir(B.Buf.path(B.Files.at(fs, i)))}) == True{} : Bool}:
  +p = B.Buf.path(B.Files.at(fs, i))
  +d = Laws.Spec.dir(p)
  %Equal.sym(String, B.Path.dir(p), d, Path.dir_eq(p)) : {B.Tgt.real(fs, T.Dir{_}) == True{} : Bool}
  PathL.real_shape(String.is_empty(d), B.Path.is_dir(d), B.Files.under(d, fs), Path.dir_shape(p), PathL.under_mem(fs, i, d, hi, PathL.prefix_dir(p)))

def Path.real_dir(+fs: List<&2, T.Buf>, +i: Nat, hi: {Nat.is_lt(i, Nat.max(B.Files.len(fs), 1n)) == True{} : Bool}) -> {B.Tgt.real(fs, T.Dir{B.Path.dir(B.Buf.path(B.Files.at(fs, i)))}) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      +n = Laws.Spec.nfiles(t)
      +e1 = Equal.cong(Nat, Nat, x => Nat.max(x, 1n), B.Files.len.go(t, 1n), 1n+n, PathL.len_go(t, 1n))
      +e2 = Equal.trans(Nat, Nat.max(B.Files.len.go(t, 1n), 1n), Nat.max(1n+n, 1n), 1n+n, e1, Equal.cong(Nat, Nat, x => 1n+x, Nat.max(n, 0n), n, PathL.max_zero(n)))
      +hi2 = Equal.trans(Bool, Nat.is_lt(i, 1n+n), Nat.is_lt(i, Nat.max(B.Files.len.go(t, 1n), 1n)), True{}, Equal.cong(Nat, Bool, x => Nat.is_lt(i, x), 1n+n, Nat.max(B.Files.len.go(t, 1n), 1n), Equal.sym(Nat, Nat.max(B.Files.len.go(t, 1n), 1n), 1n+n, e2)), hi)
      PathL.real_dir_go(Con{b, t}, i, hi2)

def Path.real_up(+fs: List<&2, T.Buf>, +path: String, h: {B.Tgt.real(fs, T.Dir{path}) == True{} : Bool}) -> {B.Tgt.real(fs, T.Dir{B.Path.up(path)}) == True{} : Bool}:
  match path:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +s = {SCon{c, t} : String}
      +par = Laws.Spec.parent(s)
      +rest = Path.parent_rest(s)
      +hu = L.And.r(B.Path.is_dir(s), B.Files.under(s, fs), h)
      +hu2 = Equal.trans(Bool, B.Files.under(String.append(par, rest), fs), B.Files.under(s, fs), True{}, Equal.cong(String, Bool, x => B.Files.under(x, fs), String.append(par, rest), s, Equal.sym(String, s, String.append(par, rest), Path.parent_split(s))), hu)
      %Equal.sym(String, B.Path.up(s), par, Path.up_eq(s)) : {B.Tgt.real(fs, T.Dir{_}) == True{} : Bool}
      PathL.real_shape(String.is_empty(par), B.Path.is_dir(par), B.Files.under(par, fs), Path.dir_shape(Laws.Spec.drop_last(s)), Path.under_cut(par, rest, fs, hu2))

# Spec.path
# ---------

def Path.spec_path(fs: List<&2, T.Buf>, i: Nat) -> {B.Buf.path(B.Files.at(Sb.Files.norm(fs), i)) == Laws.Spec.path(fs, i) : String}:
  match fs i:
    case Nil{} _:
      {==}
    case Con{T.Buf{p, ls}, t} 0n:
      {==}
    case Con{T.Buf{p, ls}, t} 1n+q:
      Path.spec_path(t, q)
