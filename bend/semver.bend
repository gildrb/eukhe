# semver: eukhe's release versions (laws/semver.bend R1, docs/develop.md
# "Releases"). The rule runs as compiled Bend (entry bend/ffi_semver.bend,
# laws/semver.bend R2): `eukhe-next-version` computes a release with it and
# crates/eukhe-build-info's build script checks EUKHE_RELEASE_VERSION.
#
# 1. Numbers. A number is written in decimal without leading zeros: "0",
#    "7", "10", never "", "07" or "+7". Num.show writes one; Num.read
#    takes the digits of a field (last digit first) and accepts them only
#    when they are the way Num.show writes their value.
# 2. Versions. A version is major.minor.patch, three numbers and two dots
#    and nothing else. Ver.show writes one, Ver.parse reads one and
#    refuses any other text.
# 3. The order. Major first, then minor, then patch. Ver.lt(u, v): v is
#    newer than u.
# 4. Tags and titles. The tag of v is "eukhe-v" ++ show(v); its release is
#    titled "Eukhe v" ++ show(v). Tag.ver reads a tag back; any other text
#    (the upstream "v1.2.3" tags, "eukhe-v0.9.9-main.4") is no version.
# 5. The next release. The series is the workspace version X.Y.Z of
#    Cargo.toml (Z is not used). The next release of the series is X.Y.P:
#    P is 1 + the highest patch among the version tags of the series, 0
#    when there is none. Tags of other series change nothing.
# 6. A release. The workspace version must be X.Y.0, and the next release
#    must be newer than every version tag (a tag of a newer series stops
#    it); else there is none and the script fails.
#
# A number is unary underneath (Nat): the model reads and writes any
# number, and runs fast on small ones; the entry refuses a number of more
# than 6 digits.

import Base

# 1. Numbers
# ----------

type Dig is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def Dig.val(d: Dig) -> Nat:
  match d:
    case D0{}:
      0n
    case D1{}:
      1n
    case D2{}:
      2n
    case D3{}:
      3n
    case D4{}:
      4n
    case D5{}:
      5n
    case D6{}:
      6n
    case D7{}:
      7n
    case D8{}:
      8n
    case D9{}:
      9n

def Dig.chr(d: Dig) -> Char:
  match d:
    case D0{}:
      '0'
    case D1{}:
      '1'
    case D2{}:
      '2'
    case D3{}:
      '3'
    case D4{}:
      '4'
    case D5{}:
      '5'
    case D6{}:
      '6'
    case D7{}:
      '7'
    case D8{}:
      '8'
    case D9{}:
      '9'

def Dig.eq(+a: Dig, +b: Dig) -> Bool:
  Nat.is_eq(Dig.val(a), Dig.val(b))

# the digits of a number, last digit first
def Num.ten(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      Nat.add(10n, Num.ten(p))

def Num.val(ds: List<&2, Dig>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case d <> rest:
      Nat.add(Dig.val(d), Num.ten(Num.val(rest)))

# the digits of the next number
def Num.inc(ds: List<&2, Dig>) -> List<&2, Dig>:
  match ds:
    case Nil{}:
      [D1{}]
    case d <> rest:
      match d:
        case D0{}:
          D1{} <> rest
        case D1{}:
          D2{} <> rest
        case D2{}:
          D3{} <> rest
        case D3{}:
          D4{} <> rest
        case D4{}:
          D5{} <> rest
        case D5{}:
          D6{} <> rest
        case D6{}:
          D7{} <> rest
        case D7{}:
          D8{} <> rest
        case D8{}:
          D9{} <> rest
        case D9{}:
          D0{} <> Num.inc(rest)

# the digits of n as Num.show writes them: "0" for 0, else no leading zero
def Num.dec(n: Nat) -> List<&2, Dig>:
  match n:
    case 0n:
      [D0{}]
    case 1n+p:
      Num.inc(Num.dec(p))

def Num.digs_eq(xs: List<&2, Dig>, ys: List<&2, Dig>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} _ <> _:
      False{}
    case _ <> _ Nil{}:
      False{}
    case +x <> xr +y <> yr:
      Bool.and(Dig.eq(x, y), Num.digs_eq(xr, yr))

# ds (last digit first) written before acc
def Num.str(ds: List<&2, Dig>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case d <> rest:
      Num.str(rest, SCon{Dig.chr(d), acc})

def Num.show(n: Nat) -> String:
  Num.str(Num.dec(n), SNil{})

def Num.read.ok(n: Nat, ok: Bool) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# the number of a field's digits, when Num.show writes it that way
def Num.read(+ds: List<&2, Dig>) -> Maybe<&2, Nat>:
  Num.read.ok(Num.val(ds), Num.digs_eq(Num.dec(Num.val(ds)), ds))

# 2. Versions
# -----------

type Ver is Data:
  Ver{major: Nat, minor: Nat, patch: Nat}

def Ver.show(v: Ver) -> String:
  match v:
    case Ver{a, b, c}:
      Num.str(Num.dec(a), SCon{'.', Num.str(Num.dec(b), SCon{'.', Num.str(Num.dec(c), SNil{})})})

type Sym is Data:
  Digit{d: Dig}
  Dot{}
  Other{}

def Sym.when(hit: Bool, y: Sym, miss: Sym) -> Sym:
  match hit:
    case True{}:
      y
    case False{}:
      miss

# the symbol of a char: one compare per symbol, on the char's code
def Sym.of(+c: Char) -> Sym:
  Sym.when(Char.is_eq(c, '0'), Digit{D0{}}, Sym.when(Char.is_eq(c, '1'), Digit{D1{}}, Sym.when(Char.is_eq(c, '2'), Digit{D2{}}, Sym.when(Char.is_eq(c, '3'), Digit{D3{}}, Sym.when(Char.is_eq(c, '4'), Digit{D4{}}, Sym.when(Char.is_eq(c, '5'), Digit{D5{}}, Sym.when(Char.is_eq(c, '6'), Digit{D6{}}, Sym.when(Char.is_eq(c, '7'), Digit{D7{}}, Sym.when(Char.is_eq(c, '8'), Digit{D8{}}, Sym.when(Char.is_eq(c, '9'), Digit{D9{}}, Sym.when(Char.is_eq(c, '.'), Dot{}, Other{})))))))))))

def Sym.list(s: String) -> List<&2, Sym>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Sym.of(c) <> Sym.list(t)

# the fields of a text split at its dots: cur is the field being read
# (last digit first), fs the fields read (last first); None on a symbol
# that is no digit and no dot
def Ver.fields(ss: List<&2, Sym>, cur: List<&2, Dig>, fs: List<&2, List<&2, Dig>>) -> Maybe<&2, List<&2, List<&2, Dig>>>:
  match ss:
    case Nil{}:
      Some{cur <> fs}
    case s <> rest:
      match s:
        case Digit{d}:
          Ver.fields(rest, d <> cur, fs)
        case Dot{}:
          Ver.fields(rest, Nil{}, cur <> fs)
        case Other{}:
          None{}

def Ver.of3(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> Maybe<&2, Ver>:
  match a b c:
    case Some{x} Some{y} Some{z}:
      Some{Ver{x, y, z}}
    case _ _ _:
      None{}

# three fields, last first
def Ver.of_fields(m: Maybe<&2, List<&2, List<&2, Dig>>>) -> Maybe<&2, Ver>:
  match m:
    case None{}:
      None{}
    case Some{fs}:
      match fs:
        case c <> b <> a <> Nil{}:
          Ver.of3(Num.read(a), Num.read(b), Num.read(c))
        case _:
          None{}

def Ver.parse(s: String) -> Maybe<&2, Ver>:
  Ver.of_fields(Ver.fields(Sym.list(s), Nil{}, Nil{}))

# 3. The order
# ------------

def Num.le(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n _:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      Num.le(p, q)

def Ver.le2(b1: Nat, b2: Nat, c1: Nat, c2: Nat) -> Bool:
  match b1 b2:
    case 0n 0n:
      Num.le(c1, c2)
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      Ver.le2(p, q, c1, c2)

def Ver.le3(a1: Nat, a2: Nat, b1: Nat, b2: Nat, c1: Nat, c2: Nat) -> Bool:
  match a1 a2:
    case 0n 0n:
      Ver.le2(b1, b2, c1, c2)
    case 0n 1n+q:
      True{}
    case 1n+p 0n:
      False{}
    case 1n+p 1n+q:
      Ver.le3(p, q, b1, b2, c1, c2)

# u is v or older
def Ver.le(u: Ver, v: Ver) -> Bool:
  match u v:
    case Ver{a1, b1, c1} Ver{a2, b2, c2}:
      Ver.le3(a1, a2, b1, b2, c1, c2)

# v is newer than u
def Ver.lt(u: Ver, v: Ver) -> Bool:
  Bool.not(Ver.le(v, u))

# 4. Tags and titles
# ------------------

def Tag.of(v: Ver) -> String:
  String.append("eukhe-v", Ver.show(v))

def Rel.title(v: Ver) -> String:
  String.append("Eukhe v", Ver.show(v))

def Tag.strip(t: String) -> Maybe<&2, String>:
  match t:
    case SCon{'e', SCon{'u', SCon{'k', SCon{'h', SCon{'e', SCon{'-', SCon{'v', rest}}}}}}}:
      Some{rest}
    case _:
      None{}

def Tag.ver.of(m: Maybe<&2, String>) -> Maybe<&2, Ver>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Ver.parse(s)

# the version a tag names, None for any other text
def Tag.ver(t: String) -> Maybe<&2, Ver>:
  Tag.ver.of(Tag.strip(t))

# 5. The next release
# -------------------

def Ver.in_series(s: Ver, v: Ver) -> Bool:
  match s v:
    case Ver{a1, b1, c1} Ver{a2, b2, c2}:
      Bool.and(Nat.is_eq(a1, a2), Nat.is_eq(b1, b2))

def Num.max(a: Nat, b: Nat) -> Nat:
  match a b:
    case 0n _:
      b
    case 1n+p 0n:
      1n+p
    case 1n+p 1n+q:
      1n+Num.max(p, q)

def Rel.max(p: Nat, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match acc:
    case None{}:
      Some{p}
    case Some{q}:
      Some{Num.max(p, q)}

def Rel.keep(b: Bool, p: Nat, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Rel.max(p, acc)
    case False{}:
      acc

def Ver.patch(v: Ver) -> Nat:
  match v:
    case Ver{a, b, c}:
      c

def Rel.add(+s: Ver, m: Maybe<&2, Ver>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      acc
    case Some{+v}:
      Rel.keep(Ver.in_series(s, v), Ver.patch(v), acc)

# the highest patch among the version tags of the series, None when none
def Rel.top(+s: Ver, tags: List<&2, String>) -> Maybe<&2, Nat>:
  match tags:
    case Nil{}:
      None{}
    case t <> rest:
      Rel.add(s, Tag.ver(t), Rel.top(s, rest))

def Rel.after(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{p}:
      1n+p

def Rel.next(+s: Ver, tags: List<&2, String>) -> Ver:
  match s:
    case Ver{a, b, c}:
      Ver{a, b, Rel.after(Rel.top(Ver{a, b, c}, tags))}

# the tag names a version of the series
def Rel.ofs.of(+s: Ver, m: Maybe<&2, Ver>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      Ver.in_series(s, v)

def Rel.ofs(+s: Ver, t: String) -> Bool:
  Rel.ofs.of(s, Tag.ver(t))

# no tag names a version of the series
def Rel.none(+s: Ver, tags: List<&2, String>) -> Bool:
  match tags:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(Bool.not(Rel.ofs(s, t)), Rel.none(s, rest))

# every tag that names a version names one of the series
def Rel.only.of(+s: Ver, m: Maybe<&2, Ver>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{v}:
      Ver.in_series(s, v)

def Rel.only(+s: Ver, tags: List<&2, String>) -> Bool:
  match tags:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(Rel.only.of(s, Tag.ver(t)), Rel.only(s, rest))

# 6. A release
# ------------

def Rel.older(+n: Ver, m: Maybe<&2, Ver>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{v}:
      Ver.lt(v, n)

# n is newer than every version tag
def Rel.newest(+n: Ver, tags: List<&2, String>) -> Bool:
  match tags:
    case Nil{}:
      True{}
    case t <> rest:
      Bool.and(Rel.older(n, Tag.ver(t)), Rel.newest(n, rest))

def Rel.guard(ok: Bool, v: Ver) -> Maybe<&2, Ver>:
  match ok:
    case True{}:
      Some{v}
    case False{}:
      None{}

def Rel.release.at(a: Nat, b: Nat, c: Nat, +tags: List<&2, String>) -> Maybe<&2, Ver>:
  match c:
    case 0n:
      +n = Rel.next(Ver{a, b, 0n}, tags)
      Rel.guard(Rel.newest(n, tags), n)
    case 1n+p:
      None{}

def Rel.release.of(m: Maybe<&2, Ver>, +tags: List<&2, String>) -> Maybe<&2, Ver>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case Ver{a, b, c}:
          Rel.release.at(a, b, c, tags)

# the release of a commit: the workspace version `cargo` and the
# repository's tags; None when there is none
def Rel.release(cargo: String, +tags: List<&2, String>) -> Maybe<&2, Ver>:
  Rel.release.of(Ver.parse(cargo), tags)
