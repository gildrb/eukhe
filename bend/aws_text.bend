# aws_text: the names and texts the Bedrock client reads (eukhe-ai
# api/bedrock_converse_stream/client.rs, credentials/sdk_client.rs): the
# partition of a region, the request-id header, a base64 blob, the region
# of a standard Bedrock endpoint host and of a Bedrock ARN, a FIPS
# pseudo-region's real region. Each is a plain string rule (a prefix taken
# off, a run of chars read); laws/aws_text.bend states each in plain words
# over splits of the text. Above each rule: the regex it replaced. A word
# char here is A-Z, a-z, 0-9 or `_` (Rust's `\w` takes every Unicode word
# char: an intended difference). Pure: no IO, no @unsafe.

import Base
import ./text_pat.bend as Tp
import ./phrase.bend as P
import ./model_name.bend as M

# Chars
# -----

# a char of a region in a host or an ARN: a-z, 0-9 or `-`
def is_lc(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(P.in_range(x, 97, 122), Bool.or(P.in_range(x, 48, 57), U32.is_eq(x, 45)))

# a word char or `-`
def is_wd(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(P.is_word(Chr{x}), U32.is_eq(x, 45))

# R1: the partition of a region
# -----------------------------

# N: one or more digits, then the end (seen: a digit was read)
def shape.n(s: String, seen: Bool) -> Bool:
  match s:
    case SNil{}:
      seen
    case SCon{x, t}:
      P.pm.and(Tp.is_dig(x), u => shape.n(t, True{}))

# W: one or more word chars, then `-`, then N (seen: a word char was read)
def shape.w(s: String, seen: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+x, +t}:
      M.ite(P.is_word(x), u => shape.w(t, True{}), v => P.pm.and(seen, w => P.pm.and(Char.is_eq(x, '-'), z => shape.n(t, False{}))))

def shape.on(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      shape.w(r, False{})

# whether the region is p, `-`, word chars, `-`, digits
def shape(+p: String, region: String) -> Bool:
  shape.on(M.strip(String.append(p, "-"), region))

def shapes(ps: List<&2, String>, +region: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      P.pm.or(shape(p, region), u => shapes(more, region))

# the prefixes of each partition, in the order the rule tries them: aws,
# aws-cn, aws-eusc, aws-iso, aws-iso-b, aws-iso-e, aws-iso-f, aws-us-gov
#   ^(us|eu|ap|sa|ca|me|af|il|mx)-[A-Za-z0-9_]+-[0-9]+$
#   ^cn-[A-Za-z0-9_]+-[0-9]+$
#   ^eusc-(de)-[A-Za-z0-9_]+-[0-9]+$
#   ^us-iso-[A-Za-z0-9_]+-[0-9]+$
#   ^us-isob-[A-Za-z0-9_]+-[0-9]+$
#   ^eu-isoe-[A-Za-z0-9_]+-[0-9]+$
#   ^us-isof-[A-Za-z0-9_]+-[0-9]+$
#   ^us-gov-[A-Za-z0-9_]+-[0-9]+$
def partitions() -> List<&2, List<&2, String>>:
  [["us", "eu", "ap", "sa", "ca", "me", "af", "il", "mx"], ["cn"], ["eusc-de"], ["us-iso"], ["us-isob"], ["eu-isoe"], ["us-isof"], ["us-gov"]]

def pick(b: Bool, i: Nat, rest: Unit -> Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      rest(Unit{})

def partition.go(tab: List<&2, List<&2, String>>, +region: String, i: Nat) -> Maybe<&2, Nat>:
  match tab:
    case Nil{}:
      None{}
    case ps <> more:
      +j = i
      pick(shapes(ps, region), j, u => partition.go(more, region, 1n+j))

# the index of the first partition whose shape the region has
def partition(+region: String) -> Maybe<&2, Nat>:
  partition.go(partitions(), region, 0n)

# R2: the request-id header
# -------------------------

# whether s is `-request-id` or `-requestid`
def rid.tail(+s: String) -> Bool:
  P.pm.or(M.got_all(M.strip("-request-id", s)), u => M.got_all(M.strip("-requestid", s)))

# M then the tail (seen: a char of M was read)
def rid.go(s: String, seen: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+x, +t}:
      P.pm.or(P.pm.and(seen, u => rid.tail(SCon{x, t})), v => P.pm.and(is_wd(x), w => rid.go(t, True{})))

def rid.on(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      rid.go(r, False{})

# ^x-[\w-]+-request-?id$
def is_rid(name: String) -> Bool:
  rid.on(M.strip("x-", name))

def rid.index(names: List<&2, String>, i: Nat) -> Maybe<&2, Nat>:
  match names:
    case Nil{}:
      None{}
    case n <> more:
      +j = i
      pick(is_rid(n), j, u => rid.index(more, 1n+j))

# the index of the first request-id header name
def request_id(names: List<&2, String>) -> Maybe<&2, Nat>:
  rid.index(names, 0n)

# R3: base64
# ----------

# UTF-16 code units read so far, modulo 4
type Q is Data:
  Q0{}
  Q1{}
  Q2{}
  Q3{}

# where the text is: in the body, after one `=`, after two, invalid
type Ph is Data:
  PB{}
  P1{}
  P2{}
  PX{}

type St is Data:
  St{q: Q, p: Ph}

def q.one(q: Q) -> Q:
  match q:
    case Q0{}:
      Q1{}
    case Q1{}:
      Q2{}
    case Q2{}:
      Q3{}
    case Q3{}:
      Q0{}

# q after a char of 1 code unit, or 2 (wide: past U+FFFF)
def q.add(q: Q, wide: Bool) -> Q:
  match wide:
    case True{}:
      q.one(q.one(q))
    case False{}:
      q.one(q)

# a base64 char: A-Z, a-z, 0-9, `+`, `/`
def is_b64(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(P.in_range(x, 65, 90), Bool.or(P.in_range(x, 97, 122), Bool.or(P.in_range(x, 48, 57), Bool.or(U32.is_eq(x, 43), U32.is_eq(x, 47)))))

def ph.body(b: Bool, eq: Bool) -> Ph:
  match b:
    case True{}:
      PB{}
    case False{}:
      match eq:
        case True{}:
          P1{}
        case False{}:
          PX{}

def ph.pad(eq: Bool, next: Ph) -> Ph:
  match eq:
    case True{}:
      next
    case False{}:
      PX{}

def ph.step(p: Ph, +c: Char) -> Ph:
  match p:
    case PB{}:
      ph.body(is_b64(c), Char.is_eq(c, '='))
    case P1{}:
      ph.pad(Char.is_eq(c, '='), P2{})
    case P2{}:
      PX{}
    case PX{}:
      PX{}

def wide(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      U32.is_lt(65535, x)

# the state after s, from q and p (one pass)
def b64.go(s: String, q: Q, p: Ph) -> St:
  match s:
    case SNil{}:
      St{q, p}
    case SCon{+c, t}:
      b64.go(t, q.add(q, wide(c)), ph.step(p, c))

def b64.go1(s: String, st: St) -> St:
  match st:
    case St{q, p}:
      b64.go(s, q, p)

# the state after the chunks, in order (one pass over each)
def b64.chunks(cs: List<&2, String>, st: St) -> St:
  match cs:
    case Nil{}:
      st
    case c <> more:
      b64.chunks(more, b64.go1(c, st))

def b64.verdict.q(q: Q, p: Ph) -> Nat:
  match q:
    case Q0{}:
      match p:
        case PX{}:
          2n
        case PB{}:
          0n
        case P1{}:
          0n
        case P2{}:
          0n
    case Q1{}:
      1n
    case Q2{}:
      1n
    case Q3{}:
      1n

def b64.verdict(st: St) -> Nat:
  match st:
    case St{q, p}:
      b64.verdict.q(q, p)

# 1 when the text's length in UTF-16 code units is no multiple of 4 (bad
# padding), else 0 when ^[A-Za-z0-9+/]*={0,2}$ (valid), else 2 (invalid);
# the text is the chunks read as one
def base64(cs: List<&2, String>) -> Nat:
  b64.verdict(b64.chunks(cs, St{Q0{}, PB{}}))

# R4, R5: regions in a host and an ARN
# ------------------------------------

def lc.take.at(b: Bool, x: Char, rest: Unit -> String) -> String:
  match b:
    case True{}:
      SCon{x, rest(Unit{})}
    case False{}:
      SNil{}

# the region chars at the start of s
def lc.take(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      lc.take.at(is_lc(x), x, u => lc.take(t))

def lc.drop.at(b: Bool, s: String, rest: Unit -> String) -> String:
  match b:
    case True{}:
      rest(Unit{})
    case False{}:
      s

# s after the region chars at its start
def lc.drop(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      lc.drop.at(is_lc(x), SCon{x, t}, u => lc.drop(t))

def found(b: Bool, r: String) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{r}
    case False{}:
      None{}

# the region chars at the start of s, when there are some and the rest is
# `.amazonaws.com` or `.amazonaws.com.cn`
def ep.region(+s: String) -> Maybe<&2, String>:
  +r = lc.drop(s)
  found(Bool.and(Bool.not(String.is_empty(lc.take(s))), P.pm.or(M.got_all(M.strip(".amazonaws.com", r)), u => M.got_all(M.strip(".amazonaws.com.cn", r)))), lc.take(s))

def ep.dot(m: Maybe<&2, String>, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      rest(Unit{})
    case Some{r}:
      ep.region(r)

def ep.fips(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      ep.region(r)

def ep.after(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+r}:
      ep.dot(M.strip(".", r), u => ep.fips(M.strip("-fips.", r)))

# ^bedrock-runtime(?:-fips)?\.([a-z0-9-]+)\.amazonaws\.com(?:\.cn)?$
def endpoint(host: String) -> Maybe<&2, String>:
  ep.after(M.strip("bedrock-runtime", host))

# the region chars at the start of s, when there are some and `:` follows
def arn.region(+s: String) -> Maybe<&2, String>:
  found(Bool.and(Bool.not(String.is_empty(lc.take(s))), M.got(M.strip(":", lc.drop(s)))), lc.take(s))

def arn.bedrock(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      arn.region(r)

def arn.part.at(empty: Bool, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match empty:
    case True{}:
      None{}
    case False{}:
      rest(Unit{})

# after `arn:aws-`: one or more partition chars, then `:bedrock:`
def arn.part(+s: String) -> Maybe<&2, String>:
  arn.part.at(String.is_empty(lc.take(s)), u => arn.bedrock(M.strip(":bedrock:", lc.drop(s))))

def arn.dash(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      arn.part(r)

def arn.colon(m: Maybe<&2, String>, rest: Unit -> Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      rest(Unit{})
    case Some{r}:
      arn.region(r)

def arn.after(m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+r}:
      arn.colon(M.strip(":bedrock:", r), u => arn.dash(M.strip("-", r)))

# ^arn:aws(?:-[a-z0-9-]+)?:bedrock:([a-z0-9-]+):
def arn(id: String) -> Maybe<&2, String>:
  arn.after(M.strip("arn:aws", id))

# R6: FIPS
# --------

def fips.longer(m: Maybe<&2, String>, rest: Unit -> String) -> String:
  match m:
    case None{}:
      rest(Unit{})
    case Some{r}:
      r

# s after `fips-`: past `dkr-` or `prod-` when one stands there
def fips.tail(+r: String) -> String:
  fips.longer(M.strip("dkr-", r), u => fips.longer(M.strip("prod-", r), v => r))

def fips.first(m: Maybe<&2, String>, +s: String) -> Maybe<&2, String>:
  match m:
    case None{}:
      M.strip("-fips", s)
    case Some{r}:
      Some{fips.tail(r)}

# what is left of s when a FIPS part begins at its start, cut out
def fips.cut(+s: String) -> Maybe<&2, String>:
  fips.first(M.strip("fips-", s), s)

def fips.at(m: Maybe<&2, String>, x: Char, rest: Unit -> String) -> String:
  match m:
    case None{}:
      SCon{x, rest(Unit{})}
    case Some{r}:
      r

# fips-(dkr-|prod-)?|-fips replaced once by "": at the first place where a
# FIPS part begins, the longest is cut out
def without_fips(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      fips.at(fips.cut(SCon{x, t}), x, u => without_fips(t))
