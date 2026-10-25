# package_source: the package sources of `eukhe package` (Rust: eukhe-bend
# rules/package_source.rs; asked by eukhe-core packages/source.rs): what a
# source string is (an `npm:` spec, a git URL, a local path), the parts a
# git or npm source names, why such a part is refused, and the texts.
#
# Trim: Rust `str::trim` (whitespace = `char::is_whitespace`, gateway_answer's
# `space`). Checks: an argument is non-empty, does not start with `-`, holds
# no control char (U+0000-U+001F, U+007F-U+009F) and no backslash; a
# relative path is an argument whose `/`-separated segments are all
# non-empty, not `.` or `..`, and do not start with an ASCII letter then `:`.
# Pure: no IO, no @unsafe.

import Base
import ./gateway_answer.bend as Ga

# The part of a source a refusal names
type Part is Data:
  PHost{}
  PPath{}
  PRef{}
  PClone{}
  PSpec{}
  PName{}

# Why a part is refused
type Defect is Data:
  DEmpty{}
  DEmptySeg{}
  DDot{}
  DDrive{}
  DBackslash{}
  DControl{}
  DDash{}
  DSlash{}

# A refused part and why
type Flaw is Data:
  Flaw{part: Part, defect: Defect}

# An `npm:` source: the spec, its package name, whether it pins a version
type NpmSrc is Data:
  NpmSrc{spec: String, name: String, pinned: Bool}

# A git source: the clone URL, the host, the repository path, the ref,
# whether a ref pins it
type GitSrc is Data:
  GitSrc{repo: String, host: String, path: String, gref: Maybe<&2, String>, pinned: Bool}

# A source's kind
type Src is Data:
  SrcNpm{npm: NpmSrc}
  SrcGit{git: GitSrc}
  SrcLocal{path: String}

# A source string's answer
type Parsed is Data:
  Parsed{src: Src}
  Refused{flaw: Flaw}

# A source string read as a git URL
type GitAns is Data:
  NoGit{}
  IsGit{git: GitSrc}
  BadGit{flaw: Flaw}

# An npm spec: the name, the pinned version
type NpmSpec is Data:
  NpmSpec{name: String, version: Maybe<&2, String>}

# Text before a separator, and the text after it
type Cut is Data:
  Cut{head: String, tail: String}

# A protocol URL: the scheme (before the first `://`), the authority (up to
# the next `/`), the path after that `/`
type Url is Data:
  Url{scheme: String, auth: String, path: String}

# A URL and the ref split off it
type Refd is Data:
  Refd{repo: String, gref: Maybe<&2, String>}

# A hosted shortcut source: the domain, the user, the project, the
# committish
type Hosted is Data:
  Hosted{domain: String, user: String, project: String, committish: Maybe<&2, String>}

# Text
# ----

def is_some(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# s holds the char x
def has(s: String, +x: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, x), has(t, x))

def lspace.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading whitespace
def lspace(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      lspace.at(Ga.space(c), c, t, lspace(t))

# s without whitespace at both ends (Rust `str::trim`)
def trim(s: String) -> String:
  String.reverse(lspace(String.reverse(lspace(s))))

def lslash.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `/`s
def lslash(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      lslash.at(Char.is_eq(c, '/'), c, t, lslash(t))

def nogit.at(b: Bool, r: String, k: String) -> String:
  match b:
    case True{}:
      k
    case False{}:
      r

# a reversed text without its leading `tig.`s, at most n of them
def nogit(n: Nat, +r: String) -> String:
  match n:
    case 0n:
      r
    case 1n+p:
      nogit.at(String.starts_with(r, "tig."), r, nogit(p, String.drop(r, 4n)))

# s without its trailing `.git`s
def unsuffix(+s: String) -> String:
  String.reverse(nogit(String.length(s), String.reverse(s)))

def cut.at(b: Bool, c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match b:
    case True{}:
      Some{Cut{SNil{}, t}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Cut{h, u}:
              Some{Cut{SCon{c, h}, u}}

# s split at its first `sep` (none without one)
def cut(s: String, +sep: Char) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      cut.at(Char.is_eq(c, sep), c, t, cut(t, sep))

def before.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

# s up to its first `sep` (all of s without one)
def before(s: String, +sep: Char) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      before.at(Char.is_eq(c, sep), c, before(t, sep))

def proto.at(b: Bool, c: Char, t: String, r: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match b:
    case True{}:
      Some{Cut{SNil{}, String.drop(t, 2n)}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Cut{h, u}:
              Some{Cut{SCon{c, h}, u}}

# s split at its first `://` (none without one)
def proto(s: String) -> Maybe<&2, Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      proto.at(String.starts_with(SCon{c, t}, "://"), c, t, proto(t))

def url.at(sc: String, m: Maybe<&2, Cut>) -> Maybe<&2, Url>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{a, p}:
          Some{Url{sc, a, p}}

def url.of(m: Maybe<&2, Cut>) -> Maybe<&2, Url>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{sc, rest}:
          url.at(sc, cut(rest, '/'))

# s as a protocol URL: a `://`, then a `/` after it (none without both)
def url(s: String) -> Maybe<&2, Url>:
  url.of(proto(s))

# the host of an authority: after its last `@`, up to its first `:`
def host_of(a: String) -> String:
  before(String.reverse(before(String.reverse(a), '@')), ':')

# s starts with `https://`, `http://`, `ssh://` or `git://`, ASCII letters
# in either case
def proto_url(s: String) -> Bool:
  +l = String.to_lower(s)
  Bool.or(String.starts_with(l, "https://"), Bool.or(String.starts_with(l, "http://"), Bool.or(String.starts_with(l, "ssh://"), String.starts_with(l, "git://"))))

# Checks
# ------

def control(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_le(x, 31), Bool.and(U32.is_ge(x, 127), U32.is_le(x, 159)))

def any_control(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(control(c), any_control(t))

def arg.at(dash: Bool, ctl: Bool, bs: Bool) -> Maybe<&2, Defect>:
  match dash:
    case True{}:
      Some{DDash{}}
    case False{}:
      match ctl:
        case True{}:
          Some{DControl{}}
        case False{}:
          match bs:
            case True{}:
              Some{DBackslash{}}
            case False{}:
              None{}

# why a value git or npm could misread is refused (none: it is safe)
def arg(s: String) -> Maybe<&2, Defect>:
  match s:
    case SNil{}:
      Some{DEmpty{}}
    case SCon{+c, +t}:
      arg.at(Char.is_eq(c, '-'), any_control(SCon{c, t}), has(SCon{c, t}, Chr{92}))

def seg.at(dot: Bool, drive: Bool) -> Maybe<&2, Defect>:
  match dot:
    case True{}:
      Some{DDot{}}
    case False{}:
      match drive:
        case True{}:
          Some{DDrive{}}
        case False{}:
          None{}

# why a path segment is refused (none: a plain name)
def seg(s: String) -> Maybe<&2, Defect>:
  match s:
    case SNil{}:
      Some{DEmptySeg{}}
    case SCon{+c, +t}:
      seg.at(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, "..")), Bool.and(Char.is_alpha(c), String.starts_with(t, ":")))

def first.at(m: Maybe<&2, Defect>, r: Maybe<&2, Defect>) -> Maybe<&2, Defect>:
  match m:
    case None{}:
      r
    case Some{d}:
      Some{d}

# the first segment's defect
def segs(xs: List<&2, String>) -> Maybe<&2, Defect>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      first.at(seg(h), segs(t))

# why a relative path is refused: as an argument, then segment by segment
def rel(+s: String) -> Maybe<&2, Defect>:
  first.at(arg(s), segs(String.split(s, '/')))

# Git URLs
# --------

def refcut.ok(e: Bool, a: String, b: String) -> Maybe<&2, Cut>:
  match e:
    case True{}:
      None{}
    case False{}:
      Some{Cut{a, b}}

def refcut.at(m: Maybe<&2, Cut>) -> Maybe<&2, Cut>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{+a, +b}:
          refcut.ok(Bool.or(String.is_empty(a), String.is_empty(b)), a, b)

# s split at its first `@` into a path and a ref, both non-empty
def refcut(s: String) -> Maybe<&2, Cut>:
  refcut.at(cut(s, '@'))

def sref.scp.at(h: String, m: Maybe<&2, Cut>, u: String) -> Refd:
  match m:
    case None{}:
      Refd{u, None{}}
    case Some{x}:
      match x:
        case Cut{p, r}:
          Refd{String.concat(["git@", h, ":", p]), Some{r}}

def sref.url.at(sc: String, a: String, m: Maybe<&2, Cut>, u: String) -> Refd:
  match m:
    case None{}:
      Refd{u, None{}}
    case Some{x}:
      match x:
        case Cut{p, r}:
          Refd{String.concat([sc, "://", a, "/", p]), Some{r}}

def sref.short.at(h: String, m: Maybe<&2, Cut>, u: String) -> Refd:
  match m:
    case None{}:
      Refd{u, None{}}
    case Some{x}:
      match x:
        case Cut{p, r}:
          Refd{String.concat([h, "/", p]), Some{r}}

def sref.short(m: Maybe<&2, Cut>, u: String) -> Refd:
  match m:
    case None{}:
      Refd{u, None{}}
    case Some{x}:
      match x:
        case Cut{h, p}:
          sref.short.at(h, refcut(p), u)

def sref.url(m: Maybe<&2, Url>, +u: String) -> Refd:
  match m:
    case None{}:
      sref.short(cut(u, '/'), u)
    case Some{x}:
      match x:
        case Url{sc, a, p}:
          sref.url.at(sc, a, refcut(lslash(p)), u)

def sref.scp(m: Maybe<&2, Cut>, +u: String) -> Refd:
  match m:
    case None{}:
      sref.url(url(u), u)
    case Some{x}:
      match x:
        case Cut{h, p}:
          sref.scp.at(h, refcut(p), u)

def sref.at(b: Bool, +u: String) -> Refd:
  match b:
    case True{}:
      sref.scp(cut(String.drop(u, 4n), ':'), u)
    case False{}:
      sref.url(url(u), u)

# a URL split into the clone URL and its ref: `git@host:path@ref`, a
# protocol URL's path `@ref`, `host/path@ref`
def sref(+u: String) -> Refd:
  sref.at(String.starts_with(u, "git@"), u)

def short.at(a: Bool, b: Bool, c: Bool, d: Bool, +u: String) -> Maybe<&2, Cut>:
  match a:
    case True{}:
      Some{Cut{"github.com", String.drop(u, 7n)}}
    case False{}:
      match b:
        case True{}:
          Some{Cut{"gitlab.com", String.drop(u, 7n)}}
        case False{}:
          match c:
            case True{}:
              Some{Cut{"bitbucket.org", String.drop(u, 10n)}}
            case False{}:
              match d:
                case True{}:
                  Some{Cut{"gist.github.com", String.drop(u, 5n)}}
                case False{}:
                  None{}

# a hosted shortcut's domain and the text after the shortcut
def short(+u: String) -> Maybe<&2, Cut>:
  short.at(String.starts_with(u, "github:"), String.starts_with(u, "gitlab:"), String.starts_with(u, "bitbucket:"), String.starts_with(u, "gist:"), u)

def hosted.ok(e: Bool, d: String, u: String, p: String, k: Maybe<&2, String>) -> Maybe<&2, Hosted>:
  match e:
    case True{}:
      None{}
    case False{}:
      Some{Hosted{d, u, unsuffix(p), k}}

def hosted.parts(d: String, m: Maybe<&2, Cut>, k: Maybe<&2, String>) -> Maybe<&2, Hosted>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{+u, +p}:
          hosted.ok(Bool.or(String.is_empty(u), String.is_empty(p)), d, u, p, k)

def hosted.short(m: Maybe<&2, Cut>, k: Maybe<&2, String>) -> Maybe<&2, Hosted>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{d, rest}:
          hosted.parts(d, cut(rest, '/'), k)

def hosted.at(m: Maybe<&2, Cut>, c: String) -> Maybe<&2, Hosted>:
  match m:
    case None{}:
      hosted.short(short(c), None{})
    case Some{x}:
      match x:
        case Cut{u, k}:
          hosted.short(short(u), Some{k})

# a hosted shortcut candidate `<shortcut>user/project[#committish]`
def hosted(+c: String) -> Maybe<&2, Hosted>:
  hosted.at(cut(c, '#'), c)

def keep.at(drop: Bool, h: Hosted) -> Maybe<&2, Hosted>:
  match drop:
    case True{}:
      None{}
    case False{}:
      Some{h}

def keep.of(h: Hosted, +r: Bool) -> Maybe<&2, Hosted>:
  match h:
    case Hosted{d, u, +p, k}:
      keep.at(Bool.and(r, has(p, '@')), Hosted{d, u, p, k})

# a candidate, dropped when a ref was split off and its project holds `@`
def keep(m: Maybe<&2, Hosted>, +r: Bool) -> Maybe<&2, Hosted>:
  match m:
    case None{}:
      None{}
    case Some{h}:
      keep.of(h, r)

def pick(a: Maybe<&2, Hosted>, b: Maybe<&2, Hosted>) -> Maybe<&2, Hosted>:
  match a:
    case None{}:
      b
    case Some{h}:
      Some{h}

def cand.at(repo: String, m: Maybe<&2, String>) -> Maybe<&2, Hosted>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      keep(hosted(String.concat([repo, "#", r])), True{})

# the first candidate: the clone URL `#` the split ref (none without a ref)
def cand(rd: Refd) -> Maybe<&2, Hosted>:
  match rd:
    case Refd{repo, m}:
      cand.at(repo, m)

def or_ref(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

def https.at(b: Bool, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      String.append("https://", r)

# the clone URL: `https://` before one without a scheme or `git@`
def https(+r: String) -> String:
  https.at(Bool.or(String.starts_with(r, "http://"), Bool.or(String.starts_with(r, "https://"), Bool.or(String.starts_with(r, "ssh://"), Bool.or(String.starts_with(r, "git://"), String.starts_with(r, "git@"))))), r)

def from_hosted.at(h: Hosted, repo: String, +r: Maybe<&2, String>) -> GitSrc:
  match h:
    case Hosted{d, u, p, +k}:
      GitSrc{https(repo), d, String.concat([u, "/", p]), or_ref(k, r), Bool.or(is_some(k), is_some(r))}

# a hosted candidate's git source
def from_hosted(h: Hosted, rd: Refd) -> GitSrc:
  match rd:
    case Refd{repo, r}:
      from_hosted.at(h, repo, r)

def shape.at(bad: Bool, h: String, q: String, clone: String, +r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match bad:
    case True{}:
      None{}
    case False{}:
      Some{GitSrc{clone, h, q, r, is_some(r)}}

# a generic source: the path without trailing `.git`s, then leading `/`s;
# none for an empty host or path, or a path of one segment
def shape(+h: String, p: String, clone: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  +q = lslash(unsuffix(p))
  shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(q), Bool.not(has(q, '/')))), h, q, clone, r)

def generic.scp(m: Maybe<&2, Cut>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{h, p}:
          shape(h, p, repo, r)

def generic.url(m: Maybe<&2, Url>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Url{sc, a, p}:
          shape(host_of(a), lslash(p), repo, r)

def generic.dot(ok: Bool, h: String, p: String, repo: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match ok:
    case True{}:
      shape(h, p, String.append("https://", repo), r)
    case False{}:
      None{}

def generic.short(m: Maybe<&2, Cut>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{+h, p}:
          generic.dot(Bool.or(has(h, '.'), String.eq(h, "localhost")), h, p, repo, r)

def generic.at(scp: Bool, pu: Bool, +repo: String, r: Maybe<&2, String>) -> Maybe<&2, GitSrc>:
  match scp:
    case True{}:
      generic.scp(cut(String.drop(repo, 4n), ':'), repo, r)
    case False{}:
      match pu:
        case True{}:
          generic.url(url(repo), repo, r)
        case False{}:
          generic.short(cut(repo, '/'), repo, r)

# a generic git source: `git@host:path`, a protocol URL, or `host/path`
# whose host holds a `.` or is `localhost`
def generic(rd: Refd) -> Maybe<&2, GitSrc>:
  match rd:
    case Refd{+repo, r}:
      generic.at(String.starts_with(repo, "git@"), proto_url(repo), repo, r)

def found.at(m: Maybe<&2, Hosted>, +rd: Refd) -> Maybe<&2, GitSrc>:
  match m:
    case None{}:
      generic(rd)
    case Some{h}:
      Some{from_hosted(h, rd)}

def ref_some(rd: Refd) -> Bool:
  match rd:
    case Refd{repo, m}:
      is_some(m)

# a git URL's source: a hosted candidate (the split one, then the URL),
# else the generic forms
def found(u: String, +rd: Refd) -> Maybe<&2, GitSrc>:
  found.at(pick(cand(rd), keep(hosted(u), ref_some(rd))), rd)

def on(p: Part, m: Maybe<&2, Defect>) -> Maybe<&2, Flaw>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Flaw{p, d}}

def host.at(b: Bool, +h: String) -> Maybe<&2, Defect>:
  match b:
    case True{}:
      Some{DSlash{}}
    case False{}:
      rel(h)

def gref(m: Maybe<&2, String>) -> Maybe<&2, Flaw>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      on(PRef{}, arg(r))

def dash.ok(b: Bool) -> Maybe<&2, Flaw>:
  match b:
    case True{}:
      Some{Flaw{PClone{}, DDash{}}}
    case False{}:
      None{}

def dash.at(m: Maybe<&2, Cut>) -> Maybe<&2, Flaw>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Cut{s, a}:
          dash.ok(String.starts_with(a, "-"))

def flaw.or(m: Maybe<&2, Flaw>, r: Maybe<&2, Flaw>) -> Maybe<&2, Flaw>:
  match m:
    case None{}:
      r
    case Some{f}:
      Some{f}

# the first refused part: the host, the path, the ref, the clone URL, then
# a clone URL whose authority starts with `-`
def flaws(g: GitSrc) -> Maybe<&2, Flaw>:
  match g:
    case GitSrc{+repo, +h, p, r, n}:
      flaw.or(on(PHost{}, host.at(has(h, '/'), h)), flaw.or(on(PPath{}, rel(p)), flaw.or(gref(r), flaw.or(on(PClone{}, arg(repo)), dash.at(proto(repo))))))

def checked.at(m: Maybe<&2, Flaw>, g: GitSrc) -> GitAns:
  match m:
    case None{}:
      IsGit{g}
    case Some{f}:
      BadGit{f}

def checked(m: Maybe<&2, GitSrc>) -> GitAns:
  match m:
    case None{}:
      NoGit{}
    case Some{+g}:
      checked.at(flaws(g), g)

def git.gate(go: Bool, +u: String) -> GitAns:
  match go:
    case True{}:
      checked(found(u, sref(u)))
    case False{}:
      NoGit{}

def git.at(b: Bool, +t: String) -> GitAns:
  match b:
    case True{}:
      git.gate(True{}, trim(String.drop(t, 4n)))
    case False{}:
      git.gate(proto_url(t), t)

# a source read as a git URL (Rust `parse_git_url`)
def git(s: String) -> GitAns:
  +t = trim(s)
  git.at(String.starts_with(t, "git:"), t)

# Sources
# -------

# a value that is no `npm:`/`git:`/`github:`/`http:`/`https:`/`ssh:`
# source once trimmed (Rust `is_local_path`)
def local(s: String) -> Bool:
  +t = trim(s)
  Bool.not(Bool.or(String.starts_with(t, "npm:"), Bool.or(String.starts_with(t, "git:"), Bool.or(String.starts_with(t, "github:"), Bool.or(String.starts_with(t, "http:"), Bool.or(String.starts_with(t, "https:"), String.starts_with(t, "ssh:")))))))

def npm_spec.ok(e: Bool, c: Char, h: String, v: String, t: String) -> NpmSpec:
  match e:
    case True{}:
      NpmSpec{SCon{c, t}, None{}}
    case False{}:
      NpmSpec{SCon{c, h}, Some{v}}

def npm_spec.at(m: Maybe<&2, Cut>, c: Char, t: String) -> NpmSpec:
  match m:
    case None{}:
      NpmSpec{SCon{c, t}, None{}}
    case Some{x}:
      match x:
        case Cut{h, +v}:
          npm_spec.ok(String.is_empty(v), c, h, v, t)

# an npm spec's name and pinned version: split at the first `@` after the
# first char, when the version is not empty (Rust `parse_npm_spec`)
def npm_spec(s: String) -> NpmSpec:
  match s:
    case SNil{}:
      NpmSpec{SNil{}, None{}}
    case SCon{+c, +t}:
      npm_spec.at(cut(t, '@'), c, t)

def npm.ok(m: Maybe<&2, Defect>, name: String, pinned: Bool, spec: String) -> Parsed:
  match m:
    case None{}:
      Parsed{SrcNpm{NpmSrc{spec, name, pinned}}}
    case Some{d}:
      Refused{Flaw{PName{}, d}}

def npm.name(ns: NpmSpec, spec: String) -> Parsed:
  match ns:
    case NpmSpec{+name, v}:
      npm.ok(rel(name), name, is_some(v), spec)

def npm.at(m: Maybe<&2, Defect>, +spec: String) -> Parsed:
  match m:
    case None{}:
      npm.name(npm_spec(spec), spec)
    case Some{d}:
      Refused{Flaw{PSpec{}, d}}

# an `npm:` source: the spec (trimmed) and its package name checked
def npm(+spec: String) -> Parsed:
  npm.at(arg(spec), spec)

def source.git(a: GitAns, s: String) -> Parsed:
  match a:
    case NoGit{}:
      Parsed{SrcLocal{s}}
    case IsGit{g}:
      Parsed{SrcGit{g}}
    case BadGit{f}:
      Refused{f}

def source.local(b: Bool, +s: String) -> Parsed:
  match b:
    case True{}:
      Parsed{SrcLocal{s}}
    case False{}:
      source.git(git(s), s)

def source.at(b: Bool, +s: String) -> Parsed:
  match b:
    case True{}:
      npm(trim(String.drop(s, 4n)))
    case False{}:
      source.local(local(s), s)

# a package source string's answer (Rust `parse_source`)
def source(+s: String) -> Parsed:
  source.at(String.starts_with(s, "npm:"), s)

# Texts
# -----

# a part's name (Rust `SourcePart` Display)
def part_text(p: Part) -> String:
  match p:
    case PHost{}:
      "git host"
    case PPath{}:
      "git path"
    case PRef{}:
      "git ref"
    case PClone{}:
      "git clone URL"
    case PSpec{}:
      "npm spec"
    case PName{}:
      "npm package name"

# a defect's words (Rust `SourceDefect` Display)
def defect_text(d: Defect) -> String:
  match d:
    case DEmpty{}:
      "is empty"
    case DEmptySeg{}:
      "has an empty path segment"
    case DDot{}:
      "has a '.' or '..' segment"
    case DDrive{}:
      "has a drive-prefixed segment"
    case DBackslash{}:
      "contains a backslash"
    case DControl{}:
      "contains a control character"
    case DDash{}:
      "starts with '-'"
    case DSlash{}:
      "contains '/'"

# a refused source's text (Rust `SourceParseError` Display)
def error_text(s: String, f: Flaw) -> String:
  match f:
    case Flaw{p, d}:
      String.concat(["Invalid package source ", s, ": ", part_text(p), " ", defect_text(d)])
