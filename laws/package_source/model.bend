# eukhe: the laws of area package_source: the model (bend/package_source.bend)

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/gateway_answer.bend as Ga

# (D1) The package sources of `eukhe package`
# ---------------------------------------------
# bend/package_source.bend, run as the compiled core by
# bend/ffi_package_source.bend (eukhe-bend rules/package_source.rs; asked
# by eukhe-core packages/source.rs for `eukhe package install/remove/
# update/list`, the settings entries and the session's git remote).
# Every input is free: any text, part, defect.
#
# R1: trim (Rust `str::trim`): the leading and trailing chars that are
#     whitespace (Rust `char::is_whitespace`: Ga.space) removed.
# R2: an argument's defect (Rust `check_argument`), the first that holds:
#     empty; the first char `-` (leading dash); a char in U+0000-U+001F or
#     U+007F-U+009F (control character); a `\` (backslash); else none. A
#     relative path's defect (Rust `check_relative_path`): the argument's,
#     else that of the first `/`-separated segment with one: empty (empty
#     segment); `.` or `..` (dot segment); an ASCII letter then `:` as its
#     first two chars (drive prefix); else none.
# R3: a URL u split into a clone URL and a ref (Rust `split_ref`), where a
#     text p "splits" when its first `@` has text before and after it:
#     when u starts with `git@` and the text after it has a `:`, with h the
#     text before that first `:` and p the text after it: p splits into a
#     and r: `git@<h>:<a>` and ref r, else u and no ref; else when u has a
#     `://` and a `/` after its first `://`, with q the text up to that `/`
#     and p the text after it with its leading `/`s trimmed: p splits: `<q>/<a>`
#     and r, else u and no ref; else when u has a `/`, with h the text
#     before the first `/` and p the text after it: p splits: `<h>/<a>` and
#     r, else u and no ref; else u and no ref.
# R4: a hosted candidate c (Rust `hosted_from_url`): k the text after the
#     first `#` of c (none without one), v the text before it (all of c
#     without one); when v starts with `github:` (domain github.com),
#     `gitlab:` (gitlab.com), `bitbucket:` (bitbucket.org) or `gist:`
#     (gist.github.com), the text after that prefix split at its first `/`
#     into a non-empty user and a non-empty project: the domain, the user,
#     the project with every trailing `.git` trimmed (repeatedly), the
#     committish k; else none. (Rust also looked a protocol URL's host up in
#     a domain table, but then split the path at its first `/`, which is
#     the path's own leading `/`: the user was always empty and that lookup
#     never answered.)
# R5: a source read as a git URL (Rust `parse_git_url`) of s: t = trim(s);
#     when t starts with `git:`, u = trim(the text after it); else u = t,
#     and without a `https://`, `http://`, `ssh://` or `git://` start of u
#     (ASCII letters in either case) no git. (repo, ref) = R3 of u. The
#     candidates `<repo>#<ref>` (only with a ref), then u: the first with a
#     hosted answer (R4) that, when a ref was split, has no `@` in its
#     project is the git source: clone URL repo when repo starts with
#     `http://`, `https://`, `ssh://`, `git://` or `git@` (case as typed),
#     else `https://<repo>`; host the domain; path `<user>/<project>`; ref
#     the committish, else the split ref; pinned when either is there.
#     Without one, the generic forms of repo (Rust
#     `parse_generic_git_url`): starting with `git@`: host and path the
#     text after `git@` split at its first `:` (none: no git), clone URL
#     repo; else a protocol URL start (as above, either case): with a `/`
#     after the first `://` (none: no git), the authority between them, the
#     host its text after its last `@` up to its first `:`, the path the
#     text after that `/` with its leading `/`s trimmed, clone URL repo;
#     else repo split at its first `/` (none: no git) into a host that holds
#     a `.` or is `localhost` (else no git) and a path, clone URL
#     `https://<repo>`. The path then loses every trailing `.git`
#     (repeatedly), then its leading `/`s; an empty host, an empty path or
#     a path without `/` is no git; the ref is the split ref, pinned when
#     there is one. A git source is refused by the first that holds: a host
#     holding `/` (git host, slash); the host's relative-path defect (git
#     host); the path's (git path); the ref's argument defect (git ref);
#     the clone URL's argument defect (git clone URL); the text after the
#     clone URL's first `://` starting with `-` (git clone URL, leading
#     dash). Else the answer is the git source.
# R6: a local path (Rust `is_local_path`): trim of the value starts with
#     none of `npm:`, `git:`, `github:`, `http:`, `https:`, `ssh:`.
# R7: an npm spec (Rust `parse_npm_spec`): split at the first `@` after
#     its first char into a name and a non-empty version; else all of the
#     spec and no version.
# R8: a package source s (Rust `parse_source`): when s (as given) starts
#     with `npm:`: the spec trim(the text after it), refused (npm spec) by
#     its argument defect; the name R7's; refused (npm package name) by the
#     name's relative-path defect; else npm: the spec, the name, pinned when
#     R7 found a version. Else a local path (R6) is local s; else R5: a
#     refusal is the refusal, a git source the git source, no git local s.
# R9: the texts (Rust Display): parts `git host`, `git path`, `git ref`,
#     `git clone URL`, `npm spec`, `npm package name`; defects `is empty`,
#     `has an empty path segment`, `has a '.' or '..' segment`, `has a
#     drive-prefixed segment`, `contains a backslash`, `contains a control
#     character`, `starts with '-'`, `contains '/'`; a refused source s
#     `Invalid package source <s>: <part> <defect>`.

# Spec helpers
# ------------

# Text
# ----

def ps_is_some(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# s holds the char x
def ps_has(s: String, +x: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, x), ps_has(t, x))

def ps_lspace.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading whitespace
def ps_lspace(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ps_lspace.at(Ga.space(c), c, t, ps_lspace(t))

# s without whitespace at both ends (Rust `str::trim`)
def ps_trim(s: String) -> String:
  String.reverse(ps_lspace(String.reverse(ps_lspace(s))))

def ps_lslash.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `/`s
def ps_lslash(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      ps_lslash.at(Char.is_eq(c, '/'), c, t, ps_lslash(t))

def ps_nogit.at(b: Bool, r: String, k: String) -> String:
  match b:
    case True{}:
      k
    case False{}:
      r

# a reversed text without its leading `tig.`s, at most n of them
def ps_nogit(n: Nat, +r: String) -> String:
  match n:
    case 0n:
      r
    case 1n+p:
      ps_nogit.at(String.starts_with(r, "tig."), r, ps_nogit(p, String.drop(r, 4n)))

# s without its trailing `.git`s
def ps_unsuffix(+s: String) -> String:
  String.reverse(ps_nogit(String.length(s), String.reverse(s)))

def ps_cut.at(b: Bool, c: Char, t: String, r: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Cut>:
  match b:
    case True{}:
      Some{Ps.Cut{SNil{}, t}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Ps.Cut{h, u}:
              Some{Ps.Cut{SCon{c, h}, u}}

# s split at its first `sep` (none without one)
def ps_cut(s: String, +sep: Char) -> Maybe<&2, Ps.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      ps_cut.at(Char.is_eq(c, sep), c, t, ps_cut(t, sep))

def ps_before.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

# s up to its first `sep` (all of s without one)
def ps_before(s: String, +sep: Char) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      ps_before.at(Char.is_eq(c, sep), c, ps_before(t, sep))

def ps_proto.at(b: Bool, c: Char, t: String, r: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Cut>:
  match b:
    case True{}:
      Some{Ps.Cut{SNil{}, String.drop(t, 2n)}}
    case False{}:
      match r:
        case None{}:
          None{}
        case Some{x}:
          match x:
            case Ps.Cut{h, u}:
              Some{Ps.Cut{SCon{c, h}, u}}

# s split at its first `://` (none without one)
def ps_proto(s: String) -> Maybe<&2, Ps.Cut>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      ps_proto.at(String.starts_with(SCon{c, t}, "://"), c, t, ps_proto(t))

def ps_url.at(sc: String, m: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Url>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{a, p}:
          Some{Ps.Url{sc, a, p}}

def ps_url.of(m: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Url>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{sc, rest}:
          ps_url.at(sc, ps_cut(rest, '/'))

# s as a protocol URL: a `://`, then a `/` after it (none without both)
def ps_url(s: String) -> Maybe<&2, Ps.Url>:
  ps_url.of(ps_proto(s))

# the host of an authority: after its last `@`, up to its first `:`
def ps_host_of(a: String) -> String:
  ps_before(String.reverse(ps_before(String.reverse(a), '@')), ':')

# s starts with `https://`, `http://`, `ssh://` or `git://`, ASCII letters
# in either case
def ps_proto_url(s: String) -> Bool:
  +l = String.to_lower(s)
  Bool.or(String.starts_with(l, "https://"), Bool.or(String.starts_with(l, "http://"), Bool.or(String.starts_with(l, "ssh://"), String.starts_with(l, "git://"))))

# Checks
# ------

def ps_control(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_le(x, 31), Bool.and(U32.is_ge(x, 127), U32.is_le(x, 159)))

def ps_any_control(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(ps_control(c), ps_any_control(t))

def ps_arg.at(dash: Bool, ctl: Bool, bs: Bool) -> Maybe<&2, Ps.Defect>:
  match dash:
    case True{}:
      Some{Ps.DDash{}}
    case False{}:
      match ctl:
        case True{}:
          Some{Ps.DControl{}}
        case False{}:
          match bs:
            case True{}:
              Some{Ps.DBackslash{}}
            case False{}:
              None{}

# why a value git or npm could misread is refused (none: it is safe)
def ps_arg(s: String) -> Maybe<&2, Ps.Defect>:
  match s:
    case SNil{}:
      Some{Ps.DEmpty{}}
    case SCon{+c, +t}:
      ps_arg.at(Char.is_eq(c, '-'), ps_any_control(SCon{c, t}), ps_has(SCon{c, t}, Chr{92}))

def ps_seg.at(dot: Bool, drive: Bool) -> Maybe<&2, Ps.Defect>:
  match dot:
    case True{}:
      Some{Ps.DDot{}}
    case False{}:
      match drive:
        case True{}:
          Some{Ps.DDrive{}}
        case False{}:
          None{}

# why a path segment is refused (none: a plain name)
def ps_seg(s: String) -> Maybe<&2, Ps.Defect>:
  match s:
    case SNil{}:
      Some{Ps.DEmptySeg{}}
    case SCon{+c, +t}:
      ps_seg.at(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, "..")), Bool.and(Char.is_alpha(c), String.starts_with(t, ":")))

def ps_first.at(m: Maybe<&2, Ps.Defect>, r: Maybe<&2, Ps.Defect>) -> Maybe<&2, Ps.Defect>:
  match m:
    case None{}:
      r
    case Some{d}:
      Some{d}

# the first segment's defect
def ps_segs(xs: List<&2, String>) -> Maybe<&2, Ps.Defect>:
  match xs:
    case Nil{}:
      None{}
    case h <> t:
      ps_first.at(ps_seg(h), ps_segs(t))

# why a relative path is refused: as an argument, then segment by segment
def ps_rel(+s: String) -> Maybe<&2, Ps.Defect>:
  ps_first.at(ps_arg(s), ps_segs(String.split(s, '/')))

# Git URLs
# --------

def ps_refcut.ok(e: Bool, a: String, b: String) -> Maybe<&2, Ps.Cut>:
  match e:
    case True{}:
      None{}
    case False{}:
      Some{Ps.Cut{a, b}}

def ps_refcut.at(m: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Cut>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{+a, +b}:
          ps_refcut.ok(Bool.or(String.is_empty(a), String.is_empty(b)), a, b)

# s split at its first `@` into a path and a ref, both non-empty
def ps_refcut(s: String) -> Maybe<&2, Ps.Cut>:
  ps_refcut.at(ps_cut(s, '@'))

def ps_sref.scp.at(h: String, m: Maybe<&2, Ps.Cut>, u: String) -> Ps.Refd:
  match m:
    case None{}:
      Ps.Refd{u, None{}}
    case Some{x}:
      match x:
        case Ps.Cut{p, r}:
          Ps.Refd{String.concat(["git@", h, ":", p]), Some{r}}

def ps_sref.url.at(sc: String, a: String, m: Maybe<&2, Ps.Cut>, u: String) -> Ps.Refd:
  match m:
    case None{}:
      Ps.Refd{u, None{}}
    case Some{x}:
      match x:
        case Ps.Cut{p, r}:
          Ps.Refd{String.concat([sc, "://", a, "/", p]), Some{r}}

def ps_sref.short.at(h: String, m: Maybe<&2, Ps.Cut>, u: String) -> Ps.Refd:
  match m:
    case None{}:
      Ps.Refd{u, None{}}
    case Some{x}:
      match x:
        case Ps.Cut{p, r}:
          Ps.Refd{String.concat([h, "/", p]), Some{r}}

def ps_sref.short(m: Maybe<&2, Ps.Cut>, u: String) -> Ps.Refd:
  match m:
    case None{}:
      Ps.Refd{u, None{}}
    case Some{x}:
      match x:
        case Ps.Cut{h, p}:
          ps_sref.short.at(h, ps_refcut(p), u)

def ps_sref.url(m: Maybe<&2, Ps.Url>, +u: String) -> Ps.Refd:
  match m:
    case None{}:
      ps_sref.short(ps_cut(u, '/'), u)
    case Some{x}:
      match x:
        case Ps.Url{sc, a, p}:
          ps_sref.url.at(sc, a, ps_refcut(ps_lslash(p)), u)

def ps_sref.scp(m: Maybe<&2, Ps.Cut>, +u: String) -> Ps.Refd:
  match m:
    case None{}:
      ps_sref.url(ps_url(u), u)
    case Some{x}:
      match x:
        case Ps.Cut{h, p}:
          ps_sref.scp.at(h, ps_refcut(p), u)

def ps_sref.at(b: Bool, +u: String) -> Ps.Refd:
  match b:
    case True{}:
      ps_sref.scp(ps_cut(String.drop(u, 4n), ':'), u)
    case False{}:
      ps_sref.url(ps_url(u), u)

# a URL split into the clone URL and its ref: `git@host:path@ref`, a
# protocol URL's path `@ref`, `host/path@ref`
def ps_sref(+u: String) -> Ps.Refd:
  ps_sref.at(String.starts_with(u, "git@"), u)

def ps_short.at(a: Bool, b: Bool, c: Bool, d: Bool, +u: String) -> Maybe<&2, Ps.Cut>:
  match a:
    case True{}:
      Some{Ps.Cut{"github.com", String.drop(u, 7n)}}
    case False{}:
      match b:
        case True{}:
          Some{Ps.Cut{"gitlab.com", String.drop(u, 7n)}}
        case False{}:
          match c:
            case True{}:
              Some{Ps.Cut{"bitbucket.org", String.drop(u, 10n)}}
            case False{}:
              match d:
                case True{}:
                  Some{Ps.Cut{"gist.github.com", String.drop(u, 5n)}}
                case False{}:
                  None{}

# a hosted shortcut's domain and the text after the shortcut
def ps_short(+u: String) -> Maybe<&2, Ps.Cut>:
  ps_short.at(String.starts_with(u, "github:"), String.starts_with(u, "gitlab:"), String.starts_with(u, "bitbucket:"), String.starts_with(u, "gist:"), u)

def ps_hosted.ok(e: Bool, d: String, u: String, p: String, k: Maybe<&2, String>) -> Maybe<&2, Ps.Hosted>:
  match e:
    case True{}:
      None{}
    case False{}:
      Some{Ps.Hosted{d, u, ps_unsuffix(p), k}}

def ps_hosted.parts(d: String, m: Maybe<&2, Ps.Cut>, k: Maybe<&2, String>) -> Maybe<&2, Ps.Hosted>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{+u, +p}:
          ps_hosted.ok(Bool.or(String.is_empty(u), String.is_empty(p)), d, u, p, k)

def ps_hosted.short(m: Maybe<&2, Ps.Cut>, k: Maybe<&2, String>) -> Maybe<&2, Ps.Hosted>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{d, rest}:
          ps_hosted.parts(d, ps_cut(rest, '/'), k)

def ps_hosted.at(m: Maybe<&2, Ps.Cut>, c: String) -> Maybe<&2, Ps.Hosted>:
  match m:
    case None{}:
      ps_hosted.short(ps_short(c), None{})
    case Some{x}:
      match x:
        case Ps.Cut{u, k}:
          ps_hosted.short(ps_short(u), Some{k})

# a hosted shortcut candidate `<shortcut>user/project[#committish]`
def ps_hosted(+c: String) -> Maybe<&2, Ps.Hosted>:
  ps_hosted.at(ps_cut(c, '#'), c)

def ps_keep.at(drop: Bool, h: Ps.Hosted) -> Maybe<&2, Ps.Hosted>:
  match drop:
    case True{}:
      None{}
    case False{}:
      Some{h}

def ps_keep.of(h: Ps.Hosted, +r: Bool) -> Maybe<&2, Ps.Hosted>:
  match h:
    case Ps.Hosted{d, u, +p, k}:
      ps_keep.at(Bool.and(r, ps_has(p, '@')), Ps.Hosted{d, u, p, k})

# a candidate, dropped when a ref was split off and its project holds `@`
def ps_keep(m: Maybe<&2, Ps.Hosted>, +r: Bool) -> Maybe<&2, Ps.Hosted>:
  match m:
    case None{}:
      None{}
    case Some{h}:
      ps_keep.of(h, r)

def ps_pick(a: Maybe<&2, Ps.Hosted>, b: Maybe<&2, Ps.Hosted>) -> Maybe<&2, Ps.Hosted>:
  match a:
    case None{}:
      b
    case Some{h}:
      Some{h}

def ps_cand.at(repo: String, m: Maybe<&2, String>) -> Maybe<&2, Ps.Hosted>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      ps_keep(ps_hosted(String.concat([repo, "#", r])), True{})

# the first candidate: the clone URL `#` the split ref (none without a ref)
def ps_cand(rd: Ps.Refd) -> Maybe<&2, Ps.Hosted>:
  match rd:
    case Ps.Refd{repo, m}:
      ps_cand.at(repo, m)

def ps_or_ref(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case None{}:
      b
    case Some{x}:
      Some{x}

def ps_https.at(b: Bool, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      String.append("https://", r)

# the clone URL: `https://` before one without a scheme or `git@`
def ps_https(+r: String) -> String:
  ps_https.at(Bool.or(String.starts_with(r, "http://"), Bool.or(String.starts_with(r, "https://"), Bool.or(String.starts_with(r, "ssh://"), Bool.or(String.starts_with(r, "git://"), String.starts_with(r, "git@"))))), r)

def ps_from_hosted.at(h: Ps.Hosted, repo: String, +r: Maybe<&2, String>) -> Ps.GitSrc:
  match h:
    case Ps.Hosted{d, u, p, +k}:
      Ps.GitSrc{ps_https(repo), d, String.concat([u, "/", p]), ps_or_ref(k, r), Bool.or(ps_is_some(k), ps_is_some(r))}

# a hosted candidate's git source
def ps_from_hosted(h: Ps.Hosted, rd: Ps.Refd) -> Ps.GitSrc:
  match rd:
    case Ps.Refd{repo, r}:
      ps_from_hosted.at(h, repo, r)

def ps_shape.at(bad: Bool, h: String, q: String, clone: String, +r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match bad:
    case True{}:
      None{}
    case False{}:
      Some{Ps.GitSrc{clone, h, q, r, ps_is_some(r)}}

# a generic source: the path without trailing `.git`s, then leading `/`s;
# none for an empty host or path, or a path of one segment
def ps_shape(+h: String, p: String, clone: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  +q = ps_lslash(ps_unsuffix(p))
  ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(q), Bool.not(ps_has(q, '/')))), h, q, clone, r)

def ps_generic.scp(m: Maybe<&2, Ps.Cut>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{h, p}:
          ps_shape(h, p, repo, r)

def ps_generic.url(m: Maybe<&2, Ps.Url>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Url{sc, a, p}:
          ps_shape(ps_host_of(a), ps_lslash(p), repo, r)

def ps_generic.dot(ok: Bool, h: String, p: String, repo: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match ok:
    case True{}:
      ps_shape(h, p, String.append("https://", repo), r)
    case False{}:
      None{}

def ps_generic.short(m: Maybe<&2, Ps.Cut>, repo: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{+h, p}:
          ps_generic.dot(Bool.or(ps_has(h, '.'), String.eq(h, "localhost")), h, p, repo, r)

def ps_generic.at(scp: Bool, pu: Bool, +repo: String, r: Maybe<&2, String>) -> Maybe<&2, Ps.GitSrc>:
  match scp:
    case True{}:
      ps_generic.scp(ps_cut(String.drop(repo, 4n), ':'), repo, r)
    case False{}:
      match pu:
        case True{}:
          ps_generic.url(ps_url(repo), repo, r)
        case False{}:
          ps_generic.short(ps_cut(repo, '/'), repo, r)

# a generic git source: `git@host:path`, a protocol URL, or `host/path`
# whose host holds a `.` or is `localhost`
def ps_generic(rd: Ps.Refd) -> Maybe<&2, Ps.GitSrc>:
  match rd:
    case Ps.Refd{+repo, r}:
      ps_generic.at(String.starts_with(repo, "git@"), ps_proto_url(repo), repo, r)

def ps_found.at(m: Maybe<&2, Ps.Hosted>, +rd: Ps.Refd) -> Maybe<&2, Ps.GitSrc>:
  match m:
    case None{}:
      ps_generic(rd)
    case Some{h}:
      Some{ps_from_hosted(h, rd)}

def ps_ref_some(rd: Ps.Refd) -> Bool:
  match rd:
    case Ps.Refd{repo, m}:
      ps_is_some(m)

# a git URL's source: a hosted candidate (the split one, then the URL),
# else the generic forms
def ps_found(u: String, +rd: Ps.Refd) -> Maybe<&2, Ps.GitSrc>:
  ps_found.at(ps_pick(ps_cand(rd), ps_keep(ps_hosted(u), ps_ref_some(rd))), rd)

def ps_on(p: Ps.Part, m: Maybe<&2, Ps.Defect>) -> Maybe<&2, Ps.Flaw>:
  match m:
    case None{}:
      None{}
    case Some{d}:
      Some{Ps.Flaw{p, d}}

def ps_host.at(b: Bool, +h: String) -> Maybe<&2, Ps.Defect>:
  match b:
    case True{}:
      Some{Ps.DSlash{}}
    case False{}:
      ps_rel(h)

def ps_gref(m: Maybe<&2, String>) -> Maybe<&2, Ps.Flaw>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      ps_on(Ps.PRef{}, ps_arg(r))

def ps_dash.ok(b: Bool) -> Maybe<&2, Ps.Flaw>:
  match b:
    case True{}:
      Some{Ps.Flaw{Ps.PClone{}, Ps.DDash{}}}
    case False{}:
      None{}

def ps_dash.at(m: Maybe<&2, Ps.Cut>) -> Maybe<&2, Ps.Flaw>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match x:
        case Ps.Cut{s, a}:
          ps_dash.ok(String.starts_with(a, "-"))

def ps_flaw.or(m: Maybe<&2, Ps.Flaw>, r: Maybe<&2, Ps.Flaw>) -> Maybe<&2, Ps.Flaw>:
  match m:
    case None{}:
      r
    case Some{f}:
      Some{f}

# the first refused part: the host, the path, the ref, the clone URL, then
# a clone URL whose authority starts with `-`
def ps_flaws(g: Ps.GitSrc) -> Maybe<&2, Ps.Flaw>:
  match g:
    case Ps.GitSrc{+repo, +h, p, r, n}:
      ps_flaw.or(ps_on(Ps.PHost{}, ps_host.at(ps_has(h, '/'), h)), ps_flaw.or(ps_on(Ps.PPath{}, ps_rel(p)), ps_flaw.or(ps_gref(r), ps_flaw.or(ps_on(Ps.PClone{}, ps_arg(repo)), ps_dash.at(ps_proto(repo))))))

def ps_checked.at(m: Maybe<&2, Ps.Flaw>, g: Ps.GitSrc) -> Ps.GitAns:
  match m:
    case None{}:
      Ps.IsGit{g}
    case Some{f}:
      Ps.BadGit{f}

def ps_checked(m: Maybe<&2, Ps.GitSrc>) -> Ps.GitAns:
  match m:
    case None{}:
      Ps.NoGit{}
    case Some{+g}:
      ps_checked.at(ps_flaws(g), g)

def ps_git.gate(go: Bool, +u: String) -> Ps.GitAns:
  match go:
    case True{}:
      ps_checked(ps_found(u, ps_sref(u)))
    case False{}:
      Ps.NoGit{}

def ps_git.at(b: Bool, +t: String) -> Ps.GitAns:
  match b:
    case True{}:
      ps_git.gate(True{}, ps_trim(String.drop(t, 4n)))
    case False{}:
      ps_git.gate(ps_proto_url(t), t)

# a source read as a git URL (Rust `parse_git_url`)
def ps_git(s: String) -> Ps.GitAns:
  +t = ps_trim(s)
  ps_git.at(String.starts_with(t, "git:"), t)

# Sources
# -------

# a value that is no `npm:`/`git:`/`github:`/`http:`/`https:`/`ssh:`
# source once trimmed (Rust `is_local_path`)
def ps_local(s: String) -> Bool:
  +t = ps_trim(s)
  Bool.not(Bool.or(String.starts_with(t, "npm:"), Bool.or(String.starts_with(t, "git:"), Bool.or(String.starts_with(t, "github:"), Bool.or(String.starts_with(t, "http:"), Bool.or(String.starts_with(t, "https:"), String.starts_with(t, "ssh:")))))))

def ps_npm_spec.ok(e: Bool, c: Char, h: String, v: String, t: String) -> Ps.NpmSpec:
  match e:
    case True{}:
      Ps.NpmSpec{SCon{c, t}, None{}}
    case False{}:
      Ps.NpmSpec{SCon{c, h}, Some{v}}

def ps_npm_spec.at(m: Maybe<&2, Ps.Cut>, c: Char, t: String) -> Ps.NpmSpec:
  match m:
    case None{}:
      Ps.NpmSpec{SCon{c, t}, None{}}
    case Some{x}:
      match x:
        case Ps.Cut{h, +v}:
          ps_npm_spec.ok(String.is_empty(v), c, h, v, t)

# an npm spec's name and pinned version: split at the first `@` after the
# first char, when the version is not empty (Rust `parse_npm_spec`)
def ps_npm_spec(s: String) -> Ps.NpmSpec:
  match s:
    case SNil{}:
      Ps.NpmSpec{SNil{}, None{}}
    case SCon{+c, +t}:
      ps_npm_spec.at(ps_cut(t, '@'), c, t)

def ps_npm.ok(m: Maybe<&2, Ps.Defect>, name: String, pinned: Bool, spec: String) -> Ps.Parsed:
  match m:
    case None{}:
      Ps.Parsed{Ps.SrcNpm{Ps.NpmSrc{spec, name, pinned}}}
    case Some{d}:
      Ps.Refused{Ps.Flaw{Ps.PName{}, d}}

def ps_npm.name(ns: Ps.NpmSpec, spec: String) -> Ps.Parsed:
  match ns:
    case Ps.NpmSpec{+name, v}:
      ps_npm.ok(ps_rel(name), name, ps_is_some(v), spec)

def ps_npm.at(m: Maybe<&2, Ps.Defect>, +spec: String) -> Ps.Parsed:
  match m:
    case None{}:
      ps_npm.name(ps_npm_spec(spec), spec)
    case Some{d}:
      Ps.Refused{Ps.Flaw{Ps.PSpec{}, d}}

# an `npm:` source: the spec (trimmed) and its package name checked
def ps_npm(+spec: String) -> Ps.Parsed:
  ps_npm.at(ps_arg(spec), spec)

def ps_source.git(a: Ps.GitAns, s: String) -> Ps.Parsed:
  match a:
    case Ps.NoGit{}:
      Ps.Parsed{Ps.SrcLocal{s}}
    case Ps.IsGit{g}:
      Ps.Parsed{Ps.SrcGit{g}}
    case Ps.BadGit{f}:
      Ps.Refused{f}

def ps_source.local(b: Bool, +s: String) -> Ps.Parsed:
  match b:
    case True{}:
      Ps.Parsed{Ps.SrcLocal{s}}
    case False{}:
      ps_source.git(ps_git(s), s)

def ps_source.at(b: Bool, +s: String) -> Ps.Parsed:
  match b:
    case True{}:
      ps_npm(ps_trim(String.drop(s, 4n)))
    case False{}:
      ps_source.local(ps_local(s), s)

# a package source string's answer (Rust `parse_source`)
def ps_source(+s: String) -> Ps.Parsed:
  ps_source.at(String.starts_with(s, "npm:"), s)

# Texts
# -----

# a part's name (Rust `SourcePart` Display)
def ps_part_text(p: Ps.Part) -> String:
  match p:
    case Ps.PHost{}:
      "git host"
    case Ps.PPath{}:
      "git path"
    case Ps.PRef{}:
      "git ref"
    case Ps.PClone{}:
      "git clone URL"
    case Ps.PSpec{}:
      "npm spec"
    case Ps.PName{}:
      "npm package name"

# a defect's words (Rust `SourceDefect` Display)
def ps_defect_text(d: Ps.Defect) -> String:
  match d:
    case Ps.DEmpty{}:
      "is empty"
    case Ps.DEmptySeg{}:
      "has an empty path segment"
    case Ps.DDot{}:
      "has a '.' or '..' segment"
    case Ps.DDrive{}:
      "has a drive-prefixed segment"
    case Ps.DBackslash{}:
      "contains a backslash"
    case Ps.DControl{}:
      "contains a control character"
    case Ps.DDash{}:
      "starts with '-'"
    case Ps.DSlash{}:
      "contains '/'"

# a refused source's text (Rust `SourceParseError` Display)
def ps_error_text(s: String, f: Ps.Flaw) -> String:
  match f:
    case Ps.Flaw{p, d}:
      String.concat(["Invalid package source ", s, ": ", ps_part_text(p), " ", ps_defect_text(d)])

# Laws: the model
# ---------------

# LAW package_source_source_spec (R1-R8): every source string answers the
# spec's source or refusal
# EXCLUDES: an `npm:` spec read untrimmed or as a git URL, a check skipped
#   or run in another order, another part or defect named, a hosted
#   candidate tried in another order or kept with an `@` project, a `.git`
#   trimmed once only, a clone URL without its `https://`, a ref kept on the
#   clone URL, a local path read as git, a `git://` source read as git
law package_source_source_spec:
  for +s: String
  {Ps.source(s) == ps_source(s) : Ps.Parsed}

# LAW package_source_git_spec (R1-R5): every source read as a git URL
# answers the spec's git source, refusal or none
# EXCLUDES: a protocol checked case-sensitively, the `git:` prefix kept,
#   the host read before the last `@`, a port kept on the host, a path of
#   one segment accepted, a dash-led authority accepted
law package_source_git_spec:
  for +s: String
  {Ps.git(s) == ps_git(s) : Ps.GitAns}

# LAW package_source_local_spec (R1, R6): every value is local as the spec
# says
# EXCLUDES: an untrimmed check, a prefix missing or added
law package_source_local_spec:
  for +s: String
  {Ps.local(s) == ps_local(s) : Bool}

# LAW package_source_npm_spec_spec (R7): every npm spec splits as the spec
# EXCLUDES: a scope `@` read as the version, an empty version kept, the
#   last `@` taken
law package_source_npm_spec_spec:
  for +s: String
  {Ps.npm_spec(s) == ps_npm_spec(s) : Ps.NpmSpec}

# LAW package_source_part_text_spec (R9): every part's name is the spec's
# EXCLUDES: a changed or swapped name
law package_source_part_text_spec:
  for +p: Ps.Part
  {Ps.part_text(p) == ps_part_text(p) : String}

# LAW package_source_defect_text_spec (R9): every defect's words are the
# spec's
# EXCLUDES: changed or swapped words
law package_source_defect_text_spec:
  for +d: Ps.Defect
  {Ps.defect_text(d) == ps_defect_text(d) : String}

# LAW package_source_error_text_spec (R9): every refused source's text is
# the spec's
# EXCLUDES: the input, part or defect left out or reordered
law package_source_error_text_spec:
  for +s: String
  for +f: Ps.Flaw
  {Ps.error_text(s, f) == ps_error_text(s, f) : String}

# LAW package_source_kind_example (R6-R8): anchor: Rust's npm and local
# sources
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_kind_example:
  {[Ps.source("npm:@scope/pkg@1.2.3"), Ps.source("npm: pkg "), Ps.source("/absolute/path/to/package"), Ps.source("../packages/agent-timers"), Ps.source("github.com/user/repo"), Ps.source("git://localhost/fixtures/repo.git")] == [Ps.Parsed{Ps.SrcNpm{Ps.NpmSrc{"@scope/pkg@1.2.3", "@scope/pkg", True{}}}}, Ps.Parsed{Ps.SrcNpm{Ps.NpmSrc{"pkg", "pkg", False{}}}}, Ps.Parsed{Ps.SrcLocal{"/absolute/path/to/package"}}, Ps.Parsed{Ps.SrcLocal{"../packages/agent-timers"}}, Ps.Parsed{Ps.SrcLocal{"github.com/user/repo"}}, Ps.Parsed{Ps.SrcLocal{"git://localhost/fixtures/repo.git"}}] : List<&2, Ps.Parsed>}

# LAW package_source_git_example (R3-R5, R8): anchor: Rust's git sources
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_git_example:
  {[Ps.source("https://github.com/user/repo"), Ps.source("git:https://github.com/user/repo"), Ps.source("https://github.com/user/repo@v1.2.3"), Ps.source("https://github.com/user/repo@feature/branch"), Ps.source("git:github.com/user/repo@v1"), Ps.source("https://github.com/user/repo.git"), Ps.source("https://codeberg.org/user/repo"), Ps.source("git:git@github.com:user/repo"), Ps.source("git:ssh://git@github.com/user/repo"), Ps.source("git:gist:u/p@v"), Ps.source("git:github:u/r.git#x")] == [Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo", "github.com", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo", "github.com", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo", "github.com", "user/repo", Some{"v1.2.3"}, True{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo", "github.com", "user/repo", Some{"feature/branch"}, True{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo", "github.com", "user/repo", Some{"v1"}, True{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github.com/user/repo.git", "github.com", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://codeberg.org/user/repo", "codeberg.org", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"git@github.com:user/repo", "github.com", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"ssh://git@github.com/user/repo", "github.com", "user/repo", None{}, False{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://gist:u/p", "gist.github.com", "u/p", Some{"v"}, True{}}}}, Ps.Parsed{Ps.SrcGit{Ps.GitSrc{"https://github:u/r.git#x", "github.com", "u/r", Some{"x"}, True{}}}}] : List<&2, Ps.Parsed>}

# LAW package_source_refuse_example (R2, R5, R8): anchor: Rust's refused
# sources that escape the install root
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_refuse_example:
  {[Ps.source("git:git@h.io:../../../../tmp/a/b"), Ps.source("git:git@/home/u:x/y"), Ps.source("git:github:../x"), Ps.source("git:../../x/y"), Ps.source("git:github.com/user//repo"), Ps.source("git:git@h.io:user\\..\\x/y"), Ps.source("git:git@h.io:C:/x")] == [Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DDot{}}}, Ps.Refused{Ps.Flaw{Ps.PHost{}, Ps.DSlash{}}}, Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DDot{}}}, Ps.Refused{Ps.Flaw{Ps.PHost{}, Ps.DDot{}}}, Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DEmptySeg{}}}, Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DBackslash{}}}, Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DDrive{}}}] : List<&2, Ps.Parsed>}

# LAW package_source_option_example (R2, R5, R8): anchor: Rust's refused
# sources read as options or holding a control char
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_option_example:
  {[Ps.source("git:git@h.io:user/repo\u{0}"), Ps.source("git:git@-oProxyCommand=x.io:user/repo"), Ps.source("git:github.com/user/repo@--orphan=x"), Ps.source("https://github.com/user/repo@-x"), Ps.source("ssh://-oProxyCommand=x@h.io/user/repo"), Ps.source("npm:--registry=http://evil.test"), Ps.source("npm:../../x")] == [Ps.Refused{Ps.Flaw{Ps.PPath{}, Ps.DControl{}}}, Ps.Refused{Ps.Flaw{Ps.PHost{}, Ps.DDash{}}}, Ps.Refused{Ps.Flaw{Ps.PRef{}, Ps.DDash{}}}, Ps.Refused{Ps.Flaw{Ps.PRef{}, Ps.DDash{}}}, Ps.Refused{Ps.Flaw{Ps.PClone{}, Ps.DDash{}}}, Ps.Refused{Ps.Flaw{Ps.PSpec{}, Ps.DDash{}}}, Ps.Refused{Ps.Flaw{Ps.PName{}, Ps.DDot{}}}] : List<&2, Ps.Parsed>}

# LAW package_source_npm_spec_example (R6, R7): anchor: Rust's npm specs and
# local values
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_npm_spec_example:
  {[Ps.npm_spec("@scope/pkg@1.2.3"), Ps.npm_spec("pkg"), Ps.npm_spec("@scope/pkg"), Ps.npm_spec("pkg@"), Ps.npm_spec("@"), Ps.npm_spec("")] == [Ps.NpmSpec{"@scope/pkg", Some{"1.2.3"}}, Ps.NpmSpec{"pkg", None{}}, Ps.NpmSpec{"@scope/pkg", None{}}, Ps.NpmSpec{"pkg@", None{}}, Ps.NpmSpec{"@", None{}}, Ps.NpmSpec{"", None{}}] : List<&2, Ps.NpmSpec>} & {[Ps.local(" npm:x"), Ps.local("github:u/r"), Ps.local("https:x"), Ps.local("ssh:x"), Ps.local("gitlab:u/r"), Ps.local("./x"), Ps.local("HTTP://x")] == [False{}, False{}, False{}, False{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW package_source_text_example (R9): anchor: Rust's texts
# EXCLUDES: a spec that drifts from the Rust it replaced
law package_source_text_example:
  {[Ps.error_text("npm:../../x", Ps.Flaw{Ps.PName{}, Ps.DDot{}}), Ps.error_text("x", Ps.Flaw{Ps.PClone{}, Ps.DDash{}}), Ps.part_text(Ps.PRef{}), Ps.defect_text(Ps.DSlash{})] == ["Invalid package source npm:../../x: npm package name has a '.' or '..' segment", "Invalid package source x: git clone URL starts with '-'", "git ref", "contains '/'"] : List<&2, String>}
