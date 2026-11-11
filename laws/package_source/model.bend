# eukhe: the laws of area package_source: the model (bend/package_source.bend)

import Base
import ../../bend/package_source.bend as Ps

# (D1) The package sources of `eukhe package`
# ---------------------------------------------
# bend/package_source.bend, run as the compiled core by
# bend/ffi_package_source.bend (eukhe-bend rules/package_source.rs; asked
# by eukhe-core packages/source.rs for `eukhe package install/remove/
# update/list`, the settings entries and the session's git remote).
# Every input is free: any text, part, defect.
#
# R1: trim (Rust `str::trim`): the leading and trailing chars that are
#     whitespace (Rust `char::is_whitespace`, Unicode White_Space: ps_white)
#     removed.
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

# Terms
# -----

def ps_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), ps_in(x, rest))

# R1: Unicode White_Space (Unicode PropList.txt; Rust `char::is_whitespace`),
# by code point
def ps_ws() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def ps_white(c: Char) -> Bool:
  ps_in(Char.to_u32(c), ps_ws())

# R1: a text of White_Space only (the empty text too)
def ps_blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ps_white(c), ps_blank(t))

# s holds the char x
def ps_has(s: String, +x: Char) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Char.is_eq(c, x), ps_has(t, x))

# R2: a control character: U+0000-U+001F or U+007F-U+009F
def ps_control(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(U32.is_le(x, 31), Bool.and(U32.is_ge(x, 127), U32.is_le(x, 159)))

# R2: no char of s is a control character or a backslash
def ps_clean(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.and(Bool.not(Bool.or(ps_control(c), Char.is_eq(c, Chr{92}))), ps_clean(t))

# R2: an argument git or npm cannot read as an option or a path escape: not
# empty, not led by `-`, no control character, no backslash
def ps_arg_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.and(Bool.not(Char.is_eq(c, '-')), ps_clean(SCon{c, t}))

# R2: a path segment that names a plain entry: not empty, not `.` or `..`,
# not an ASCII letter then `:` (a drive)
def ps_seg_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.and(Bool.not(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, ".."))), Bool.not(Bool.and(Char.is_alpha(c), String.starts_with(t, ":"))))

def ps_segs_ok(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(ps_seg_ok(x), ps_segs_ok(t))

# R2: a relative path that stays under the root it is joined to: an
# argument whose every `/`-separated segment is plain
def ps_rel_ok(+s: String) -> Bool:
  Bool.and(ps_arg_ok(s), ps_segs_ok(String.split(s, '/')))

def ps_auth_ok.at(b: Bool, t: String, r: Bool) -> Bool:
  match b:
    case True{}:
      Bool.not(String.starts_with(String.drop(t, 2n), "-"))
    case False{}:
      r

# R5: the text after the first `://` of s (when s has one) does not start
# with `-`
def ps_auth_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +t}:
      ps_auth_ok.at(String.starts_with(SCon{c, t}, "://"), t, ps_auth_ok(t))

# R5: a ref git cannot misread: none, or an argument
def ps_ref_ok(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      ps_arg_ok(r)

# R2, R5: a git source safe to fetch into the install root: its host holds
# no `/` and is a relative path, its path is a relative path, its ref (if
# any) an argument, its clone URL an argument whose authority does not
# start with `-`
def ps_git_ok(g: Ps.GitSrc) -> Bool:
  match g:
    case Ps.GitSrc{+repo, +h, p, r, n}:
      Bool.and(Bool.not(ps_has(h, '/')), Bool.and(ps_rel_ok(h), Bool.and(ps_rel_ok(p), Bool.and(ps_ref_ok(r), Bool.and(ps_arg_ok(repo), ps_auth_ok(repo))))))

# R2, R5, R8: an accepted source safe to install: an npm spec that is an
# argument with a relative-path package name, a safe git source; a local
# path as given
def ps_src_ok(x: Ps.Src) -> Bool:
  match x:
    case Ps.SrcNpm{m}:
      match m:
        case Ps.NpmSrc{spec, name, n}:
          Bool.and(ps_arg_ok(spec), ps_rel_ok(name))
    case Ps.SrcGit{g}:
      ps_git_ok(g)
    case Ps.SrcLocal{p}:
      True{}

# R7: s holds no `@`
def ps_no_at(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, '@')), ps_no_at(t))

# Laws: the safety of an accepted source (R2, R5, R8)
# ---------------------------------------------------

# LAW package_source_git_safe (R2, R5): for every text read as a git URL,
# a git source it answers has a host without `/`, a host and a path that
# are relative paths (no empty, `.`, `..` or drive segment), a ref (when
# there is one) and a clone URL that are arguments (not empty, not led by
# `-`, no control character, no backslash), and no `-` right after the
# clone URL's `://`
# EXCLUDES: a path escaping the install root (`..`, `//`, `C:`, `\`), a
#   host, ref or clone URL git reads as an option, a control char passed to
#   git, a check skipped for one part
law package_source_git_safe:
  for +s: String
  for +g: Ps.GitSrc
  for got: {Ps.git(s) == Ps.IsGit{g} : Ps.GitAns}
  {ps_git_ok(g) == True{} : Bool}

# LAW package_source_source_safe (R2, R5, R8): for every package source
# string, a source it accepts is safe: an npm spec is an argument and its
# package name a relative path; a git source is safe as in
# package_source_git_safe
# EXCLUDES: an `npm:` spec read as an option (`npm:--registry=..`), a
#   package name escaping node_modules (`npm:../../x`), a git source
#   accepted past a failed check
law package_source_source_safe:
  for +s: String
  for +x: Ps.Src
  for got: {Ps.source(s) == Ps.Parsed{x} : Ps.Parsed}
  {ps_src_ok(x) == True{} : Bool}

# Laws: the shapes (R1, R5-R7)
# ----------------------------

# LAW package_source_git_trims (R1, R5): for every text s and every two
# White_Space texts w1 and w2, s between them reads as a git URL as s does
# EXCLUDES: whitespace (ASCII or Unicode) at either end read into the URL,
#   a `git:` or protocol prefix missed after leading whitespace
law package_source_git_trims:
  for +w1: String
  for b1: {ps_blank(w1) == True{} : Bool}
  for +s: String
  for +w2: String
  for b2: {ps_blank(w2) == True{} : Bool}
  {Ps.git(String.append(w1, String.append(s, w2))) == Ps.git(s) : Ps.GitAns}

# LAW package_source_local_prefixed (R1, R6): for every White_Space text w
# and every text x, w then `npm:`, `git:`, `github:`, `http:`, `https:` or
# `ssh:` then x is not a local path
# EXCLUDES: a prefix missing from the table, a check that skips leading
#   whitespace badly, a prefix matched only as the whole value
law package_source_local_prefixed:
  for +w: String
  for +b: {ps_blank(w) == True{} : Bool}
  for +x: String
  {Ps.local(String.append(w, String.append("npm:", x))) == False{} : Bool} &
  {Ps.local(String.append(w, String.append("git:", x))) == False{} : Bool} &
  {Ps.local(String.append(w, String.append("github:", x))) == False{} : Bool} &
  {Ps.local(String.append(w, String.append("http:", x))) == False{} : Bool} &
  {Ps.local(String.append(w, String.append("https:", x))) == False{} : Bool} &
  {Ps.local(String.append(w, String.append("ssh:", x))) == False{} : Bool}

# LAW package_source_local_plain (R1, R6): for every White_Space text w,
# every char c that is not White_Space and none of `n`, `g`, `h`, `s`
# (the first letters of the prefixes), and every text x, w then c then x is
# a local path
# EXCLUDES: a path (`/`, `.`, `~`, a name) refused as local, a test that
#   reads past leading whitespace into a refusal
law package_source_local_plain:
  for +w: String
  for b: {ps_blank(w) == True{} : Bool}
  for +c: Char
  for cw: {ps_white(c) == False{} : Bool}
  for cn: {Bool.or(Char.is_eq(c, 'n'), Bool.or(Char.is_eq(c, 'g'), Bool.or(Char.is_eq(c, 'h'), Char.is_eq(c, 's')))) == False{} : Bool}
  for +x: String
  {Ps.local(String.append(w, SCon{c, x})) == True{} : Bool}

# LAW package_source_npm_spec_first_at (R7): for every char c, every text t
# without `@` and every non-empty text v, the spec c, t, `@`, v names the
# package c t and pins the version v
# EXCLUDES: a scope's leading `@` read as the version mark, the last `@`
#   taken, the version left on the name
law package_source_npm_spec_first_at:
  for +c: Char
  for +t: String
  for na: {ps_no_at(t) == True{} : Bool}
  for +x: Char
  for +v: String
  {Ps.npm_spec(String.append(SCon{c, t}, SCon{'@', SCon{x, v}})) == Ps.NpmSpec{SCon{c, t}, Some{SCon{x, v}}} : Ps.NpmSpec}

# LAW package_source_npm_spec_whole (R7): the empty spec, and for every char
# c and text t without `@` the spec c t and the spec c t `@`, name the whole
# spec with no version (with package_source_npm_spec_first_at this fixes
# every spec)
# EXCLUDES: an empty version pinned, a leading `@` read as the version
#   mark, a name cut short
law package_source_npm_spec_whole:
  for +c: Char
  for +t: String
  for +na: {ps_no_at(t) == True{} : Bool}
  {Ps.npm_spec("") == Ps.NpmSpec{"", None{}} : Ps.NpmSpec} &
  {Ps.npm_spec(SCon{c, t}) == Ps.NpmSpec{SCon{c, t}, None{}} : Ps.NpmSpec} &
  {Ps.npm_spec(String.append(SCon{c, t}, "@")) == Ps.NpmSpec{String.append(SCon{c, t}, "@"), None{}} : Ps.NpmSpec}

# Laws: the texts (R9)
# --------------------

# LAW package_source_texts_table (R9): every part's name and every defect's
# words, constructor by constructor (the table of R9)
# EXCLUDES: a changed or swapped name or words
law package_source_texts_table:
  {[Ps.part_text(Ps.PHost{}), Ps.part_text(Ps.PPath{}), Ps.part_text(Ps.PRef{}), Ps.part_text(Ps.PClone{}), Ps.part_text(Ps.PSpec{}), Ps.part_text(Ps.PName{})] == ["git host", "git path", "git ref", "git clone URL", "npm spec", "npm package name"] : List<&2, String>} &
  {[Ps.defect_text(Ps.DEmpty{}), Ps.defect_text(Ps.DEmptySeg{}), Ps.defect_text(Ps.DDot{}), Ps.defect_text(Ps.DDrive{}), Ps.defect_text(Ps.DBackslash{}), Ps.defect_text(Ps.DControl{}), Ps.defect_text(Ps.DDash{}), Ps.defect_text(Ps.DSlash{})] == ["is empty", "has an empty path segment", "has a '.' or '..' segment", "has a drive-prefixed segment", "contains a backslash", "contains a control character", "starts with '-'", "contains '/'"] : List<&2, String>}

# Anchors
# -------

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
