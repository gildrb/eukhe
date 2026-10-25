# eukhe: the laws of area package_source: the entry (bend/ffi_package_source.bend)

import Base
import ../../bend/package_source.bend as Ps
import ../../bend/ffi_package_source.bend as FPs
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as PackageSource

# (D2) The entry
# --------------
# R10: the entry answers each request Rust writes (tag 0 source, 1 git, 2
#     local, 3 npm spec: the text; 4 part: the part; 5 defect: the
#     defect; 6 error: the text and the flaw; a part 0 git host | 1 git
#     path | 2 git ref | 3 git clone URL | 4 npm spec | 5 npm package name;
#     a defect 0 empty | 1 empty segment | 2 dot segment | 3 drive prefix |
#     4 backslash | 5 control character | 6 leading dash | 7 slash; a flaw
#     the part then the defect; every length within the wire) with the
#     spec's answer (source: 0 then the source: 0 npm: the spec, the name,
#     pinned | 1 git | 2 local: the text; or 1 then the flaw; git: 0 none |
#     1 the git | 2 the flaw; a git: the clone URL, the host, the path, the
#     ref as Maybe<String>, pinned; local: the Bool; npm spec: the name and
#     the version as Maybe<String>; the texts: the text), reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E package_source: malformed request`.

# Spellers
# --------

def ps_w_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def ps_w_part(p: Ps.Part, rest: String) -> String:
  match p:
    case Ps.PHost{}:
      Wr.put_nat(0n, rest)
    case Ps.PPath{}:
      Wr.put_nat(1n, rest)
    case Ps.PRef{}:
      Wr.put_nat(2n, rest)
    case Ps.PClone{}:
      Wr.put_nat(3n, rest)
    case Ps.PSpec{}:
      Wr.put_nat(4n, rest)
    case Ps.PName{}:
      Wr.put_nat(5n, rest)

def ps_w_defect(d: Ps.Defect, rest: String) -> String:
  match d:
    case Ps.DEmpty{}:
      Wr.put_nat(0n, rest)
    case Ps.DEmptySeg{}:
      Wr.put_nat(1n, rest)
    case Ps.DDot{}:
      Wr.put_nat(2n, rest)
    case Ps.DDrive{}:
      Wr.put_nat(3n, rest)
    case Ps.DBackslash{}:
      Wr.put_nat(4n, rest)
    case Ps.DControl{}:
      Wr.put_nat(5n, rest)
    case Ps.DDash{}:
      Wr.put_nat(6n, rest)
    case Ps.DSlash{}:
      Wr.put_nat(7n, rest)

def ps_w_flaw(f: Ps.Flaw, rest: String) -> String:
  match f:
    case Ps.Flaw{p, d}:
      ps_w_part(p, ps_w_defect(d, rest))

def ps_w_git(g: Ps.GitSrc, rest: String) -> String:
  match g:
    case Ps.GitSrc{repo, h, p, r, n}:
      Wr.put_str(repo, Wr.put_str(h, Wr.put_str(p, ps_w_ms(r, Wr.put_bool(n, rest)))))

def ps_w_src(x: Ps.Src) -> String:
  match x:
    case Ps.SrcNpm{m}:
      match m:
        case Ps.NpmSrc{spec, name, n}:
          Wr.put_nat(0n, Wr.put_str(spec, Wr.put_str(name, Wr.put_bool(n, ""))))
    case Ps.SrcGit{g}:
      Wr.put_nat(1n, ps_w_git(g, ""))
    case Ps.SrcLocal{p}:
      Wr.put_nat(2n, Wr.put_str(p, ""))

def ps_w_parsed(a: Ps.Parsed) -> String:
  match a:
    case Ps.Parsed{x}:
      Wr.put_nat(0n, ps_w_src(x))
    case Ps.Refused{f}:
      Wr.put_nat(1n, ps_w_flaw(f, ""))

def ps_w_gitans(a: Ps.GitAns) -> String:
  match a:
    case Ps.NoGit{}:
      Wr.put_nat(0n, "")
    case Ps.IsGit{g}:
      Wr.put_nat(1n, ps_w_git(g, ""))
    case Ps.BadGit{f}:
      Wr.put_nat(2n, ps_w_flaw(f, ""))

def ps_w_spec(n: Ps.NpmSpec) -> String:
  match n:
    case Ps.NpmSpec{name, v}:
      Wr.put_str(name, ps_w_ms(v, ""))

def ps_w_req(q: FPs.Req, rest: String) -> String:
  match q:
    case FPs.QSource{x}:
      Wr.put_nat(0n, Wr.put_str(x, rest))
    case FPs.QGit{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case FPs.QLocal{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))
    case FPs.QNpm{x}:
      Wr.put_nat(3n, Wr.put_str(x, rest))
    case FPs.QPart{p}:
      Wr.put_nat(4n, ps_w_part(p, rest))
    case FPs.QDefect{d}:
      Wr.put_nat(5n, ps_w_defect(d, rest))
    case FPs.QError{x, f}:
      Wr.put_nat(6n, Wr.put_str(x, ps_w_flaw(f, rest)))

def ps_w_reply(q: FPs.Req) -> String:
  match q:
    case FPs.QSource{x}:
      ps_w_parsed(PackageSource.ps_source(x))
    case FPs.QGit{x}:
      ps_w_gitans(PackageSource.ps_git(x))
    case FPs.QLocal{x}:
      Wr.put_bool(PackageSource.ps_local(x), "")
    case FPs.QNpm{x}:
      ps_w_spec(PackageSource.ps_npm_spec(x))
    case FPs.QPart{p}:
      Wr.put_str(PackageSource.ps_part_text(p), "")
    case FPs.QDefect{d}:
      Wr.put_str(PackageSource.ps_defect_text(d), "")
    case FPs.QError{x, f}:
      Wr.put_str(PackageSource.ps_error_text(x, f), "")

def ps_fit_str(s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

# every length of the request fits the wire
def ps_fit_req(q: FPs.Req) -> Bool:
  match q:
    case FPs.QSource{x}:
      ps_fit_str(x)
    case FPs.QGit{x}:
      ps_fit_str(x)
    case FPs.QLocal{x}:
      ps_fit_str(x)
    case FPs.QNpm{x}:
      ps_fit_str(x)
    case FPs.QPart{p}:
      True{}
    case FPs.QDefect{d}:
      True{}
    case FPs.QError{x, f}:
      ps_fit_str(x)

# Laws
# ----

# LAW package_source_entry_answers (R10): the entry answers every request
# Rust spells, every length within the wire, with the spec's answer spelled
# EXCLUDES: fields read in another order, a tag misread, a part or defect
#   tag swapped, a reply in another constructor, a default
law package_source_entry_answers:
  for +q: FPs.Req
  for fit: {ps_fit_req(q) == True{} : Bool}
  {FPs.ffi(ps_w_req(q, "")) == ps_w_reply(q) : String}

# LAW package_source_entry_left_over (R10): a spelled request followed by
# more input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law package_source_entry_left_over:
  for +q: FPs.Req
  for +c: Char
  for +t: String
  for fit: {ps_fit_req(q) == True{} : Bool}
  {FPs.ffi(ps_w_req(q, SCon{c, t})) == Wr.err("package_source: malformed request") : String}

# LAW package_source_entry_exact (R10): every input the entry does not
# answer with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request (an unknown tag, a part
#   tag past 5, a defect tag past 7, a short field, input left over)
law package_source_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FPs.ffi(s)) == False{} : Bool}
  exs q: FPs.Req
  {s == ps_w_req(q, "") : String} & {ps_fit_req(q) == True{} : Bool}

# LAW package_source_entry_refuses (R10): every error the entry answers is
# exactly `E package_source: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law package_source_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FPs.ffi(s)) == True{} : Bool}
  {FPs.ffi(s) == Wr.err("package_source: malformed request") : String}

# LAW package_source_entry_example (R10): anchor: the wire strings Rust
# sends and the replies it reads
# EXCLUDES: another spelling of a request or of a reply
law package_source_entry_example:
  {[FPs.ffi("0,7,npm:a@1"), FPs.ffi("0,1,x"), FPs.ffi("0,5,npm:-"), FPs.ffi("1,18,git:git@h.io:u/r@v"), FPs.ffi("1,1,x"), FPs.ffi("1,13,git:h.io/a/.."), FPs.ffi("2,4,ssh:"), FPs.ffi("3,3,a@1"), FPs.ffi("4,3,"), FPs.ffi("5,7,"), FPs.ffi("6,1,x5,1,"), FPs.ffi("4,6,"), FPs.ffi("5,8,"), FPs.ffi("7,"), FPs.ffi("2,1,xy")] == ["0,0,3,a@11,aT", "0,2,1,x", "1,4,6,", "1,12,git@h.io:u/r4,h.io3,u/r1,1,vT", "0,", "2,1,2,", "F", "1,a1,1,1", "13,git clone URL", "12,contains '/'", "68,Invalid package source x: npm package name has an empty path segment", Wr.err("package_source: malformed request"), Wr.err("package_source: malformed request"), Wr.err("package_source: malformed request"), Wr.err("package_source: malformed request")] : List<&2, String>}
