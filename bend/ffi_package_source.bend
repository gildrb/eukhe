# ffi_package_source: the entry of the compiled Bend core for the package
# sources (bend/package_source.bend; Rust: eukhe-bend
# rules/package_source.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   part     0 git host | 1 git path | 2 git ref | 3 git clone URL | 4 npm
#            spec | 5 npm package name
#   defect   0 empty | 1 empty segment | 2 dot segment | 3 drive prefix |
#            4 backslash | 5 control char | 6 leading dash | 7 slash
#   flaw     the part, the defect
#   git      the clone URL, the host, the path, the ref (Maybe<String>),
#            pinned (Bool)
#   source   0 npm: the spec, the name, pinned (Bool) | 1 git: the git | 2
#            local: the path
#   request  a question, its tag then its fields:
#            0 source: the text     reply: 0 the source | 1 the flaw
#            1 git: the text        reply: 0 none | 1 the git | 2 the flaw
#            2 local: the text      reply: Bool
#            3 npm spec: the text   reply: the name, the version
#                                   (Maybe<String>)
#            4 part: the part       reply: the text (String)
#            5 defect: the defect   reply: the text (String)
#            6 error: the source, the flaw   reply: the text (String)
#
# Malformed input, or input left after the request, answers
# `E package_source: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./package_source.bend as Ps

# A request of the entry
type Req is Data:
  QSource{text: String}
  QGit{text: String}
  QLocal{text: String}
  QNpm{text: String}
  QPart{part: Ps.Part}
  QDefect{defect: Ps.Defect}
  QError{text: String, flaw: Ps.Flaw}

# Requests
# --------

def get_part.tag(t: Nat, s: String) -> W.Dec<Ps.Part>:
  match t:
    case 0n:
      W.Got{Ps.PHost{}, s}
    case 1n:
      W.Got{Ps.PPath{}, s}
    case 2n:
      W.Got{Ps.PRef{}, s}
    case 3n:
      W.Got{Ps.PClone{}, s}
    case 4n:
      W.Got{Ps.PSpec{}, s}
    case 5n:
      W.Got{Ps.PName{}, s}
    case 6n+u:
      W.Bad{}

def get_part.start(r: W.Dec<Nat>) -> W.Dec<Ps.Part>:
  match r:
    case W.Got{t, s}:
      get_part.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a part at the start of s
def get_part(s: String) -> W.Dec<Ps.Part>:
  get_part.start(W.get_nat(s))

def get_defect.tag(t: Nat, s: String) -> W.Dec<Ps.Defect>:
  match t:
    case 0n:
      W.Got{Ps.DEmpty{}, s}
    case 1n:
      W.Got{Ps.DEmptySeg{}, s}
    case 2n:
      W.Got{Ps.DDot{}, s}
    case 3n:
      W.Got{Ps.DDrive{}, s}
    case 4n:
      W.Got{Ps.DBackslash{}, s}
    case 5n:
      W.Got{Ps.DControl{}, s}
    case 6n:
      W.Got{Ps.DDash{}, s}
    case 7n:
      W.Got{Ps.DSlash{}, s}
    case 8n+u:
      W.Bad{}

def get_defect.start(r: W.Dec<Nat>) -> W.Dec<Ps.Defect>:
  match r:
    case W.Got{t, s}:
      get_defect.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a defect at the start of s
def get_defect(s: String) -> W.Dec<Ps.Defect>:
  get_defect.start(W.get_nat(s))

def get_flaw.defect(p: Ps.Part, r: W.Dec<Ps.Defect>) -> W.Dec<Ps.Flaw>:
  match r:
    case W.Got{d, s}:
      W.Got{Ps.Flaw{p, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_flaw.part(r: W.Dec<Ps.Part>) -> W.Dec<Ps.Flaw>:
  match r:
    case W.Got{p, s}:
      get_flaw.defect(p, get_defect(s))
    case W.Bad{}:
      W.Bad{}

# a flaw at the start of s
def get_flaw(s: String) -> W.Dec<Ps.Flaw>:
  get_flaw.part(get_part(s))

def get_source(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QSource{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_git(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QGit{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_local(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QLocal{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_npm(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QNpm{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_qpart(r: W.Dec<Ps.Part>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QPart{p}, s}
    case W.Bad{}:
      W.Bad{}

def get_qdefect(r: W.Dec<Ps.Defect>) -> W.Dec<Req>:
  match r:
    case W.Got{d, s}:
      W.Got{QDefect{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_error.flaw(x: String, r: W.Dec<Ps.Flaw>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{QError{x, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_error(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      get_error.flaw(x, get_flaw(s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_source(W.get_str(s))
    case 1n:
      get_git(W.get_str(s))
    case 2n:
      get_local(W.get_str(s))
    case 3n:
      get_npm(W.get_str(s))
    case 4n:
      get_qpart(get_part(s))
    case 5n:
      get_qdefect(get_defect(s))
    case 6n:
      get_error(W.get_str(s))
    case 7n+u:
      W.Bad{}

def get_req.start(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.start(W.get_nat(s))

# Replies
# -------

def put_ms(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{x}:
      W.put_nat(1n, W.put_str(x, rest))

def put_part(p: Ps.Part, rest: String) -> String:
  match p:
    case Ps.PHost{}:
      W.put_nat(0n, rest)
    case Ps.PPath{}:
      W.put_nat(1n, rest)
    case Ps.PRef{}:
      W.put_nat(2n, rest)
    case Ps.PClone{}:
      W.put_nat(3n, rest)
    case Ps.PSpec{}:
      W.put_nat(4n, rest)
    case Ps.PName{}:
      W.put_nat(5n, rest)

def put_defect(d: Ps.Defect, rest: String) -> String:
  match d:
    case Ps.DEmpty{}:
      W.put_nat(0n, rest)
    case Ps.DEmptySeg{}:
      W.put_nat(1n, rest)
    case Ps.DDot{}:
      W.put_nat(2n, rest)
    case Ps.DDrive{}:
      W.put_nat(3n, rest)
    case Ps.DBackslash{}:
      W.put_nat(4n, rest)
    case Ps.DControl{}:
      W.put_nat(5n, rest)
    case Ps.DDash{}:
      W.put_nat(6n, rest)
    case Ps.DSlash{}:
      W.put_nat(7n, rest)

def put_flaw(f: Ps.Flaw, rest: String) -> String:
  match f:
    case Ps.Flaw{p, d}:
      put_part(p, put_defect(d, rest))

def put_git(g: Ps.GitSrc, rest: String) -> String:
  match g:
    case Ps.GitSrc{repo, h, p, r, n}:
      W.put_str(repo, W.put_str(h, W.put_str(p, put_ms(r, W.put_bool(n, rest)))))

def put_src(x: Ps.Src) -> String:
  match x:
    case Ps.SrcNpm{m}:
      match m:
        case Ps.NpmSrc{spec, name, n}:
          W.put_nat(0n, W.put_str(spec, W.put_str(name, W.put_bool(n, ""))))
    case Ps.SrcGit{g}:
      W.put_nat(1n, put_git(g, ""))
    case Ps.SrcLocal{p}:
      W.put_nat(2n, W.put_str(p, ""))

def put_parsed(a: Ps.Parsed) -> String:
  match a:
    case Ps.Parsed{x}:
      W.put_nat(0n, put_src(x))
    case Ps.Refused{f}:
      W.put_nat(1n, put_flaw(f, ""))

def put_gitans(a: Ps.GitAns) -> String:
  match a:
    case Ps.NoGit{}:
      W.put_nat(0n, "")
    case Ps.IsGit{g}:
      W.put_nat(1n, put_git(g, ""))
    case Ps.BadGit{f}:
      W.put_nat(2n, put_flaw(f, ""))

def put_spec(n: Ps.NpmSpec) -> String:
  match n:
    case Ps.NpmSpec{name, v}:
      W.put_str(name, put_ms(v, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QSource{x}:
      put_parsed(Ps.source(x))
    case QGit{x}:
      put_gitans(Ps.git(x))
    case QLocal{x}:
      W.put_bool(Ps.local(x), "")
    case QNpm{x}:
      put_spec(Ps.npm_spec(x))
    case QPart{p}:
      W.put_str(Ps.part_text(p), "")
    case QDefect{d}:
      W.put_str(Ps.defect_text(d), "")
    case QError{x, f}:
      W.put_str(Ps.error_text(x, f), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("package_source: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("package_source: malformed request")

# the entry: decode the request, answer the model's text
def ffi(input: String) -> String:
  ffi.got(get_req(input))
