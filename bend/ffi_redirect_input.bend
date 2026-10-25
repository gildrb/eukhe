# ffi_redirect_input: the entry of the compiled Bend core for the pasted
# authorization input (bend/redirect_input.bend; Rust: eukhe-bend
# rules/redirect_input.rs). Grammar: crates/eukhe-bend/WIRE.md.
#
#   fail     0 no code | 1 state mismatch | 2 provider error: the error,
#            the description (Maybe<String>)
#   answer   0 pasted: the code, the state (Maybe<String>) | 1 failed: the
#            fail
#   request  a question, its tag then its fields:
#            0 clean: the text            reply: the text (String)
#            1 parse: the text            reply: the answer
#            2 verify: the code, the state (Maybe<String>), the login's
#              state                      reply: the answer
#            3 text: the fail             reply: the text (String)
#            4 notice: the error text     reply: the text (String)
#
# Malformed input, or input left after the request, answers
# `E redirect_input: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./redirect_input.bend as Ri

# A request of the entry
type Req is Data:
  QClean{text: String}
  QParse{text: String}
  QVerify{code: String, state: Maybe<&2, String>, expected: String}
  QText{fail: Ri.Fail}
  QNotice{text: String}

# Requests
# --------

def get_ms.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_ms.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_ms.some(W.get_str(s))
    case 2n+u:
      W.Bad{}

def get_ms.start(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_ms.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a Maybe<String> at the start of s
def get_ms(s: String) -> W.Dec<Maybe<&2, String>>:
  get_ms.start(W.get_nat(s))

def get_clean(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QClean{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_parse(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QParse{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_notice(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{x, s}:
      W.Got{QNotice{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_verify.expected(c: String, m: Maybe<&2, String>, r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{e, s}:
      W.Got{QVerify{c, m, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_verify.state(c: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{m, s}:
      get_verify.expected(c, m, W.get_str(s))
    case W.Bad{}:
      W.Bad{}

def get_verify(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{c, s}:
      get_verify.state(c, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_provider.desc(e: String, r: W.Dec<Maybe<&2, String>>) -> W.Dec<Ri.Fail>:
  match r:
    case W.Got{d, s}:
      W.Got{Ri.FProvider{e, d}, s}
    case W.Bad{}:
      W.Bad{}

def get_provider(r: W.Dec<String>) -> W.Dec<Ri.Fail>:
  match r:
    case W.Got{e, s}:
      get_provider.desc(e, get_ms(s))
    case W.Bad{}:
      W.Bad{}

def get_fail.tag(t: Nat, s: String) -> W.Dec<Ri.Fail>:
  match t:
    case 0n:
      W.Got{Ri.FMissing{}, s}
    case 1n:
      W.Got{Ri.FMismatch{}, s}
    case 2n:
      get_provider(W.get_str(s))
    case 3n+u:
      W.Bad{}

def get_fail.start(r: W.Dec<Nat>) -> W.Dec<Ri.Fail>:
  match r:
    case W.Got{t, s}:
      get_fail.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fail(r: W.Dec<Ri.Fail>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{QText{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_clean(W.get_str(s))
    case 1n:
      get_parse(W.get_str(s))
    case 2n:
      get_verify(W.get_str(s))
    case 3n:
      get_fail(get_fail.start(W.get_nat(s)))
    case 4n:
      get_notice(W.get_str(s))
    case 5n+u:
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

def put_fail(f: Ri.Fail) -> String:
  match f:
    case Ri.FMissing{}:
      W.put_nat(0n, "")
    case Ri.FMismatch{}:
      W.put_nat(1n, "")
    case Ri.FProvider{e, d}:
      W.put_nat(2n, W.put_str(e, put_ms(d, "")))

def put_answer(a: Ri.Answer) -> String:
  match a:
    case Ri.Pasted{c, m}:
      W.put_nat(0n, W.put_str(c, put_ms(m, "")))
    case Ri.Failed{f}:
      W.put_nat(1n, put_fail(f))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QClean{x}:
      W.put_str(Ri.clean(x), "")
    case QParse{x}:
      put_answer(Ri.parse(x))
    case QVerify{c, m, e}:
      put_answer(Ri.verify(c, m, e))
    case QText{f}:
      W.put_str(Ri.text(f), "")
    case QNotice{x}:
      W.put_str(Ri.notice(x), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("redirect_input: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("redirect_input: malformed request")

# the entry: decode the request, answer the model's text
def ffi(input: String) -> String:
  ffi.got(get_req(input))
