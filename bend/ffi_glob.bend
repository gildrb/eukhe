# ffi_glob: the entry of the compiled Bend core for glob patterns
# (bend/glob.bend; Rust: eukhe-bend rules/glob.rs). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   request  0, pattern (String)                  whether globset refuses it
#            1, sep (Bool), fold (Bool), patterns (List<String>),
#               texts (List<String>), group sizes (List<Nat>)
#                                                  per group of texts, whether
#                                                  a pattern matches one of them
#            2, selector (String), patterns (List<String>)
#                                                  whether the model allowlist
#                                                  allows the selector
#            3, sep (Bool), fold (Bool), patterns (List<String>),
#               texts (List<String>), rule sizes (List<Nat>)
#                                                  per rule (its patterns in
#                                                  order), whether one of its
#                                                  patterns matches a text
#            4, rule texts (List<String>), rule codes (List<Nat>),
#               entries (List<String>)            per entry (a directory's
#                                                  path ends in `/`), whether
#                                                  the ignore rules ignore it
#   reply    to 0: 0 accepted | 1, then the error: 0 unclosed class |
#               1, lo, hi (char codes) invalid range | 2 unopened group |
#               3 unclosed group | 4 dangling escape
#            to 1: the groups' answers (List<Bool>)
#            to 2: the answer (Bool)
#            to 3: the rules' answers, to 4: the entries' (List<Bool>)
#
# Malformed input, or input left after the request, answers
# `E glob: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./glob.bend as G

# A request of the entry
type Req is Data:
  QCheck{p: String}
  QMatch{sep: Bool, fold: Bool, ps: List<&2, String>, ss: List<&2, String>, ks: List<&2, Nat>}
  QAllow{sel: String, ps: List<&2, String>}
  QRules{sep: Bool, fold: Bool, ps: List<&2, String>, ss: List<&2, String>, ks: List<&2, Nat>}
  QIgnore{ps: List<&2, String>, cs: List<&2, Nat>, es: List<&2, String>}

# Decoding
# --------

def get_check(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{p, s}:
      W.Got{QCheck{p}, s}
    case W.Bad{}:
      W.Bad{}

# the group query (rules False) or the rules query (rules True): both
# spell the same fields
def mkq(rules: Bool, sep: Bool, fold: Bool, ps: List<&2, String>, ss: List<&2, String>, ks: List<&2, Nat>) -> Req:
  match rules:
    case True{}:
      QRules{sep, fold, ps, ss, ks}
    case False{}:
      QMatch{sep, fold, ps, ss, ks}

def get_match.ks(rules: Bool, sep: Bool, fold: Bool, ps: List<&2, String>, ss: List<&2, String>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{ks, s}:
      W.Got{mkq(rules, sep, fold, ps, ss, ks), s}
    case W.Bad{}:
      W.Bad{}

def get_match.ss(rules: Bool, sep: Bool, fold: Bool, ps: List<&2, String>, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ss, s}:
      get_match.ks(rules, sep, fold, ps, ss, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_match.ps(rules: Bool, sep: Bool, fold: Bool, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      get_match.ss(rules, sep, fold, ps, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_match.fold(rules: Bool, sep: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{fold, s}:
      get_match.ps(rules, sep, fold, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_match(rules: Bool, r: W.Dec<Bool>) -> W.Dec<Req>:
  match r:
    case W.Got{sep, s}:
      get_match.fold(rules, sep, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ignore.es(ps: List<&2, String>, cs: List<&2, Nat>, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{es, s}:
      W.Got{QIgnore{ps, cs, es}, s}
    case W.Bad{}:
      W.Bad{}

def get_ignore.cs(ps: List<&2, String>, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      get_ignore.es(ps, cs, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_ignore(r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      get_ignore.cs(ps, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_allow.ps(sel: String, r: W.Dec<List<&2, String>>) -> W.Dec<Req>:
  match r:
    case W.Got{ps, s}:
      W.Got{QAllow{sel, ps}, s}
    case W.Bad{}:
      W.Bad{}

def get_allow(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{sel, s}:
      get_allow.ps(sel, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_req.tag(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      match t:
        case 0n:
          get_check(W.get_str(s))
        case 1n:
          get_match(False{}, W.get_bool(s))
        case 2n:
          get_allow(W.get_str(s))
        case 3n:
          get_match(True{}, W.get_bool(s))
        case 4n:
          get_ignore(W.get_list(~String, ~W.get_str, s))
        case 5n+k:
          W.Bad{}
    case W.Bad{}:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  get_req.tag(W.get_nat(s))

# The entry
# ---------

def put_err(e: G.Err, rest: String) -> String:
  match e:
    case G.EClass{}:
      W.put_nat(0n, rest)
    case G.ERange{lo, hi}:
      W.put_nat(1n, W.put_nat(U32.to_nat(G.code(lo)), W.put_nat(U32.to_nat(G.code(hi)), rest)))
    case G.EUnopened{}:
      W.put_nat(2n, rest)
    case G.EUnclosed{}:
      W.put_nat(3n, rest)
    case G.EEscape{}:
      W.put_nat(4n, rest)

def put_check(m: Maybe<&2, G.Err>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{e}:
      W.put_nat(1n, put_err(e, ""))

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QCheck{p}:
      put_check(G.check(p))
    case QMatch{sep, fold, ps, ss, ks}:
      W.put_list(~Bool, ~W.put_bool, G.match_groups(G.Opts{sep, fold}, ps, ss, ks), "")
    case QAllow{sel, ps}:
      W.put_bool(G.allowed(sel, ps), "")
    case QRules{sep, fold, ps, ss, ks}:
      W.put_list(~Bool, ~W.put_bool, G.rules(ks, G.Opts{sep, fold}, ps, ss), "")
    case QIgnore{ps, cs, es}:
      W.put_list(~Bool, ~W.put_bool, G.ignored(ps, cs, es), "")

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("glob: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("glob: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
