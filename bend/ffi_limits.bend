# ffi_limits: the entry of the compiled Bend core for the limits of a run
# (bend/limits.bend; Rust: eukhe-bend rules/limits.rs). Grammar:
# crates/eukhe-bend/WIRE.md.
#
#   a kind     a tag (Nat): 0 interactive, 1 headless, 2 sdk, 3 scheduled,
#              4 loop, 5 autoresearch
#   an auth    a tag (Nat): 0 plan, 1 API key, 2 local model
#   a limit    a tag (Nat): 0 unset | 1, then the number (Nat) | 2
#              unlimited
#   limits     five limits: money (micro-dollars), tokens, time (ms),
#              tool calls, model requests
#   a source   a tag (Nat): 0 until finished, 1 set, 2 limits profile,
#              3 profile | 4, then the preset's place (Nat)
#   a window   its label (String), its used permille (Nat)
#   amounts, asks, accounts: as bend/ffi_budget.bend
#   request  a question, its tag then its fields:
#            0 fill: T|F limits on, the kind, the auth, the limits set,
#              the presets (List of limits), the principal's profile
#            1 profile: the kind, the auth
#            2 preset: a tag (0 quick, 1 deep), the kind, the auth
#            3 plan wraps: the windows' used permille (List of Nat), the
#              reserve (Nat, permille)
#            4 plan notice: the windows (List), the reserve (Nat,
#              permille), the labels told of (List of String)
#            5 floor: the limits, the first work ask, the final-answer
#              reserve (asks)
#            6 renew: the limits, the spent mark (an amount), now (Nat,
#              ms), the account
#            7 prefix: the message (String), the preset names (List of
#              String)
#   reply    fill: the limits, then five sources
#            profile, preset: the limits
#            plan wraps: a Maybe of the window's place (Nat)
#            plan notice: the places to tell of (List of Nat), the labels
#              told of (List of String)
#            floor: a Maybe of the dimension (0 money, 1 tokens, 2 time,
#              3 tool calls, 4 model requests)
#            renew: the account
#            prefix: 0, the presets' places (List of Nat), the pairs (List
#              of a key tag (0 cost, 1 tokens, 2 time, 3 calls, 4
#              requests) then the value (String)), the rest (String) | 1,
#              the refused word (String)
#
# Malformed input (an unknown tag, a missing field, input left after the
# request) answers `E limits: malformed request`, never a default. Pure:
# no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./budget.bend as B
import ./ffi_budget.bend as FB
import ./limits.bend as L

# A request of the entry
type Req is Data:
  QFill{t: L.Toggle, k: L.Run, a: L.Auth, set: L.Lims, ps: List<&2, L.Lims>, own: L.Lims}
  QProfile{k: L.Run, a: L.Auth}
  QPreset{s: L.Scale, k: L.Run, a: L.Auth}
  QWraps{us: List<&2, Nat>, reserve: Nat}
  QNotice{ws: List<&2, L.Win>, reserve: Nat, told: List<&2, String>}
  QFloor{l: L.Lims, c: B.Ask, keep: B.Ask}
  QRenew{l: L.Lims, mark: B.Amt, now: Nat, acct: B.Acct}
  QPrefix{text: String, names: List<&2, String>}

# Decoders
# --------

# d's value, then k on it and the input after it
def then(-A: Data, -R: Data, d: W.Dec<A>, k: A -> String -> W.Dec<R>) -> W.Dec<R>:
  match d:
    case W.Got{x, s}:
      k(x, s)
    case W.Bad{}:
      W.Bad{}

def get_kind.of(n: Nat, s: String) -> W.Dec<L.Run>:
  match n:
    case 0n:
      W.Got{L.Interactive{}, s}
    case 1n:
      W.Got{L.Headless{}, s}
    case 2n:
      W.Got{L.Sdk{}, s}
    case 3n:
      W.Got{L.Scheduled{}, s}
    case 4n:
      W.Got{L.Loop{}, s}
    case 5n:
      W.Got{L.Autoresearch{}, s}
    case 6n+p:
      W.Bad{}

def get_kind(s: String) -> W.Dec<L.Run>:
  then(Nat, L.Run, W.get_nat(s), n => r => get_kind.of(n, r))

def get_auth.of(n: Nat, s: String) -> W.Dec<L.Auth>:
  match n:
    case 0n:
      W.Got{L.Plan{}, s}
    case 1n:
      W.Got{L.ApiKey{}, s}
    case 2n:
      W.Got{L.Local{}, s}
    case 3n+p:
      W.Bad{}

def get_auth(s: String) -> W.Dec<L.Auth>:
  then(Nat, L.Auth, W.get_nat(s), n => r => get_auth.of(n, r))

def get_scale.of(n: Nat, s: String) -> W.Dec<L.Scale>:
  match n:
    case 0n:
      W.Got{L.Quick{}, s}
    case 1n:
      W.Got{L.Deep{}, s}
    case 2n+p:
      W.Bad{}

def get_scale(s: String) -> W.Dec<L.Scale>:
  then(Nat, L.Scale, W.get_nat(s), n => r => get_scale.of(n, r))

def get_toggle.of(b: Bool, s: String) -> W.Dec<L.Toggle>:
  match b:
    case True{}:
      W.Got{L.On{}, s}
    case False{}:
      W.Got{L.Off{}, s}

def get_toggle(s: String) -> W.Dec<L.Toggle>:
  then(Bool, L.Toggle, W.get_bool(s), b => r => get_toggle.of(b, r))

def get_val.of(n: Nat, s: String) -> W.Dec<L.Val>:
  match n:
    case 0n:
      W.Got{L.Unset{}, s}
    case 1n:
      then(Nat, L.Val, W.get_nat(s), v => r => W.Got{L.At{v}, r})
    case 2n:
      W.Got{L.Unlimited{}, s}
    case 3n+p:
      W.Bad{}

def get_val(s: String) -> W.Dec<L.Val>:
  then(Nat, L.Val, W.get_nat(s), n => r => get_val.of(n, r))

def get_lims(s: String) -> W.Dec<L.Lims>:
  then(L.Val, L.Lims, get_val(s), c => s1 => then(L.Val, L.Lims, get_val(s1), k => s2 => then(L.Val, L.Lims, get_val(s2), m => s3 => then(L.Val, L.Lims, get_val(s3), n => s4 => then(L.Val, L.Lims, get_val(s4), r => s5 => W.Got{L.Lims{c, k, m, n, r}, s5})))))

def get_win(s: String) -> W.Dec<L.Win>:
  then(String, L.Win, W.get_str(s), l => s1 => then(Nat, L.Win, W.get_nat(s1), u => s2 => W.Got{L.Win{l, u}, s2}))

def get_fill(s: String) -> W.Dec<Req>:
  then(L.Toggle, Req, get_toggle(s), t => s1 => then(L.Run, Req, get_kind(s1), k => s2 => then(L.Auth, Req, get_auth(s2), a => s3 => then(L.Lims, Req, get_lims(s3), set => s4 => then(List<&2, L.Lims>, Req, W.get_list(~L.Lims, ~get_lims, s4), ps => s5 => then(L.Lims, Req, get_lims(s5), own => s6 => W.Got{QFill{t, k, a, set, ps, own}, s6}))))))

def get_profile(s: String) -> W.Dec<Req>:
  then(L.Run, Req, get_kind(s), k => s1 => then(L.Auth, Req, get_auth(s1), a => s2 => W.Got{QProfile{k, a}, s2}))

def get_preset(s: String) -> W.Dec<Req>:
  then(L.Scale, Req, get_scale(s), c => s1 => then(L.Run, Req, get_kind(s1), k => s2 => then(L.Auth, Req, get_auth(s2), a => s3 => W.Got{QPreset{c, k, a}, s3})))

def get_wraps(s: String) -> W.Dec<Req>:
  then(List<&2, Nat>, Req, W.get_list(~Nat, ~W.get_nat, s), us => s1 => then(Nat, Req, W.get_nat(s1), r => s2 => W.Got{QWraps{us, r}, s2}))

def get_notice(s: String) -> W.Dec<Req>:
  then(List<&2, L.Win>, Req, W.get_list(~L.Win, ~get_win, s), ws => s1 => then(Nat, Req, W.get_nat(s1), r => s2 => then(List<&2, String>, Req, W.get_list(~String, ~W.get_str, s2), told => s3 => W.Got{QNotice{ws, r, told}, s3})))

def get_floor(s: String) -> W.Dec<Req>:
  then(L.Lims, Req, get_lims(s), l => s1 => then(B.Ask, Req, FB.get_ask(s1), c => s2 => then(B.Ask, Req, FB.get_ask(s2), keep => s3 => W.Got{QFloor{l, c, keep}, s3})))

def get_renew(s: String) -> W.Dec<Req>:
  then(L.Lims, Req, get_lims(s), l => s1 => then(B.Amt, Req, FB.get_amt(s1), mark => s2 => then(Nat, Req, W.get_nat(s2), now => s3 => then(B.Acct, Req, FB.get_acct(s3), a => s4 => W.Got{QRenew{l, mark, now, a}, s4}))))

def get_prefix(s: String) -> W.Dec<Req>:
  then(String, Req, W.get_str(s), text => s1 => then(List<&2, String>, Req, W.get_list(~String, ~W.get_str, s1), ns => s2 => W.Got{QPrefix{text, ns}, s2}))

# the request of tag n
def get_req.of(n: Nat, s: String) -> W.Dec<Req>:
  match n:
    case 0n:
      get_fill(s)
    case 1n:
      get_profile(s)
    case 2n:
      get_preset(s)
    case 3n:
      get_wraps(s)
    case 4n:
      get_notice(s)
    case 5n:
      get_floor(s)
    case 6n:
      get_renew(s)
    case 7n:
      get_prefix(s)
    case 8n+p:
      W.Bad{}

# the request at the start of s
def get_req(s: String) -> W.Dec<Req>:
  then(Nat, Req, W.get_nat(s), n => r => get_req.of(n, r))

# Encoders
# --------

def put_val(v: L.Val, rest: String) -> String:
  match v:
    case L.Unset{}:
      W.put_nat(0n, rest)
    case L.At{n}:
      W.put_nat(1n, W.put_nat(n, rest))
    case L.Unlimited{}:
      W.put_nat(2n, rest)

def put_lims(l: L.Lims, rest: String) -> String:
  match l:
    case L.Lims{c, k, m, n, r}:
      put_val(c, put_val(k, put_val(m, put_val(n, put_val(r, rest)))))

def put_src(x: L.Src, rest: String) -> String:
  match x:
    case L.UntilFinished{}:
      W.put_nat(0n, rest)
    case L.Set{}:
      W.put_nat(1n, rest)
    case L.LimitsProfile{}:
      W.put_nat(2n, rest)
    case L.Profile{}:
      W.put_nat(3n, rest)
    case L.Preset{i}:
      W.put_nat(4n, W.put_nat(i, rest))

def put_filled(f: L.Filled) -> String:
  match f:
    case L.Filled{l, x}:
      match x:
        case L.Srcs{c, k, m, n, r}:
          put_lims(l, put_src(c, put_src(k, put_src(m, put_src(n, put_src(r, ""))))))

def put_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{i}:
      W.put_nat(1n, W.put_nat(i, ""))

def put_told(t: L.Told) -> String:
  match t:
    case L.Told{now, told}:
      W.put_list(~Nat, ~W.put_nat, now, W.put_list(~String, ~W.put_str, told, ""))

def put_mdim(m: Maybe<&2, B.Dim>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{d}:
      W.put_nat(1n, FB.put_dim(d, ""))

def put_key(k: L.Key, rest: String) -> String:
  match k:
    case L.KCost{}:
      W.put_nat(0n, rest)
    case L.KTok{}:
      W.put_nat(1n, rest)
    case L.KTime{}:
      W.put_nat(2n, rest)
    case L.KCalls{}:
      W.put_nat(3n, rest)
    case L.KReqs{}:
      W.put_nat(4n, rest)

def put_pair(p: L.KV, rest: String) -> String:
  match p:
    case L.KV{k, v}:
      put_key(k, W.put_str(v, rest))

def put_prefix(p: L.Prefix) -> String:
  match p:
    case L.Read{ks, ps, r}:
      W.put_nat(0n, W.put_list(~Nat, ~W.put_nat, ks, W.put_list(~L.KV, ~put_pair, ps, W.put_str(r, ""))))
    case L.Refused{w}:
      W.put_nat(1n, W.put_str(w, ""))

# The entry
# ---------

# the reply of a request: the model's answer, encoded
def answer(q: Req) -> String:
  match q:
    case QFill{t, k, a, set, ps, own}:
      put_filled(L.fill(t, k, a, set, ps, own))
    case QProfile{k, a}:
      put_lims(L.profile(k, a), "")
    case QPreset{c, k, a}:
      put_lims(L.preset(c, k, a), "")
    case QWraps{us, r}:
      put_mnat(L.plan_wraps(us, r))
    case QNotice{ws, r, told}:
      put_told(L.plan_notice(ws, r, told))
    case QFloor{l, c, keep}:
      put_mdim(L.floor(l, c, keep))
    case QRenew{l, mark, now, a}:
      FB.put_acct(L.renew(l, mark, now, a), "")
    case QPrefix{text, ns}:
      put_prefix(L.prefix(text, ns))

def ffi.done(q: Req, end: Bool) -> String:
  match end:
    case True{}:
      answer(q)
    case False{}:
      W.err("limits: malformed request")

def ffi.got(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, +s}:
      ffi.done(q, W.end(s))
    case W.Bad{}:
      W.err("limits: malformed request")

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  ffi.got(get_req(input))
