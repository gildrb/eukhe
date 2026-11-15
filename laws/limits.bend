# eukhe: the laws of area limits

import Base
import ../bend/budget.bend as B
import ../bend/limits.bend as L
import ../bend/ffi_limits.bend as FL
import ../bend/wire.bend as Wr
import ../spec/budget/limits.bend as S
import ../spec/budget/ledger.bend as SL
import ./budget.bend as Budget
import ./base.bend as LawsBase

# (B15-B23) The limits of a run
# -----------------------------
# spec/README.md B15-B23. bend/limits.bend: every run's limits and their
# sources, the limits profile and the shipped presets, a plan's quota
# windows (the wrap-up line, the 80 % notice), whether a run's limits hold
# its first request, an account set to a run's limits, the `/b` prefix of
# a message. It runs as the compiled core by bend/ffi_limits.bend
# (eukhe-bend rules/limits.rs). spec/budget/limits.bend restates the rules
# (S1-S6). Every input is free unless a premise names it.
#
# R1: a dimension the principal set for the run takes that limit, source
#     set; else the last `/b` preset that gives it, source that preset;
#     else with limits off it is unlimited, until finished; with limits on
#     the principal's profile, else the limits profile's number, else
#     unlimited, until finished (S1; B15, B16).
# R2: the limits profile is the table of B15 and the shipped presets are
#     a quarter and four times it (S2; B15, B20).
# R3: a plan run wraps up at the first window at or past 1000 - reserve
#     permille (S3; B18).
# R4: a window reaching that line is told of once; a reading below it
#     arms it again: after the readings, a label is told of exactly when
#     a window of it is at or past the line, or it was told of and no
#     window of it read below the line, and the labels kept (which Rust
#     sends back with the next reading) hold each label once (S4; B23).
# R5: a run's limits hold its first request exactly when the reservation
#     on an account holding those limits is granted, and otherwise name the
#     dimension it is short in; an unbounded dimension is never short and
#     takes no part: limits that bound some dimensions hold the request as
#     those dimensions alone do (S5; B17).
# R6: a renewal gives each bounded dimension its limit less what the run
#     used, keeps every other part of the account, and puts the deadline
#     at now plus a time limit (S6; B19).
# R7: the `/b` prefix: a message that does not open with `/b` (folded)
#     then a space or its end is untouched; after the opener the words
#     read in order, presets and pairs, up to the first other word, which
#     with all after it reaches the model verbatim; full-width forms
#     folded, a decimal comma read as a point; an empty value or a
#     repeated key refused with the word as typed (S7; B20).
# R8: the entry answers every request Rust spells, every number and
#     count within the wire, with the model's answer spelled; input left
#     after a request, a tag past the known ones, and every input it
#     refuses answer the exact error form `E limits: malformed request`;
#     every input it answers otherwise is such a request, read whole; an
#     anchor pins the spelling of each request and reply.
#
# Not pinned here: that Rust asks the entry at each run's start, keeps
# the labels told of per provider, and parses a pair's value as an amount
# (crates/eukhe-tui budget_text.rs): the Rust tests cover them.

# Spec helpers: the wire (R8)
# ---------------------------

# R8: the tag of a kind: 0 interactive, 1 headless, 2 sdk, 3 scheduled,
# 4 loop, 5 autoresearch
def sp_kind_tag(k: L.Run) -> Nat:
  match k:
    case L.Interactive{}:
      0n
    case L.Headless{}:
      1n
    case L.Sdk{}:
      2n
    case L.Scheduled{}:
      3n
    case L.Loop{}:
      4n
    case L.Autoresearch{}:
      5n

# R8: the tag of an auth: 0 plan, 1 API key, 2 local
def sp_auth_tag(a: L.Auth) -> Nat:
  match a:
    case L.Plan{}:
      0n
    case L.ApiKey{}:
      1n
    case L.Local{}:
      2n

# R8: limits on is T
def sp_on(t: L.Toggle) -> Bool:
  match t:
    case L.Off{}:
      False{}
    case L.On{}:
      True{}

# R8: the spelling of a limit: 0 unset, 1 and the number, 2 unlimited
def sp_w_val(v: L.Val, rest: String) -> String:
  match v:
    case L.Unset{}:
      Wr.put_nat(0n, rest)
    case L.At{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case L.Unlimited{}:
      Wr.put_nat(2n, rest)

# R8: the spelling of limits: money, tokens, time, tool calls, requests
def sp_w_lims(l: L.Lims, rest: String) -> String:
  match l:
    case L.Lims{c, k, m, n, r}:
      sp_w_val(c, sp_w_val(k, sp_w_val(m, sp_w_val(n, sp_w_val(r, rest)))))

# R8: the spelling of a source: 0 until finished, 1 set, 2 limits
# profile, 3 profile, 4 and the preset's place
def sp_w_src(x: L.Src, rest: String) -> String:
  match x:
    case L.UntilFinished{}:
      Wr.put_nat(0n, rest)
    case L.Set{}:
      Wr.put_nat(1n, rest)
    case L.LimitsProfile{}:
      Wr.put_nat(2n, rest)
    case L.Profile{}:
      Wr.put_nat(3n, rest)
    case L.Preset{i}:
      Wr.put_nat(4n, Wr.put_nat(i, rest))

# R8: the spelling of a window: its label, its used permille
def sp_w_win(w: L.Win, rest: String) -> String:
  match w:
    case L.Win{l, u}:
      Wr.put_str(l, Wr.put_nat(u, rest))

# R8: the tag of a preset: 0 quick, 1 deep
def sp_scale_tag(s: L.Scale) -> Nat:
  match s:
    case L.Quick{}:
      0n
    case L.Deep{}:
      1n

# R8: the tag of a key: 0 cost, 1 tokens, 2 time, 3 calls, 4 requests
def sp_key_tag(k: L.Key) -> Nat:
  match k:
    case L.KCost{}:
      0n
    case L.KTok{}:
      1n
    case L.KTime{}:
      2n
    case L.KCalls{}:
      3n
    case L.KReqs{}:
      4n

# R8: the spelling of a request: its tag, then its fields
def sp_w_req(q: FL.Req, rest: String) -> String:
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      Wr.put_nat(0n, Wr.put_bool(sp_on(t), Wr.put_nat(sp_kind_tag(k), Wr.put_nat(sp_auth_tag(a), sp_w_lims(set, Wr.put_list(~L.Lims, ~sp_w_lims, ps, sp_w_lims(own, rest)))))))
    case FL.QProfile{k, a}:
      Wr.put_nat(1n, Wr.put_nat(sp_kind_tag(k), Wr.put_nat(sp_auth_tag(a), rest)))
    case FL.QPreset{s, k, a}:
      Wr.put_nat(2n, Wr.put_nat(sp_scale_tag(s), Wr.put_nat(sp_kind_tag(k), Wr.put_nat(sp_auth_tag(a), rest))))
    case FL.QWraps{us, r}:
      Wr.put_nat(3n, Wr.put_list(~Nat, ~Wr.put_nat, us, Wr.put_nat(r, rest)))
    case FL.QNotice{ws, r, told}:
      Wr.put_nat(4n, Wr.put_list(~L.Win, ~sp_w_win, ws, Wr.put_nat(r, Wr.put_list(~String, ~Wr.put_str, told, rest))))
    case FL.QFloor{l, c, keep}:
      Wr.put_nat(5n, sp_w_lims(l, Budget.sp_w_ask(c, Budget.sp_w_ask(keep, rest))))
    case FL.QRenew{l, mark, now, a}:
      Wr.put_nat(6n, sp_w_lims(l, Budget.sp_w_amt(mark, Wr.put_nat(now, Budget.sp_w_acct(a, rest)))))
    case FL.QPrefix{text, ns}:
      Wr.put_nat(7n, Wr.put_str(text, Wr.put_list(~String, ~Wr.put_str, ns, rest)))

# R8: the spelling of a pair: its key's tag, its value
def sp_w_kv(p: L.KV, rest: String) -> String:
  match p:
    case L.KV{k, v}:
      Wr.put_nat(sp_key_tag(k), Wr.put_str(v, rest))

# R8: the spelling of filled limits: the limits, then the five sources
def sp_w_filled(f: L.Filled) -> String:
  match f:
    case L.Filled{l, L.Srcs{c, k, m, n, r}}:
      sp_w_lims(l, sp_w_src(c, sp_w_src(k, sp_w_src(m, sp_w_src(n, sp_w_src(r, ""))))))

# R8: the spelling of a window's place: 0 none | 1 and the place
def sp_w_mnat(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{i}:
      Wr.put_nat(1n, Wr.put_nat(i, ""))

# R8: the spelling of the windows told of: the places, the labels
def sp_w_told(t: L.Told) -> String:
  match t:
    case L.Told{now, after}:
      Wr.put_list(~Nat, ~Wr.put_nat, now, Wr.put_list(~String, ~Wr.put_str, after, ""))

# R8: the spelling of a short dimension: 0 none | 1 and its tag
def sp_w_mdim(m: Maybe<&2, B.Dim>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{d}:
      Wr.put_nat(1n, Wr.put_nat(Budget.sp_dim_tag(d), ""))

# R8: the spelling of a prefix: 0, the presets' places, the pairs, the
# rest | 1, the refused word
def sp_w_prefix(p: L.Prefix) -> String:
  match p:
    case L.Read{ks, kvs, r}:
      Wr.put_nat(0n, Wr.put_list(~Nat, ~Wr.put_nat, ks, Wr.put_list(~L.KV, ~sp_w_kv, kvs, Wr.put_str(r, ""))))
    case L.Refused{w}:
      Wr.put_nat(1n, Wr.put_str(w, ""))

# R8: the spelling of the model's answer to a request
def sp_w_reply(q: FL.Req) -> String:
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      sp_w_filled(L.fill(t, k, a, set, ps, own))
    case FL.QProfile{k, a}:
      sp_w_lims(L.profile(k, a), "")
    case FL.QPreset{s, k, a}:
      sp_w_lims(L.preset(s, k, a), "")
    case FL.QWraps{us, r}:
      sp_w_mnat(L.plan_wraps(us, r))
    case FL.QNotice{ws, r, told}:
      sp_w_told(L.plan_notice(ws, r, told))
    case FL.QFloor{l, c, keep}:
      sp_w_mdim(L.floor(l, c, keep))
    case FL.QRenew{l, mark, now, a}:
      Budget.sp_w_acct(L.renew(l, mark, now, a), "")
    case FL.QPrefix{text, ns}:
      sp_w_prefix(L.prefix(text, ns))

# R8: every number of a limit fits the wire
def sp_fit_val(v: L.Val) -> Bool:
  match v:
    case L.Unset{}:
      True{}
    case L.At{n}:
      LawsBase.wire_fits(n)
    case L.Unlimited{}:
      True{}

# R8: every number of limits fits the wire
def sp_fit_lims(l: L.Lims) -> Bool:
  match l:
    case L.Lims{c, k, m, n, r}:
      Bool.and(sp_fit_val(c), Bool.and(sp_fit_val(k), Bool.and(sp_fit_val(m), Bool.and(sp_fit_val(n), sp_fit_val(r)))))

def sp_fit_limss(ls: List<&2, L.Lims>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(sp_fit_lims(h), sp_fit_limss(t))

def sp_fit_wins(ws: List<&2, L.Win>) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{L.Win{+l, u}, t}:
      Bool.and(LawsBase.wire_fits(String.length(l)), Bool.and(LawsBase.wire_fits(u), sp_fit_wins(t)))

# R8: every number, count and length of a request fits the wire
def sp_fit_req(q: FL.Req) -> Bool:
  match q:
    case FL.QFill{t, k, a, set, +ps, own}:
      Bool.and(sp_fit_lims(set), Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), Bool.and(sp_fit_limss(ps), sp_fit_lims(own))))
    case FL.QProfile{k, a}:
      True{}
    case FL.QPreset{s, k, a}:
      True{}
    case FL.QWraps{+us, r}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Nat, us)), Bool.and(LawsBase.wire_nats_fit(us), LawsBase.wire_fits(r)))
    case FL.QNotice{+ws, r, +told}:
      Bool.and(LawsBase.wire_fits(List.length(&2, L.Win, ws)), Bool.and(sp_fit_wins(ws), Bool.and(LawsBase.wire_fits(r), LawsBase.wire_strs_fit(told))))
    case FL.QFloor{l, c, keep}:
      Bool.and(sp_fit_lims(l), Bool.and(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep)))
    case FL.QRenew{l, mark, now, a}:
      Bool.and(sp_fit_lims(l), Bool.and(Budget.sp_fit_amt(mark), Bool.and(LawsBase.wire_fits(now), Budget.sp_fit_acct(a))))
    case FL.QPrefix{text, +ns}:
      Bool.and(LawsBase.wire_fits(String.length(text)), LawsBase.wire_strs_fit(ns))

# R8: a tag's place in a request: the request's own tag; a kind; an
# auth; a preset's scale; a limit, by its dimension, of the limits a
# request names first (a fill's limits set, a floor's, a renewal's), of a
# fill's j-th preset (from 0), of a fill's profile
type Spot is Data:
  AtReq{}
  AtKind{}
  AtAuth{}
  AtScale{}
  InLims{d: B.Dim}
  InPreset{j: Nat, d: B.Dim}
  InOwn{d: B.Dim}

# R8: the m-th value past the known ones at a tag's place: a request's
# tag past 7 (prefix), a kind's past 5 (autoresearch), an auth's past 2
# (a local model), a scale's past 1 (deep), a limit's past 2 (unlimited)
def sp_unknown(p: Spot, m: Nat) -> Nat:
  match p:
    case AtReq{}:
      8n+m
    case AtKind{}:
      6n+m
    case AtAuth{}:
      3n+m
    case AtScale{}:
      2n+m
    case InLims{d}:
      3n+m
    case InPreset{j, d}:
      3n+m
    case InOwn{d}:
      3n+m

# R8: limits spelled up to dimension d's tag, then bad in its place
def sp_w_lims_cut(l: L.Lims, d: B.Dim, bad: String) -> String:
  match l:
    case L.Lims{c, k, m, n, r}:
      match d:
        case B.Cost{}:
          bad
        case B.Tok{}:
          sp_w_val(c, bad)
        case B.Time{}:
          sp_w_val(c, sp_w_val(k, bad))
        case B.Calls{}:
          sp_w_val(c, sp_w_val(k, sp_w_val(m, bad)))
        case B.Reqs{}:
          sp_w_val(c, sp_w_val(k, sp_w_val(m, sp_w_val(n, bad))))

def sp_w_items_cut.then(h: L.Lims, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      Some{sp_w_lims(h, s)}

# R8: the items of ps spelled up to the j-th one's limit of dimension d,
# then bad in its place; none when ps has no j-th item
def sp_w_items_cut(ps: List<&2, L.Lims>, j: Nat, d: B.Dim, bad: String) -> Maybe<&2, String>:
  match ps:
    case Nil{}:
      None{}
    case Con{h, t}:
      match j:
        case 0n:
          Some{sp_w_lims_cut(h, d, bad)}
        case 1n+i:
          sp_w_items_cut.then(h, sp_w_items_cut(t, i, d, bad))

# R8: a fill's head before its limits set: its tag, the toggle, the kind,
# the auth
def sp_w_fill_head(t: L.Toggle, k: L.Run, a: L.Auth, rest: String) -> String:
  Wr.put_nat(0n, Wr.put_bool(sp_on(t), Wr.put_nat(sp_kind_tag(k), Wr.put_nat(sp_auth_tag(a), rest))))

def sp_w_fill_cut.ps(t: L.Toggle, k: L.Run, a: L.Auth, set: L.Lims, n: Nat, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      Some{sp_w_fill_head(t, k, a, sp_w_lims(set, Wr.put_nat(n, s)))}

# R8: a fill spelled up to the tag at p, then bad in its place
def sp_w_fill_cut(p: Spot, t: L.Toggle, k: L.Run, a: L.Auth, set: L.Lims, +ps: List<&2, L.Lims>, own: L.Lims, bad: String) -> Maybe<&2, String>:
  match p:
    case AtReq{}:
      Some{bad}
    case AtKind{}:
      Some{Wr.put_nat(0n, Wr.put_bool(sp_on(t), bad))}
    case AtAuth{}:
      Some{Wr.put_nat(0n, Wr.put_bool(sp_on(t), Wr.put_nat(sp_kind_tag(k), bad)))}
    case AtScale{}:
      None{}
    case InLims{d}:
      Some{sp_w_fill_head(t, k, a, sp_w_lims_cut(set, d, bad))}
    case InPreset{j, d}:
      sp_w_fill_cut.ps(t, k, a, set, List.length(&2, L.Lims, ps), sp_w_items_cut(ps, j, d, bad))
    case InOwn{d}:
      Some{sp_w_fill_head(t, k, a, sp_w_lims(set, Wr.put_list(~L.Lims, ~sp_w_lims, ps, sp_w_lims_cut(own, d, bad))))}

# R8: a request with no tag but its own spelled up to it, then bad
def sp_w_only_cut(p: Spot, bad: String) -> Maybe<&2, String>:
  match p:
    case AtReq{}:
      Some{bad}
    case AtKind{}:
      None{}
    case AtAuth{}:
      None{}
    case AtScale{}:
      None{}
    case InLims{d}:
      None{}
    case InPreset{j, d}:
      None{}
    case InOwn{d}:
      None{}

# R8: a request spelled up to the tag at p, then bad in its place; none
# when the request has no tag at p
def sp_w_req_cut(q: FL.Req, p: Spot, bad: String) -> Maybe<&2, String>:
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      sp_w_fill_cut(p, t, k, a, set, ps, own, bad)
    case FL.QProfile{k, a}:
      match p:
        case AtReq{}:
          Some{bad}
        case AtKind{}:
          Some{Wr.put_nat(1n, bad)}
        case AtAuth{}:
          Some{Wr.put_nat(1n, Wr.put_nat(sp_kind_tag(k), bad))}
        case AtScale{}:
          None{}
        case InLims{d}:
          None{}
        case InPreset{j, d}:
          None{}
        case InOwn{d}:
          None{}
    case FL.QPreset{s, k, a}:
      match p:
        case AtReq{}:
          Some{bad}
        case AtKind{}:
          Some{Wr.put_nat(2n, Wr.put_nat(sp_scale_tag(s), bad))}
        case AtAuth{}:
          Some{Wr.put_nat(2n, Wr.put_nat(sp_scale_tag(s), Wr.put_nat(sp_kind_tag(k), bad)))}
        case AtScale{}:
          Some{Wr.put_nat(2n, bad)}
        case InLims{d}:
          None{}
        case InPreset{j, d}:
          None{}
        case InOwn{d}:
          None{}
    case FL.QWraps{us, r}:
      sp_w_only_cut(p, bad)
    case FL.QNotice{ws, r, told}:
      sp_w_only_cut(p, bad)
    case FL.QFloor{l, c, keep}:
      match p:
        case AtReq{}:
          Some{bad}
        case AtKind{}:
          None{}
        case AtAuth{}:
          None{}
        case AtScale{}:
          None{}
        case InLims{d}:
          Some{Wr.put_nat(5n, sp_w_lims_cut(l, d, bad))}
        case InPreset{j, d}:
          None{}
        case InOwn{d}:
          None{}
    case FL.QRenew{l, mark, now, a}:
      match p:
        case AtReq{}:
          Some{bad}
        case AtKind{}:
          None{}
        case AtAuth{}:
          None{}
        case AtScale{}:
          None{}
        case InLims{d}:
          Some{Wr.put_nat(6n, sp_w_lims_cut(l, d, bad))}
        case InPreset{j, d}:
          None{}
        case InOwn{d}:
          None{}
    case FL.QPrefix{text, ns}:
      sp_w_only_cut(p, bad)

# R8: a request with the m-th unknown value at the tag at p, whatever
# follows it (rest); none when the request has no tag at p
def sp_w_req_bad(q: FL.Req, +p: Spot, m: Nat, rest: String) -> Maybe<&2, String>:
  sp_w_req_cut(q, p, Wr.put_nat(sp_unknown(p, m), rest))

# Laws: the fill (R1)
# -------------------

# LAW limits_set_wins (R1): a dimension the principal set for the run
# (a number or unlimited) takes that limit, source set, whatever the
# presets, the toggle, the profiles
# EXCLUDES: a preset or a profile before the principal's limit, a set
#   `unlimited` replaced by a number, the source recorded as a profile
law limits_set_wins:
  for t: L.Toggle
  for k: L.Run
  for a: L.Auth
  for +set: L.Lims
  for ps: List<&2, L.Lims>
  for own: L.Lims
  for +d: B.Dim
  for g: {S.given(S.dim(d, set)) == True{} : Bool}
  {S.filled(d, L.fill(t, k, a, set, ps, own)) == L.Pick{S.dim(d, set), L.Set{}} : L.Pick}

# LAW limits_preset_last (R1): a dimension the principal did not set
# takes the last preset that gives it, with that preset's place
# EXCLUDES: the first preset winning over a later one, a profile before a
#   preset, a wrong place recorded
law limits_preset_last:
  for t: L.Toggle
  for k: L.Run
  for a: L.Auth
  for +set: L.Lims
  for +ps: List<&2, L.Lims>
  for own: L.Lims
  for +d: B.Dim
  for p: L.Pick
  for g: {S.given(S.dim(d, set)) == False{} : Bool}
  for e: {S.last(d, ps) == Some{p} : Maybe<&2, L.Pick>}
  {S.filled(d, L.fill(t, k, a, set, ps, own)) == p : L.Pick}

# LAW limits_off_until_finished (R1): with limits off, a dimension neither
# set nor given by a preset is unlimited, until finished, whatever the
# profiles say
# EXCLUDES: a default backstop with limits off, the principal's profile
#   applied with limits off, an unset dimension left unset
law limits_off_until_finished:
  for k: L.Run
  for a: L.Auth
  for +set: L.Lims
  for +ps: List<&2, L.Lims>
  for own: L.Lims
  for +d: B.Dim
  for g: {S.given(S.dim(d, set)) == False{} : Bool}
  for e: {S.last(d, ps) == None{} : Maybe<&2, L.Pick>}
  {S.filled(d, L.fill(L.Off{}, k, a, set, ps, own)) == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}

# LAW limits_on_profile (R1): with limits on, a dimension neither set nor
# given by a preset takes the principal's profile when it gives one,
# source profile
# EXCLUDES: the limits profile before the principal's, the principal's
#   `unlimited` replaced by a number
law limits_on_profile:
  for k: L.Run
  for a: L.Auth
  for +set: L.Lims
  for +ps: List<&2, L.Lims>
  for +own: L.Lims
  for +d: B.Dim
  for g: {S.given(S.dim(d, set)) == False{} : Bool}
  for e: {S.last(d, ps) == None{} : Maybe<&2, L.Pick>}
  for h: {S.given(S.dim(d, own)) == True{} : Bool}
  {S.filled(d, L.fill(L.On{}, k, a, set, ps, own)) == L.Pick{S.dim(d, own), L.Profile{}} : L.Pick}

# LAW limits_on_table (R1): with limits on and nothing else given, a
# dimension takes the limits profile's number, source limits profile; a
# dimension the limits profile leaves unset is unlimited, until finished
# EXCLUDES: an unset dimension left unset, the limits profile's number
#   recorded as set by the principal, money filled with a number
law limits_on_table:
  for +k: L.Run
  for +a: L.Auth
  for +set: L.Lims
  for +ps: List<&2, L.Lims>
  for +own: L.Lims
  for +d: B.Dim
  for g: {S.given(S.dim(d, set)) == False{} : Bool}
  for e: {S.last(d, ps) == None{} : Maybe<&2, L.Pick>}
  for h: {S.given(S.dim(d, own)) == False{} : Bool}
  {S.filled(d, L.fill(L.On{}, k, a, set, ps, own)) == S.table(S.dim(d, L.profile(k, a))) : L.Pick}

# Laws: the limits profile and the presets (R2)
# ---------------------------------------------

# LAW limits_profile_table (R2): pin of the table of spec/README.md B15
# (the owner's limits profile, 2026-11-13; basis: the largest measured
# run, 320 requests, 400 tool calls, 743 s): per kind time (ms), tool
# calls, model requests; a local model no tool calls; money and tokens
# never. Rows in the order Interactive, Headless, Sdk, Scheduled, Loop,
# Autoresearch, each for a plan, an API key, a local model.
# EXCLUDES: a shipped `unlimited`, a zero, a money or token default, a
#   kind's row swapped with another's
law limits_profile_table:
  {[L.profile(L.Interactive{}, L.Plan{}), L.profile(L.Interactive{}, L.ApiKey{}), L.profile(L.Interactive{}, L.Local{}), L.profile(L.Headless{}, L.Plan{}), L.profile(L.Headless{}, L.ApiKey{}), L.profile(L.Headless{}, L.Local{}), L.profile(L.Sdk{}, L.Plan{}), L.profile(L.Sdk{}, L.ApiKey{}), L.profile(L.Sdk{}, L.Local{})] == [L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.Unset{}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.Unset{}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.Unset{}, L.At{3200n}}] : List<&2, L.Lims>} &
  {[L.profile(L.Scheduled{}, L.Plan{}), L.profile(L.Scheduled{}, L.ApiKey{}), L.profile(L.Scheduled{}, L.Local{}), L.profile(L.Loop{}, L.Plan{}), L.profile(L.Loop{}, L.ApiKey{}), L.profile(L.Loop{}, L.Local{}), L.profile(L.Autoresearch{}, L.Plan{}), L.profile(L.Autoresearch{}, L.ApiKey{}), L.profile(L.Autoresearch{}, L.Local{})] == [L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{4000n}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.Unset{}, L.At{3200n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{28800000n}, L.At{8000n}, L.At{6400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{28800000n}, L.At{8000n}, L.At{6400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{28800000n}, L.Unset{}, L.At{6400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{43200000n}, L.At{12000n}, L.At{9600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{43200000n}, L.At{12000n}, L.At{9600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{43200000n}, L.Unset{}, L.At{9600n}}] : List<&2, L.Lims>}

# LAW limits_preset_table (R2): pin of the shipped presets of
# spec/README.md B20 (the owner's presets, 2026-11-13): `quick` a quarter
# of the limits profile (limits_profile_table), `deep` four times it, in
# the dimensions the limits profile sets. Rows: quick then deep, each in
# the order Interactive, Headless, Sdk, Scheduled, Loop, Autoresearch,
# each for a plan, an API key, a local model.
# EXCLUDES: a preset that fills money or tokens, quick and deep swapped,
#   quick as the profile itself, a preset `unlimited`
law limits_preset_table:
  {[L.preset(L.Quick{}, L.Interactive{}, L.Plan{}), L.preset(L.Quick{}, L.Interactive{}, L.ApiKey{}), L.preset(L.Quick{}, L.Interactive{}, L.Local{}), L.preset(L.Quick{}, L.Headless{}, L.Plan{}), L.preset(L.Quick{}, L.Headless{}, L.ApiKey{}), L.preset(L.Quick{}, L.Headless{}, L.Local{}), L.preset(L.Quick{}, L.Sdk{}, L.Plan{}), L.preset(L.Quick{}, L.Sdk{}, L.ApiKey{}), L.preset(L.Quick{}, L.Sdk{}, L.Local{}), L.preset(L.Quick{}, L.Scheduled{}, L.Plan{}), L.preset(L.Quick{}, L.Scheduled{}, L.ApiKey{}), L.preset(L.Quick{}, L.Scheduled{}, L.Local{}), L.preset(L.Quick{}, L.Loop{}, L.Plan{}), L.preset(L.Quick{}, L.Loop{}, L.ApiKey{}), L.preset(L.Quick{}, L.Loop{}, L.Local{}), L.preset(L.Quick{}, L.Autoresearch{}, L.Plan{}), L.preset(L.Quick{}, L.Autoresearch{}, L.ApiKey{}), L.preset(L.Quick{}, L.Autoresearch{}, L.Local{})] == [L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.Unset{}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.Unset{}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{3600000n}, L.Unset{}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{900000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{900000n}, L.At{1000n}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{900000n}, L.Unset{}, L.At{800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{7200000n}, L.At{2000n}, L.At{1600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{7200000n}, L.At{2000n}, L.At{1600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{7200000n}, L.Unset{}, L.At{1600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{10800000n}, L.At{3000n}, L.At{2400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{10800000n}, L.At{3000n}, L.At{2400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{10800000n}, L.Unset{}, L.At{2400n}}] : List<&2, L.Lims>} &
  {[L.preset(L.Deep{}, L.Interactive{}, L.Plan{}), L.preset(L.Deep{}, L.Interactive{}, L.ApiKey{}), L.preset(L.Deep{}, L.Interactive{}, L.Local{}), L.preset(L.Deep{}, L.Headless{}, L.Plan{}), L.preset(L.Deep{}, L.Headless{}, L.ApiKey{}), L.preset(L.Deep{}, L.Headless{}, L.Local{}), L.preset(L.Deep{}, L.Sdk{}, L.Plan{}), L.preset(L.Deep{}, L.Sdk{}, L.ApiKey{}), L.preset(L.Deep{}, L.Sdk{}, L.Local{}), L.preset(L.Deep{}, L.Scheduled{}, L.Plan{}), L.preset(L.Deep{}, L.Scheduled{}, L.ApiKey{}), L.preset(L.Deep{}, L.Scheduled{}, L.Local{}), L.preset(L.Deep{}, L.Loop{}, L.Plan{}), L.preset(L.Deep{}, L.Loop{}, L.ApiKey{}), L.preset(L.Deep{}, L.Loop{}, L.Local{}), L.preset(L.Deep{}, L.Autoresearch{}, L.Plan{}), L.preset(L.Deep{}, L.Autoresearch{}, L.ApiKey{}), L.preset(L.Deep{}, L.Autoresearch{}, L.Local{})] == [L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.Unset{}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.Unset{}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{57600000n}, L.Unset{}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.At{16000n}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{14400000n}, L.Unset{}, L.At{12800n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{115200000n}, L.At{32000n}, L.At{25600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{115200000n}, L.At{32000n}, L.At{25600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{115200000n}, L.Unset{}, L.At{25600n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{172800000n}, L.At{48000n}, L.At{38400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{172800000n}, L.At{48000n}, L.At{38400n}}, L.Lims{L.Unset{}, L.Unset{}, L.At{172800000n}, L.Unset{}, L.At{38400n}}] : List<&2, L.Lims>}

# Laws: the plan (R3, R4)
# -----------------------

# LAW limits_plan_wraps_first (R3): a plan run wraps up at the first
# window whose used permille is at or past 1000 - reserve; none when no
# window is
# EXCLUDES: a strict `past` (a window exactly at 80 % not wrapping), the
#   last window over instead of the first, the reserve ignored, a wrong
#   place
law limits_plan_wraps_first:
  for +us: List<&2, Nat>
  for +r: Nat
  {L.plan_wraps(us, r) == S.over(us, Nat.sub(1000n, r)) : Maybe<&2, Nat>}

# LAW limits_notice_tells (R4): exactly the windows at or past 1000 -
# reserve whose label was not told of are told of now, in order
# EXCLUDES: a notice for a window below the line, a second notice for a
#   label told of, a window at the line missed
law limits_notice_tells:
  for +ws: List<&2, L.Win>
  for +r: Nat
  for +told: List<&2, String>
  {S.now(L.plan_notice(ws, r, told)) == S.fresh(ws, Nat.sub(1000n, r), told) : List<&2, Nat>}

# LAW limits_notice_told (R4): after the readings ws, label s is told of
# exactly when a window of that label is at or past 1000 - reserve, or it
# was told of and no window of that label read below the line
# EXCLUDES: a label kept after a reading below the line (never armed
#   again), a label at or past the line left out (told of twice), a told
#   label without a reading dropped (told of again), a label dropped or
#   armed by another window's reading
law limits_notice_told:
  for +ws: List<&2, L.Win>
  for +r: Nat
  for +told: List<&2, String>
  for +s: String
  {S.among(s, S.told(L.plan_notice(ws, r, told))) == S.told_after(s, ws, Nat.sub(1000n, r), told) : Bool}

# R4: no text of ls is there twice
def sp_distinct(ls: List<&2, String>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      Bool.and(Bool.not(S.among(h, t)), sp_distinct(t))

# LAW limits_notice_told_once (R4): after the readings ws, each label
# told of is kept once: from windows of distinct labels and labels told
# of once, the labels told of after hold no label twice
# EXCLUDES: a label kept again beside its new copy (the list Rust keeps
#   and sends back on every reading growing while a window stays at or
#   past the line), a told label copied for each reading
law limits_notice_told_once:
  for +ws: List<&2, L.Win>
  for +r: Nat
  for +told: List<&2, String>
  for dw: {S.distinct(ws) == True{} : Bool}
  for dt: {sp_distinct(told) == True{} : Bool}
  {sp_distinct(S.told(L.plan_notice(ws, r, told))) == True{} : Bool}

# LAW limits_notice_kept_once (R4): after any readings ws and any labels
# told of, the labels told of after hold no label twice
# EXCLUDES: a label kept twice when two windows of a reading share it
#   (two weekly windows both labelled 7d), a label told of twice kept
#   twice
law limits_notice_kept_once:
  for +ws: List<&2, L.Win>
  for +r: Nat
  for +told: List<&2, String>
  {sp_distinct(S.told(L.plan_notice(ws, r, told))) == True{} : Bool}

# LAW limits_notice_example (R4): anchor: a 5-hour window at 85 % is told
# of once; the same reading again tells nothing; a reading at 10 % arms it
# again; the next crossing is told; another window's reading leaves it
# EXCLUDES: a notice per reading, a label told of forever, a label dropped
#   for another window's reading
law limits_notice_example:
  {[S.now(L.plan_notice([L.Win{"5h", 850n}, L.Win{"7d", 100n}], 200n, Nil{})), S.now(L.plan_notice([L.Win{"5h", 850n}, L.Win{"7d", 100n}], 200n, ["5h"])), S.now(L.plan_notice([L.Win{"5h", 900n}], 200n, S.told(L.plan_notice([L.Win{"5h", 100n}], 200n, ["5h"]))))] == [[0n], Nil{}, [0n]] : List<&2, List<&2, Nat>>} &
  {[S.told(L.plan_notice([L.Win{"5h", 850n}, L.Win{"7d", 100n}], 200n, Nil{})), S.told(L.plan_notice([L.Win{"5h", 100n}], 200n, ["5h", "7d"])), S.told(L.plan_notice([L.Win{"7d", 100n}], 200n, ["5h"]))] == [["5h"], ["7d"], ["5h"]] : List<&2, List<&2, String>>}

# Laws: the floor (R5)
# --------------------

# LAW limits_floor_is_reserve (R5): limits that bound every dimension hold
# the run's first work request exactly when the reservation of that
# request, with its final-answer reserve, on an account holding exactly
# those limits is granted; otherwise they name the dimension the
# reservation is short in
# EXCLUDES: a floor that ignores the final-answer reserve, a floor in
#   another dimension order, a run started that the ledger then refuses
law limits_floor_is_reserve:
  for +l: L.Lims
  for +c: B.Ask
  for +keep: B.Ask
  for id: Nat
  for step: B.Ask
  for h: {S.bounded(l) == True{} : Bool}
  {L.floor(l, c, keep) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), keep, step, c, Nil{}, S.fresh_acct(l))) : Maybe<&2, B.Dim>}

# LAW limits_floor_unbounded (R5): a dimension without a number (unset or
# unlimited) is never the one a run is short in
# EXCLUDES: an unlimited dimension read as a limit of 0, a run refused
#   for money it has no limit on
law limits_floor_unbounded:
  for +l: L.Lims
  for c: B.Ask
  for keep: B.Ask
  for +d: B.Dim
  for h: {S.is_at(S.dim(d, l)) == False{} : Bool}
  {S.names(d, L.floor(l, c, keep)) == False{} : Bool}

# LAW limits_floor_drops_unbounded (R5): a dimension without a number
# takes no part in the floor: the floor of any limits is the floor of the
# same limits with each such dimension a limit of 0 and the request and
# its reserve asking nothing of it, limits that bound every dimension,
# which limits_floor_is_reserve holds to the ledger
# EXCLUDES: a floor that checks nothing when one dimension is unbounded, a
#   floor that checks a bounded dimension only beside other bounded ones
law limits_floor_drops_unbounded:
  for l: L.Lims
  for c: B.Ask
  for keep: B.Ask
  {L.floor(l, c, keep) == L.floor(S.closed(l), S.only(l, c), S.only(l, keep)) : Maybe<&2, B.Dim>}

# Laws: renewal (R6)
# ------------------

# LAW limits_renew_conserves (R6): in a bounded spent dimension, what is
# free after a renewal plus what the run used (spent since mark, held,
# lent) is the limit, or what the run used when that passed it
# EXCLUDES: a renewal that forgets the holds, the lent or the spend since
#   the run's start, one that restores the whole limit, free past the
#   limit
law limits_renew_conserves:
  for +l: L.Lims
  for +mark: B.Amt
  for now: Nat
  for +a: B.Acct
  for +d: B.Dim
  for sd: {S.spent_dim(d) == True{} : Bool}
  for h: {S.is_at(S.dim(d, l)) == True{} : Bool}
  {Nat.add(SL.at(d, SL.free(L.renew(l, mark, now, a))), S.use(d, mark, a)) == Nat.max(S.num(S.dim(d, l)), S.use(d, mark, a)) : Nat}

# LAW limits_renew_unbounded_keeps (R6): a spent dimension without a
# number keeps what is free
# EXCLUDES: an unlimited dimension's free set to 0 or to a limit
law limits_renew_unbounded_keeps:
  for +l: L.Lims
  for mark: B.Amt
  for now: Nat
  for +a: B.Acct
  for +d: B.Dim
  for h: {S.is_at(S.dim(d, l)) == False{} : Bool}
  {SL.at(d, SL.free(L.renew(l, mark, now, a))) == SL.at(d, SL.free(a)) : Nat}

# LAW limits_renew_keeps (R6): a renewal keeps the spend, the lent, the
# overrun and the holds; the deadline is now plus a time limit, else as it
# was
# EXCLUDES: a renewal that forgets the overrun or the holds, resets the
#   spend, keeps an old deadline under a new time limit
law limits_renew_keeps:
  for +l: L.Lims
  for mark: B.Amt
  for +now: Nat
  for +a: B.Acct
  {(SL.spent(L.renew(l, mark, now, a)), (SL.lent(L.renew(l, mark, now, a)), (SL.over(L.renew(l, mark, now, a)), (SL.holds(L.renew(l, mark, now, a)), SL.until(L.renew(l, mark, now, a)))))) == (SL.spent(a), (SL.lent(a), (SL.over(a), (SL.holds(a), S.deadline(S.dim(B.Time{}, l), now, SL.until(a)))))) : B.Amt & (B.Amt & (B.Amt & (List<&2, B.Hold> & Nat)))}

# Laws: the prefix (R7)
# ---------------------

# LAW limits_prefix_untouched (R7): a message that does not open with
# `/b` (folded) then a space or its end has no prefix: no preset, no
# pair, the whole message the rest as typed
# EXCLUDES: `/bob` read as `/b` then `ob`, a message without the prefix
#   trimmed or folded, a leading space taken for the start of the prefix
law limits_prefix_untouched:
  for +s: String
  for ns: List<&2, String>
  for h: {S.opens(s) == False{} : Bool}
  {L.prefix(s, ns) == L.Read{Nil{}, Nil{}, s} : L.Prefix}

# LAW limits_prefix_reads (R7): a message of an opener a b that reads as
# `/b`, then words each after a gap of spaces, then trailing spaces, reads
# word by word in order: a preset name (folded) its place, a known key
# (folded) before `=` a pair with its value folded and `,` read as `.`, a
# pair with an empty value or a key given before refused with the word as
# typed; the first other word, with every word and gap after it and the
# trailing spaces, is the rest verbatim
# EXCLUDES: a reader that eats `2h` in `/b 5 2h after` or in `/b quick 2h
#   after` (a word that looks like a duration taken as a value), a rest
#   trimmed or with its gaps collapsed, full-width digits kept in a value,
#   `,` kept in a value, a repeated key taking the last value, presets or
#   pairs out of order, a refused word folded, a tab or ideographic space
#   not read as a gap
law limits_prefix_reads:
  for +a: Char
  for +b: Char
  for +xs: List<&2, S.Item>
  for +t: String
  for +ns: List<&2, String>
  for ho: {S.opener(a, b) == True{} : Bool}
  for hx: {S.items(xs) == True{} : Bool}
  for ht: {S.spaces(t) == True{} : Bool}
  {L.prefix(SCon{a, SCon{b, S.spell(xs, t)}}, ns) == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}

# LAW limits_prefix_example (R7): anchor: the `/b` prefix of messages:
# a preset then a message word that looks like a duration, full-width
# digits and a decimal comma, a key given twice, an empty value, a word
# with an unknown key ending the prefix, `/bob`, a full-width `／ｂ`
# EXCLUDES: a prefix that eats `2h` of the message, a value read before
#   folding, a repeated key taking the last value
law limits_prefix_example:
  {[L.prefix("/b quick 2h after lunch", ["quick"]), L.prefix("/b cost=1,5 time=２h  hi  there", ["quick"]), L.prefix("/b cost=1 cost=2 x", Nil{}), L.prefix("/b time= x", Nil{}), L.prefix("/b deep x=1 cost=2", ["quick", "deep"]), L.prefix("/bob hi", Nil{}), L.prefix("／ｂ\tquick", ["quick"])] == [L.Read{[0n], Nil{}, "2h after lunch"}, L.Read{Nil{}, [L.KV{L.KCost{}, "1.5"}, L.KV{L.KTime{}, "2h"}], "hi  there"}, L.Refused{"cost=2"}, L.Refused{"time="}, L.Read{[1n], Nil{}, "x=1 cost=2"}, L.Read{Nil{}, Nil{}, "/bob hi"}, L.Read{[0n], Nil{}, ""}] : List<&2, L.Prefix>}

# Laws: the entry (R8)
# --------------------

# LAW limits_entry_answers (R8): the entry answers every request Rust
# spells, every number, count and length within the wire, with the
# model's answer spelled
# EXCLUDES: fields read in another order (the limits set read as the
#   profile, the mark read as the account's spent), a tag read as another
#   kind, auth, preset or source, a dimension of the limits swapped, a
#   preset list or a window lost, a default
law limits_entry_answers:
  for +q: FL.Req
  for fit: {sp_fit_req(q) == True{} : Bool}
  {FL.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW limits_entry_left_over (R8): a spelled request followed by more
# input answers the error form
# EXCLUDES: the input after the request ignored or read into a field
law limits_entry_left_over:
  for +q: FL.Req
  for +ch: Char
  for +t: String
  for fit: {sp_fit_req(q) == True{} : Bool}
  {FL.ffi(sp_w_req(q, SCon{ch, t})) == Wr.err("limits: malformed request") : String}

# LAW limits_entry_unknown_tag (R8): a tag past the known ones answers
# the error form, whatever follows it: a request tag past 7 (prefix), a
# kind tag past 5 (autoresearch) in a profile, an auth tag past 2 (a
# local model) in a profile of any kind, a preset tag past 1 (deep), a
# limit tag past 2 (unlimited) in a floor's limits; every such tag within
# the wire
# EXCLUDES: an unknown tag read as a known one (a newer caller's request
#   answered as a prefix or a plan reading, an unknown kind as
#   autoresearch, an unknown auth as a local model, an unknown preset as
#   deep, an unknown limit as unset or unlimited)
law limits_entry_unknown_tag:
  for +k: L.Run
  for +m: Nat
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for +rest: String
  for fm: {LawsBase.wire_fits(8n+m) == True{} : Bool}
  for fa: {LawsBase.wire_fits(6n+a) == True{} : Bool}
  for fb: {LawsBase.wire_fits(3n+b) == True{} : Bool}
  for fc: {LawsBase.wire_fits(2n+c) == True{} : Bool}
  for fd: {LawsBase.wire_fits(3n+d) == True{} : Bool}
  {FL.ffi(Wr.put_nat(8n+m, rest)) == Wr.err("limits: malformed request") : String} &
  {FL.ffi(Wr.put_nat(1n, Wr.put_nat(6n+a, rest))) == Wr.err("limits: malformed request") : String} &
  {FL.ffi(Wr.put_nat(1n, Wr.put_nat(sp_kind_tag(k), Wr.put_nat(3n+b, rest)))) == Wr.err("limits: malformed request") : String} &
  {FL.ffi(Wr.put_nat(2n, Wr.put_nat(2n+c, rest))) == Wr.err("limits: malformed request") : String} &
  {FL.ffi(Wr.put_nat(5n, Wr.put_nat(3n+d, rest))) == Wr.err("limits: malformed request") : String}

# LAW limits_entry_tag_anywhere (R8): in every request Rust spells
# (every number, count and length within the wire), an unknown value at
# any of its tags, whatever follows it, answers the error form: the
# request's tag; the kind and the auth of a fill, a profile, a preset; a
# preset's scale; each of the five limits of a fill's limits set, of each
# of its presets, of its profile, of a floor's and a renewal's limits;
# every such value within the wire
# EXCLUDES: an unknown tag read as a known one at any place (a fill's
#   time limit 3 read as unlimited, a fill's or a preset's kind 6 read as
#   autoresearch, a second preset's limit tag read as unset), an unknown
#   tag checked only at the first place of its kind
law limits_entry_tag_anywhere:
  for +q: FL.Req
  for +p: Spot
  for +m: Nat
  for +rest: String
  for +s: String
  for fit: {sp_fit_req(q) == True{} : Bool}
  for fu: {LawsBase.wire_fits(sp_unknown(p, m)) == True{} : Bool}
  for at: {sp_w_req_bad(q, p, m, rest) == Some{s} : Maybe<&2, String>}
  {FL.ffi(s) == Wr.err("limits: malformed request") : String}

# LAW limits_entry_refuses (R8): every error the entry answers is exactly
# `E limits: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law limits_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FL.ffi(s)) == True{} : Bool}
  {FL.ffi(s) == Wr.err("limits: malformed request") : String}

# LAW limits_entry_exact (R8): every input the entry does not answer with
# the error form is a request Rust spells, every number, count and length
# within the wire, and nothing after it
# EXCLUDES: a decision answered on input that is no request: a request cut
#   off before its end (a floor's missing final-answer reserve, a missing
#   field defaulted), a number not in canonical decimal (a leading zero,
#   more than 14 digits, no ','), a list shorter than its count, a known
#   tag read from an unknown one
law limits_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FL.ffi(s)) == False{} : Bool}
  exs q: FL.Req
  {s == sp_w_req(q, "") : String} & {sp_fit_req(q) == True{} : Bool}

# LAW limits_entry_example (R8): anchor: wire strings Rust sends and the
# replies it reads; an unknown tag, input left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law limits_entry_example:
  {[FL.ffi("0,T0,1,0,0,0,0,0,0,0,0,0,0,0,"), FL.ffi("0,F0,1,1,5,0,0,0,0,0,0,0,0,0,0,"), FL.ffi("2,0,3,1,"), FL.ffi("3,3,10,800,900,200,"), FL.ffi("4,2,2,5h900,2,7d100,200,1,2,7d"), FL.ffi("7,23,/b quick 2h after lunch1,5,quick")] == ["2,2,1,14400000,1,4000,1,3200,0,0,2,2,2,", "1,5,2,2,2,2,1,0,0,0,0,", "0,0,1,900000,1,1000,1,800,", "1,1,", "1,0,1,2,5h", "0,1,0,0,14,2h after lunch"] : List<&2, String>} &
  {[FL.ffi("8,"), FL.ffi("1,0,0,x"), FL.ffi("1,6,0,")] == [Wr.err("limits: malformed request"), Wr.err("limits: malformed request"), Wr.err("limits: malformed request")] : List<&2, String>}
