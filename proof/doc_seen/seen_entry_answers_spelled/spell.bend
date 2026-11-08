# eukhe: the entry's own encoders of bend/ffi_doc_seen.bend spell what the
# laws' spellers (laws/doc_seen.bend seen.spell_*) spell, field by field
# (used by the entry laws of doc_seen to reach seen_entry_refines and the
# round trips of its proof)

import Base
import ../../../bend/doc_seen.bend as Ds
import ../../../bend/ffi_doc_seen.bend as Fds
import ../../../bend/wire.bend as Wr
import ../../../laws/doc_seen.bend as DocSeen

# a Maybe<Nat>
def ssp_mnat(m: Maybe<&2, Nat>, -rest: String) -> {Fds.put_mnat(m, rest) == DocSeen.seen.spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a seen run
def ssp_iv(iv: Ds.Iv, -rest: String) -> {Fds.put_iv(iv, rest) == DocSeen.seen.spell_iv(iv, rest) : String}:
  match iv:
    case Ds.Iv{lo, hi}:
      {==}

# an anchor
def ssp_at(a: Ds.At, +rest: String) -> {Fds.put_at(a, rest) == DocSeen.seen.spell_at(a, rest) : String}:
  match a:
    case Ds.At{n, w}:
      %ssp_mnat(w, rest) : {Wr.put_nat(n, Fds.put_mnat(w, rest)) == Wr.put_nat(n, _) : String}
      {==}

# a line shown
def ssp_show(x: Ds.Show, +rest: String) -> {Fds.put_show(x, rest) == DocSeen.seen.spell_show(x, rest) : String}:
  match x:
    case Ds.Show{n, c}:
      %ssp_mnat(c, rest) : {Wr.put_nat(n, Fds.put_mnat(c, rest)) == Wr.put_nat(n, _) : String}
      {==}

# ---- seen runs ----

def ssp_iv_step(x: Ds.Iv, r: Nat & String) -> {Wr.put_list.step(~Ds.Iv, ~Fds.put_iv, x, r) == Wr.put_list.step(~Ds.Iv, ~DocSeen.seen.spell_iv, x, r) : Nat & String}:
  match r:
    case (n, s):
      %ssp_iv(x, s) : {(1n+n, Fds.put_iv(x, s)) == (1n+n, _) : Nat & String}
      {==}

def ssp_ivs_go(xs: List<&2, Ds.Iv>, +rest: String) -> {Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, xs, rest) == Wr.put_list.go(~Ds.Iv, ~DocSeen.seen.spell_iv, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %ssp_ivs_go(t, rest) : {Wr.put_list.step(~Ds.Iv, ~Fds.put_iv, x, Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, t, rest)) == Wr.put_list.step(~Ds.Iv, ~DocSeen.seen.spell_iv, x, _) : Nat & String}
      ssp_iv_step(x, Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, t, rest))

# the seen runs: the entry's list encoder is the spec's
def ssp_ivs(xs: List<&2, Ds.Iv>, +rest: String) -> {Wr.put_list(~Ds.Iv, ~Fds.put_iv, xs, rest) == DocSeen.seen.spell_seen(xs, rest) : String}:
  %ssp_ivs_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Ds.Iv, ~Fds.put_iv, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# ---- anchors ----

def ssp_at_step(x: Ds.At, r: Nat & String) -> {Wr.put_list.step(~Ds.At, ~Fds.put_at, x, r) == Wr.put_list.step(~Ds.At, ~DocSeen.seen.spell_at, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %ssp_at(x, s) : {(1n+n, Fds.put_at(x, s)) == (1n+n, _) : Nat & String}
      {==}

def ssp_ats_go(xs: List<&2, Ds.At>, +rest: String) -> {Wr.put_list.go(~Ds.At, ~Fds.put_at, xs, rest) == Wr.put_list.go(~Ds.At, ~DocSeen.seen.spell_at, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %ssp_ats_go(t, rest) : {Wr.put_list.step(~Ds.At, ~Fds.put_at, x, Wr.put_list.go(~Ds.At, ~Fds.put_at, t, rest)) == Wr.put_list.step(~Ds.At, ~DocSeen.seen.spell_at, x, _) : Nat & String}
      ssp_at_step(x, Wr.put_list.go(~Ds.At, ~Fds.put_at, t, rest))

# the anchors: the entry's list encoder is the spec's
def ssp_ats(xs: List<&2, Ds.At>, +rest: String) -> {Wr.put_list(~Ds.At, ~Fds.put_at, xs, rest) == DocSeen.seen.spell_ats(xs, rest) : String}:
  %ssp_ats_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Ds.At, ~Fds.put_at, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# ---- lines shown ----

def ssp_show_step(x: Ds.Show, r: Nat & String) -> {Wr.put_list.step(~Ds.Show, ~Fds.put_show, x, r) == Wr.put_list.step(~Ds.Show, ~DocSeen.seen.spell_show, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %ssp_show(x, s) : {(1n+n, Fds.put_show(x, s)) == (1n+n, _) : Nat & String}
      {==}

def ssp_shows_go(xs: List<&2, Ds.Show>, +rest: String) -> {Wr.put_list.go(~Ds.Show, ~Fds.put_show, xs, rest) == Wr.put_list.go(~Ds.Show, ~DocSeen.seen.spell_show, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %ssp_shows_go(t, rest) : {Wr.put_list.step(~Ds.Show, ~Fds.put_show, x, Wr.put_list.go(~Ds.Show, ~Fds.put_show, t, rest)) == Wr.put_list.step(~Ds.Show, ~DocSeen.seen.spell_show, x, _) : Nat & String}
      ssp_show_step(x, Wr.put_list.go(~Ds.Show, ~Fds.put_show, t, rest))

def ssp_shows(xs: List<&2, Ds.Show>, +rest: String) -> {Wr.put_list(~Ds.Show, ~Fds.put_show, xs, rest) == Wr.put_list(~Ds.Show, ~DocSeen.seen.spell_show, xs, rest) : String}:
  %ssp_shows_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Ds.Show, ~Fds.put_show, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# ---- requests and replies ----

# a request: the entry's encoder is the spec's
def ssp_req(+ivs: List<&2, Ds.Iv>, +ats: List<&2, Ds.At>, +rest: String) -> {Fds.put_req(ivs, ats, rest) == DocSeen.seen.spell_req(ivs, ats, rest) : String}:
  %ssp_ats(ats, rest) : {Wr.put_list(~Ds.Iv, ~Fds.put_iv, ivs, Wr.put_list(~Ds.At, ~Fds.put_at, ats, rest)) == DocSeen.seen.spell_seen(ivs, _) : String}
  ssp_ivs(ivs, Wr.put_list(~Ds.At, ~Fds.put_at, ats, rest))

# a verdict: the entry's encoder is the spec's
def ssp_check(c: Ds.Check) -> {Fds.put_check(c, "") == DocSeen.seen.spell_answer(c) : String}:
  match c:
    case Ds.Check{+u, +s, +w}:
      %ssp_shows(s, Wr.put_bool(w, "")) : {Wr.put_list(~Nat, ~Wr.put_nat, u, Wr.put_list(~Ds.Show, ~Fds.put_show, s, Wr.put_bool(w, ""))) == Wr.put_list(~Nat, ~Wr.put_nat, u, _) : String}
      {==}
