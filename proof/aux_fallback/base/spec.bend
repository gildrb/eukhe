# eukhe: lemmas of area aux_fallback: the model's decision and a pass's
# events are the spec's (laws/aux_fallback.bend, afs_*), the entry's
# encoders write what the spec's spellers write and its decoders read
# what the spec's readers read, on every input.

import Base
import ../../../bend/aux_fallback.bend as Af
import ../../../bend/ffi_aux_fallback.bend as FAf
import ../../../bend/wire.bend as Wr
import ../../../laws/aux_fallback/model.bend as AuxFallback
import ../../../laws/aux_fallback/wire.bend as AuxFallbackWire
import ../fallback_window_fits.bend as PFits
import ../fallback_pass_events.bend as PEvents

# The model
# ---------

def pxe.gate(p: Nat, sel: Af.Sel, ok: Bool) -> {Af.gate(p, sel, ok) == AuxFallback.afs_gate(p, sel, ok) : Af.Gate}:
  match sel:
    case Af.Unset{}:
      {==}
    case Af.Same{}:
      {==}
    case Af.Other{s}:
      match ok:
        case True{}:
          {==}
        case False{}:
          {==}

def pxe.fits(+w: Nat, +need: Nat) -> {Af.fits(w, need) == AuxFallback.afs_fits(w, need) : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+x:
      PFits.paf.nlt_le(1n+x, need)

def pxe.hit(b: Bool, p: Nat, s: Nat) -> {Af.fits.route(b, p, s) == AuxFallback.afs_hit(b, p, s) : Af.Route}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pxe.settle(g: Af.Gate, look: Af.Look, +need: Nat) -> {Af.settle(g, look, need) == AuxFallback.afs_settle(g, look, need) : Af.Route}:
  match g:
    case Af.Known{r}:
      {==}
    case Af.Lookup{+p, +s}:
      match look:
        case Af.Miss{r}:
          {==}
        case Af.Hit{+w}:
          %pxe.fits(w, need) : {Af.fits.route(Af.fits(w, need), p, s) == AuxFallback.afs_hit(_, p, s) : Af.Route}
          pxe.hit(Af.fits(w, need), p, s)

def pxe.same(a: Af.Key, b: Af.Key) -> {Af.Key.eq(a, b) == AuxFallback.afs_same(a, b) : Bool}:
  match a b:
    case Af.K{ap, as1, ar} Af.K{bp, bs1, br}:
      {==}

def pxe.shown(sh: List<&2, Af.Key>, +k: Af.Key) -> {Af.listed(sh, k) == AuxFallback.afs_shown(sh, k) : Bool}:
  match sh:
    case Nil{}:
      {==}
    case +x <> +t:
      %pxe.same(x, k) : {Bool.or(Af.Key.eq(x, k), Af.listed(t, k)) == Bool.or(_, AuxFallback.afs_shown(t, k)) : Bool}
      %pxe.shown(t, k) : {Bool.or(Af.Key.eq(x, k), Af.listed(t, k)) == Bool.or(Af.Key.eq(x, k), _) : Bool}
      {==}

def pxe.noted(b: Bool, k: Af.Key) -> {Af.Sub{k} <> Af.noted(b, k, Nil{}) == AuxFallback.afs_noted(b, k) : List<&2, Af.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pxe.join(b: Bool, k: Af.Key, sh: List<&2, Af.Key>) -> {Af.shown(b, k, sh) == AuxFallback.afs_join(b, k, sh) : List<&2, Af.Key>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pxe.put(r: Af.Route, +sh: List<&2, Af.Key>) -> {Af.put(r, sh, Nil{}) == AuxFallback.afs_events(r, sh) : List<&2, Af.Ev>}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      %pxe.shown(sh, k) : {Af.Sub{k} <> Af.noted(Af.listed(sh, k), k, Nil{}) == AuxFallback.afs_noted(_, k) : List<&2, Af.Ev>}
      pxe.noted(Af.listed(sh, k), k)

def pxe.after(r: Af.Route, +sh: List<&2, Af.Key>) -> {Af.after(r, sh) == AuxFallback.afs_after(r, sh) : List<&2, Af.Key>}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      %pxe.shown(sh, k) : {Af.shown(Af.listed(sh, k), k, sh) == AuxFallback.afs_join(_, k, sh) : List<&2, Af.Key>}
      pxe.join(Af.listed(sh, k), k, sh)

# a pass's route is the spec's: its gate, then its settle
def pxe.decide(x: Af.Pass) -> {Af.decide(x) == AuxFallback.afs_route(x) : Af.Route}:
  match x:
    case Af.Pass{+p, +sel, +ok, +look, +need}:
      %pxe.gate(p, sel, ok) : {Af.settle(Af.gate(p, sel, ok), look, need) == AuxFallback.afs_settle(_, look, need) : Af.Route}
      pxe.settle(Af.gate(p, sel, ok), look, need)

# a session's events are the spec's fold: per pass, the route is the
# spec's (pxe.decide), its events then the rest (PEvents.paf.put), each
# step the spec's (pxe.put, pxe.after), the rest by induction
def pxe.session(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>) -> {Af.go(ps, sh) == AuxFallback.afs_go(ps, sh) : List<&2, Af.Ev>}:
  match ps:
    case Nil{}:
      {==}
    case +x <> +rest:
      %pxe.decide(x) : {Af.put(Af.decide(x), sh, Af.go(rest, Af.after(Af.decide(x), sh))) == List.append(&2, Af.Ev, AuxFallback.afs_events(_, sh), AuxFallback.afs_go(rest, AuxFallback.afs_after(_, sh))) : List<&2, Af.Ev>}
      %pxe.session(rest, AuxFallback.afs_after(Af.decide(x), sh)) : {Af.put(Af.decide(x), sh, Af.go(rest, Af.after(Af.decide(x), sh))) == List.append(&2, Af.Ev, AuxFallback.afs_events(Af.decide(x), sh), _) : List<&2, Af.Ev>}
      %pxe.after(Af.decide(x), sh) : {Af.put(Af.decide(x), sh, Af.go(rest, Af.after(Af.decide(x), sh))) == List.append(&2, Af.Ev, AuxFallback.afs_events(Af.decide(x), sh), Af.go(rest, _)) : List<&2, Af.Ev>}
      %pxe.put(Af.decide(x), sh) : {Af.put(Af.decide(x), sh, Af.go(rest, Af.after(Af.decide(x), sh))) == List.append(&2, Af.Ev, _, Af.go(rest, Af.after(Af.decide(x), sh))) : List<&2, Af.Ev>}
      PEvents.paf.put(Af.decide(x), sh, Af.go(rest, Af.after(Af.decide(x), sh)))

# Encoders
# --------

def pxe.put_key(k: Af.Key, rest: String) -> {FAf.put_key(k, rest) == AuxFallbackWire.afs_spell_key(k, rest) : String}:
  match k:
    case Af.K{p, s, r}:
      {==}

def pxe.put_route(r: Af.Route, rest: String) -> {FAf.put_route(r, rest) == AuxFallbackWire.afs_spell_route(r, rest) : String}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{k}:
      match k:
        case Af.K{p, s, x}:
          {==}

def pxe.put_gate(g: Af.Gate, rest: String) -> {FAf.put_gate(g, rest) == AuxFallbackWire.afs_spell_gate(g, rest) : String}:
  match g:
    case Af.Known{+r}:
      %pxe.put_route(r, rest) : {Wr.put_nat(0n, FAf.put_route(r, rest)) == Wr.put_nat(0n, _) : String}
      {==}
    case Af.Lookup{p, s}:
      {==}

def pxe.put_ev(e: Af.Ev, rest: String) -> {FAf.put_ev(e, rest) == AuxFallbackWire.afs_spell_ev(e, rest) : String}:
  match e:
    case Af.Stay{}:
      {==}
    case Af.Went{}:
      {==}
    case Af.Sub{k}:
      match k:
        case Af.K{p, s, r}:
          {==}
    case Af.Note{k}:
      match k:
        case Af.K{p, s, r}:
          {==}

def pxe.put_sel(x: Af.Sel, rest: String) -> {FAf.put_sel(x, rest) == AuxFallbackWire.afs_spell_sel(x, rest) : String}:
  match x:
    case Af.Unset{}:
      {==}
    case Af.Same{}:
      {==}
    case Af.Other{s}:
      {==}

def pxe.put_look(x: Af.Look, rest: String) -> {FAf.put_look(x, rest) == AuxFallbackWire.afs_spell_look(x, rest) : String}:
  match x:
    case Af.Miss{r}:
      {==}
    case Af.Hit{w}:
      {==}

def pxe.keys_step(+x: Af.Key, r: Nat & String) -> {Wr.put_list.step(~Af.Key, ~FAf.put_key, x, r) == Wr.put_list.step(~Af.Key, ~AuxFallbackWire.afs_spell_key, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %pxe.put_key(x, s) : {(1n+n, FAf.put_key(x, s)) == (1n+n, _) : Nat & String}
      {==}

def pxe.keys_go(xs: List<&2, Af.Key>, +rest: String) -> {Wr.put_list.go(~Af.Key, ~FAf.put_key, xs, rest) == Wr.put_list.go(~Af.Key, ~AuxFallbackWire.afs_spell_key, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pxe.keys_go(t, rest) : {Wr.put_list.step(~Af.Key, ~FAf.put_key, x, Wr.put_list.go(~Af.Key, ~FAf.put_key, t, rest)) == Wr.put_list.step(~Af.Key, ~AuxFallbackWire.afs_spell_key, x, _) : Nat & String}
      pxe.keys_step(x, Wr.put_list.go(~Af.Key, ~FAf.put_key, t, rest))

def pxe.put_keys(xs: List<&2, Af.Key>, +rest: String) -> {Wr.put_list(~Af.Key, ~FAf.put_key, xs, rest) == Wr.put_list(~Af.Key, ~AuxFallbackWire.afs_spell_key, xs, rest) : String}:
  %pxe.keys_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Af.Key, ~FAf.put_key, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def pxe.evs_step(+x: Af.Ev, r: Nat & String) -> {Wr.put_list.step(~Af.Ev, ~FAf.put_ev, x, r) == Wr.put_list.step(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %pxe.put_ev(x, s) : {(1n+n, FAf.put_ev(x, s)) == (1n+n, _) : Nat & String}
      {==}

def pxe.evs_go(xs: List<&2, Af.Ev>, +rest: String) -> {Wr.put_list.go(~Af.Ev, ~FAf.put_ev, xs, rest) == Wr.put_list.go(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pxe.evs_go(t, rest) : {Wr.put_list.step(~Af.Ev, ~FAf.put_ev, x, Wr.put_list.go(~Af.Ev, ~FAf.put_ev, t, rest)) == Wr.put_list.step(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, x, _) : Nat & String}
      pxe.evs_step(x, Wr.put_list.go(~Af.Ev, ~FAf.put_ev, t, rest))

def pxe.put_evs(xs: List<&2, Af.Ev>, +rest: String) -> {Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest) == Wr.put_list(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, xs, rest) : String}:
  %pxe.evs_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Af.Ev, ~FAf.put_ev, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def pxe.put_req(x: FAf.Req, +rest: String) -> {FAf.put_req(x, rest) == AuxFallbackWire.afs_spell_req(x, rest) : String}:
  match x:
    case FAf.GateReq{+p, +sel, +ok}:
      %pxe.put_sel(sel, Wr.put_bool(ok, rest)) : {Wr.put_nat(0n, Wr.put_nat(p, FAf.put_sel(sel, Wr.put_bool(ok, rest)))) == Wr.put_nat(0n, Wr.put_nat(p, _)) : String}
      {==}
    case FAf.SettleReq{+g, +look, +need}:
      %pxe.put_look(look, Wr.put_nat(need, rest)) : {Wr.put_nat(1n, FAf.put_gate(g, FAf.put_look(look, Wr.put_nat(need, rest)))) == Wr.put_nat(1n, AuxFallbackWire.afs_spell_gate(g, _)) : String}
      %pxe.put_gate(g, FAf.put_look(look, Wr.put_nat(need, rest))) : {Wr.put_nat(1n, FAf.put_gate(g, FAf.put_look(look, Wr.put_nat(need, rest)))) == Wr.put_nat(1n, _) : String}
      {==}
    case FAf.PassReq{+r, +sh}:
      %pxe.put_keys(sh, rest) : {Wr.put_nat(2n, FAf.put_route(r, Wr.put_list(~Af.Key, ~FAf.put_key, sh, rest))) == Wr.put_nat(2n, AuxFallbackWire.afs_spell_route(r, _)) : String}
      %pxe.put_route(r, Wr.put_list(~Af.Key, ~FAf.put_key, sh, rest)) : {Wr.put_nat(2n, FAf.put_route(r, Wr.put_list(~Af.Key, ~FAf.put_key, sh, rest))) == Wr.put_nat(2n, _) : String}
      {==}

# the entry's answer to a request is the spec's reply
def pxe.answer(x: FAf.Req) -> {FAf.answer(x) == AuxFallbackWire.afs_reply(x) : String}:
  match x:
    case FAf.GateReq{+p, +sel, +ok}:
      %pxe.gate(p, sel, ok) : {FAf.put_gate(Af.gate(p, sel, ok), "") == AuxFallbackWire.afs_spell_gate(_, "") : String}
      pxe.put_gate(Af.gate(p, sel, ok), "")
    case FAf.SettleReq{+g, +look, +need}:
      %pxe.settle(g, look, need) : {FAf.put_route(Af.settle(g, look, need), "") == AuxFallbackWire.afs_spell_route(_, "") : String}
      pxe.put_route(Af.settle(g, look, need), "")
    case FAf.PassReq{+r, +sh}:
      +es = Af.put(r, sh, Nil{})
      +ks = Af.after(r, sh)
      %pxe.put(r, sh) : {Wr.put_list(~Af.Ev, ~FAf.put_ev, es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, "")) == Wr.put_list(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, _, Wr.put_list(~Af.Key, ~AuxFallbackWire.afs_spell_key, AuxFallback.afs_after(r, sh), "")) : String}
      %pxe.after(r, sh) : {Wr.put_list(~Af.Ev, ~FAf.put_ev, es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, "")) == Wr.put_list(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, es, Wr.put_list(~Af.Key, ~AuxFallbackWire.afs_spell_key, _, "")) : String}
      %pxe.put_keys(ks, "") : {Wr.put_list(~Af.Ev, ~FAf.put_ev, es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, "")) == Wr.put_list(~Af.Ev, ~AuxFallbackWire.afs_spell_ev, es, _) : String}
      pxe.put_evs(es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, ""))

# Decoders
# --------

def pxe.key_r(p: Nat, s: Nat, d: Wr.Dec<Nat>) -> {FAf.get_key.r(p, s, d) == AuxFallbackWire.afs_read_key.r(p, s, d) : Wr.Dec<Af.Key>}:
  match d:
    case Wr.Got{r, rest}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.key_s(p: Nat, d: Wr.Dec<Nat>) -> {FAf.get_key.s(p, d) == AuxFallbackWire.afs_read_key.s(p, d) : Wr.Dec<Af.Key>}:
  match d:
    case Wr.Got{s, rest}:
      pxe.key_r(p, s, Wr.get_nat(rest))
    case Wr.Bad{}:
      {==}

def pxe.key_p(d: Wr.Dec<Nat>) -> {FAf.get_key.go(d) == AuxFallbackWire.afs_read_key.p(d) : Wr.Dec<Af.Key>}:
  match d:
    case Wr.Got{p, rest}:
      pxe.key_s(p, Wr.get_nat(rest))
    case Wr.Bad{}:
      {==}

def pxe.key(s: String) -> {FAf.get_key(s) == AuxFallbackWire.afs_read_key(s) : Wr.Dec<Af.Key>}:
  pxe.key_p(Wr.get_nat(s))

def pxe.keys_lgo(n: Nat, cur: Wr.Dec<Af.Key>) -> {Wr.get_list.go(~Af.Key, ~FAf.get_key, n, cur) == Wr.get_list.go(~Af.Key, ~AuxFallbackWire.afs_read_key, n, cur) : Wr.Dec<List<&2, Af.Key>>}:
  match n cur:
    case 0n Wr.Got{x, s}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+m Wr.Got{x, +s}:
      %pxe.key(s) : {Wr.get_list.cons(Af.Key, x, Wr.get_list.go(~Af.Key, ~FAf.get_key, m, FAf.get_key(s))) == Wr.get_list.cons(Af.Key, x, Wr.get_list.go(~Af.Key, ~AuxFallbackWire.afs_read_key, m, _)) : Wr.Dec<List<&2, Af.Key>>}
      %pxe.keys_lgo(m, FAf.get_key(s)) : {Wr.get_list.cons(Af.Key, x, Wr.get_list.go(~Af.Key, ~FAf.get_key, m, FAf.get_key(s))) == Wr.get_list.cons(Af.Key, x, _) : Wr.Dec<List<&2, Af.Key>>}
      {==}
    case 1n+m Wr.Bad{}:
      {==}

def pxe.keys_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Af.Key, ~FAf.get_key, r) == Wr.get_list.start(~Af.Key, ~AuxFallbackWire.afs_read_key, r) : Wr.Dec<List<&2, Af.Key>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %pxe.key(s) : {Wr.get_list.go(~Af.Key, ~FAf.get_key, m, FAf.get_key(s)) == Wr.get_list.go(~Af.Key, ~AuxFallbackWire.afs_read_key, m, _) : Wr.Dec<List<&2, Af.Key>>}
          pxe.keys_lgo(m, FAf.get_key(s))
    case Wr.Bad{}:
      {==}

def pxe.keys(s: String) -> {Wr.get_list(~Af.Key, ~FAf.get_key, s) == Wr.get_list(~Af.Key, ~AuxFallbackWire.afs_read_key, s) : Wr.Dec<List<&2, Af.Key>>}:
  pxe.keys_start(Wr.get_nat(s))

def pxe.route_key(d: Wr.Dec<Af.Key>) -> {FAf.get_route.fallback(d) == AuxFallbackWire.afs_read_route.key(d) : Wr.Dec<Af.Route>}:
  match d:
    case Wr.Got{k, rest}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.route_tag(n: Nat, +s: String) -> {FAf.get_route.tag(n, s) == AuxFallbackWire.afs_read_route.tag(n, s) : Wr.Dec<Af.Route>}:
  match n:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              %pxe.key(s) : {FAf.get_route.fallback(FAf.get_key(s)) == AuxFallbackWire.afs_read_route.key(_) : Wr.Dec<Af.Route>}
              pxe.route_key(FAf.get_key(s))
            case 1n+c:
              {==}

def pxe.route_go(d: Wr.Dec<Nat>) -> {FAf.get_route.go(d) == AuxFallbackWire.afs_read_route.go(d) : Wr.Dec<Af.Route>}:
  match d:
    case Wr.Got{n, s}:
      pxe.route_tag(n, s)
    case Wr.Bad{}:
      {==}

def pxe.route(s: String) -> {FAf.get_route(s) == AuxFallbackWire.afs_read_route(s) : Wr.Dec<Af.Route>}:
  pxe.route_go(Wr.get_nat(s))

def pxe.gate_known(d: Wr.Dec<Af.Route>) -> {FAf.get_gate.known(d) == AuxFallbackWire.afs_read_gate.known(d) : Wr.Dec<Af.Gate>}:
  match d:
    case Wr.Got{r, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.gate_s(p: Nat, d: Wr.Dec<Nat>) -> {FAf.get_gate.s(p, d) == AuxFallbackWire.afs_read_gate.s(p, d) : Wr.Dec<Af.Gate>}:
  match d:
    case Wr.Got{s, rest}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.gate_p(d: Wr.Dec<Nat>) -> {FAf.get_gate.p(d) == AuxFallbackWire.afs_read_gate.p(d) : Wr.Dec<Af.Gate>}:
  match d:
    case Wr.Got{p, rest}:
      pxe.gate_s(p, Wr.get_nat(rest))
    case Wr.Bad{}:
      {==}

def pxe.gate_tag(n: Nat, +s: String) -> {FAf.get_gate.tag(n, s) == AuxFallbackWire.afs_read_gate.tag(n, s) : Wr.Dec<Af.Gate>}:
  match n:
    case 0n:
      %pxe.route(s) : {FAf.get_gate.known(FAf.get_route(s)) == AuxFallbackWire.afs_read_gate.known(_) : Wr.Dec<Af.Gate>}
      pxe.gate_known(FAf.get_route(s))
    case 1n+a:
      match a:
        case 0n:
          pxe.gate_p(Wr.get_nat(s))
        case 1n+b:
          {==}

def pxe.gate_go(d: Wr.Dec<Nat>) -> {FAf.get_gate.go(d) == AuxFallbackWire.afs_read_gate.go(d) : Wr.Dec<Af.Gate>}:
  match d:
    case Wr.Got{n, s}:
      pxe.gate_tag(n, s)
    case Wr.Bad{}:
      {==}

def pxe.gate_r(s: String) -> {FAf.get_gate(s) == AuxFallbackWire.afs_read_gate(s) : Wr.Dec<Af.Gate>}:
  pxe.gate_go(Wr.get_nat(s))

def pxe.sel_other(d: Wr.Dec<Nat>) -> {FAf.get_sel.other(d) == AuxFallbackWire.afs_read_sel.other(d) : Wr.Dec<Af.Sel>}:
  match d:
    case Wr.Got{s, rest}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.sel_tag(n: Nat, +s: String) -> {FAf.get_sel.tag(n, s) == AuxFallbackWire.afs_read_sel.tag(n, s) : Wr.Dec<Af.Sel>}:
  match n:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              pxe.sel_other(Wr.get_nat(s))
            case 1n+c:
              {==}

def pxe.sel_go(d: Wr.Dec<Nat>) -> {FAf.get_sel.go(d) == AuxFallbackWire.afs_read_sel.go(d) : Wr.Dec<Af.Sel>}:
  match d:
    case Wr.Got{n, s}:
      pxe.sel_tag(n, s)
    case Wr.Bad{}:
      {==}

def pxe.look_miss(d: Wr.Dec<Nat>) -> {FAf.get_look.tag(d, 0n) == AuxFallbackWire.afs_read_miss(d) : Wr.Dec<Af.Look>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.look_hit(d: Wr.Dec<Nat>) -> {FAf.get_look.tag(d, 1n) == AuxFallbackWire.afs_read_hit(d) : Wr.Dec<Af.Look>}:
  match d:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.look_go(d: Wr.Dec<Nat>) -> {FAf.get_look.go(d) == AuxFallbackWire.afs_read_look.go(d) : Wr.Dec<Af.Look>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          pxe.look_miss(Wr.get_nat(s))
        case 1n+a:
          match a:
            case 0n:
              pxe.look_hit(Wr.get_nat(s))
            case 1n+b:
              {==}
    case Wr.Bad{}:
      {==}

def pxe.gq_ok(p: Nat, sel: Af.Sel, d: Wr.Dec<Bool>) -> {FAf.get_req.ok(p, sel, d) == AuxFallbackWire.afs_read_gq.ok(p, sel, d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{ok, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.gq_sel(p: Nat, d: Wr.Dec<Af.Sel>) -> {FAf.get_req.sel(p, d) == AuxFallbackWire.afs_read_gq.sel(p, d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{sel, s}:
      pxe.gq_ok(p, sel, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def pxe.gq(d: Wr.Dec<Nat>) -> {FAf.get_req.gate(d) == AuxFallbackWire.afs_read_gq(d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{+p, +s}:
      %pxe.sel_go(Wr.get_nat(s)) : {FAf.get_req.sel(p, FAf.get_sel.go(Wr.get_nat(s))) == AuxFallbackWire.afs_read_gq.sel(p, _) : Wr.Dec<FAf.Req>}
      pxe.gq_sel(p, FAf.get_sel.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pxe.sq_need(g: Af.Gate, look: Af.Look, d: Wr.Dec<Nat>) -> {FAf.get_req.need(g, look, d) == AuxFallbackWire.afs_read_sq.need(g, look, d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{need, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.sq_look(g: Af.Gate, d: Wr.Dec<Af.Look>) -> {FAf.get_req.look(g, d) == AuxFallbackWire.afs_read_sq.look(g, d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{look, s}:
      pxe.sq_need(g, look, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pxe.sq(d: Wr.Dec<Af.Gate>) -> {FAf.get_req.settle(d) == AuxFallbackWire.afs_read_sq(d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{+g, +s}:
      %pxe.look_go(Wr.get_nat(s)) : {FAf.get_req.look(g, FAf.get_look.go(Wr.get_nat(s))) == AuxFallbackWire.afs_read_sq.look(g, _) : Wr.Dec<FAf.Req>}
      pxe.sq_look(g, FAf.get_look.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pxe.pq_shown(r: Af.Route, d: Wr.Dec<List<&2, Af.Key>>) -> {FAf.get_req.shown(r, d) == AuxFallbackWire.afs_read_pq.shown(r, d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{sh, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pxe.pq(d: Wr.Dec<Af.Route>) -> {FAf.get_req.pass(d) == AuxFallbackWire.afs_read_pq(d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{+r, +s}:
      %pxe.keys(s) : {FAf.get_req.shown(r, Wr.get_list(~Af.Key, ~FAf.get_key, s)) == AuxFallbackWire.afs_read_pq.shown(r, _) : Wr.Dec<FAf.Req>}
      pxe.pq_shown(r, Wr.get_list(~Af.Key, ~FAf.get_key, s))
    case Wr.Bad{}:
      {==}

def pxe.req_tag(n: Nat, +s: String) -> {FAf.get_req.tag(n, s) == AuxFallbackWire.afs_read_req.tag(n, s) : Wr.Dec<FAf.Req>}:
  match n:
    case 0n:
      pxe.gq(Wr.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          %pxe.gate_r(s) : {FAf.get_req.settle(FAf.get_gate(s)) == AuxFallbackWire.afs_read_sq(_) : Wr.Dec<FAf.Req>}
          pxe.sq(FAf.get_gate(s))
        case 1n+b:
          match b:
            case 0n:
              %pxe.route(s) : {FAf.get_req.pass(FAf.get_route(s)) == AuxFallbackWire.afs_read_pq(_) : Wr.Dec<FAf.Req>}
              pxe.pq(FAf.get_route(s))
            case 1n+c:
              {==}

def pxe.req_go(d: Wr.Dec<Nat>) -> {FAf.get_req.go(d) == AuxFallbackWire.afs_read_req.go(d) : Wr.Dec<FAf.Req>}:
  match d:
    case Wr.Got{n, s}:
      pxe.req_tag(n, s)
    case Wr.Bad{}:
      {==}

def pxe.req(s: String) -> {FAf.get_req(s) == AuxFallbackWire.afs_read_req(s) : Wr.Dec<FAf.Req>}:
  pxe.req_go(Wr.get_nat(s))

# The entry
# ---------

def pxe.end(b: Bool, x: FAf.Req) -> {FAf.ffi.end(b, x) == AuxFallbackWire.afs_entry.end(b, x) : String}:
  match b:
    case True{}:
      pxe.answer(x)
    case False{}:
      {==}

def pxe.go(d: Wr.Dec<FAf.Req>) -> {FAf.ffi.go(d) == AuxFallbackWire.afs_entry.go(d) : String}:
  match d:
    case Wr.Got{x, s}:
      pxe.end(Wr.end(s), x)
    case Wr.Bad{}:
      {==}

# the entry is the spec's entry, on every input
def pxe.ffi(+s: String) -> {FAf.ffi(s) == AuxFallbackWire.afs_entry(s) : String}:
  %pxe.req(s) : {FAf.ffi.go(FAf.get_req(s)) == AuxFallbackWire.afs_entry.go(_) : String}
  pxe.go(FAf.get_req(s))
