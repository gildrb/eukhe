# eukhe: the segment's metrics (bend/autoresearch/stats.bend vals,
# top_scale, dlen; state.bend first, last) for the proof of LAW
# confidence_exact: they are the law's, well formed, at one scale, and the
# baseline and the best are among them

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/state.bend as ArS
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ../../../../laws/autoresearch/model.bend as Autoresearch
import ./nat.bend as CN
import ./zint.bend as CZ
import ./order.bend as CO

def ac.vals_at_eq(ok: Bool, m: Maybe<&2, ArD.Dec>, +r: List<&2, ArD.Dec>) -> {ArT.vals.at(ok, m, r) == Autoresearch.ar_vals.at(ok, m, r) : List<&2, ArD.Dec>}:
  match ok:
    case True{}:
      match m:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case False{}:
      {==}

# the code's metrics are the law's
def ac.vals_eq(rs: List<&2, ArS.Row>, +seg: Nat) -> {ArT.vals(rs, seg) == Autoresearch.ar_vals(rs, seg) : List<&2, ArD.Dec>}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, +sg, +st, +m, ms, ps, fn, +fl, desc} <> +t:
      +ok = Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(fl)))
      %ac.vals_eq(t, seg) : {ArT.vals.at(ok, m, ArT.vals(t, seg)) == Autoresearch.ar_vals.at(ok, m, _) : List<&2, ArD.Dec>}
      ac.vals_at_eq(ok, m, ArT.vals(t, seg))

def ac.dlen_eq(vs: List<&2, ArD.Dec>) -> {ArT.dlen(vs) == SS.len(vs) : Nat}:
  match vs:
    case Nil{}:
      {==}
    case v <> +t:
      %ac.dlen_eq(t) : {1n+ArT.dlen(t) == 1n+_ : Nat}
      {==}

def ac.top_eq(vs: List<&2, ArD.Dec>) -> {ArT.top_scale(vs) == SS.top(vs) : Nat}:
  match vs:
    case Nil{}:
      {==}
    case v <> +t:
      match v:
        case ArD.Dec{n, ds, +s}:
          %ac.top_eq(t) : {Nat.max(s, ArT.top_scale(t)) == Nat.max(s, _) : Nat}
          {==}

# Good metrics
# ------------

def ac.max_l(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      CN.ac.le_zero(Nat.max(0n, b))
    case 1n++p 0n:
      CN.ac.le_refl(p)
    case 1n++p 1n++q:
      ac.max_l(p, q)

def ac.max_r(a: Nat, b: Nat) -> {Nat.is_le(b, Nat.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n b:
      CN.ac.le_refl(b)
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      ac.max_r(p, q)

# the magnitude of d's integer at scale sc
def ac.zm(d: ArD.Dec, +sc: Nat) -> Nat:
  match d:
    case ArD.Dec{n, ds, s}:
      SD.shift(Nat.sub(sc, s), SD.num(ds))

def ac.ksum(vs: List<&2, ArD.Dec>, +sc: Nat) -> Nat:
  match vs:
    case Nil{}:
      0n
    case +v <> t:
      Nat.add(ac.zm(v, sc), ac.ksum(t, sc))

def ac.rng_b(b: Bool, +X: Nat, +K: Nat, +h: {Nat.is_le(X, K) == True{} : Bool}) -> {CZ.ac.rng(K, SS.Z{b, X}) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      {==}

def ac.allwf(vs: List<&2, ArD.Dec>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> t:
      Bool.and(SD.Wf(v), ac.allwf(t))

# well formed, below the top scale, magnitudes below their sum: good
def ac.mk_good(+K: Nat, +sc: Nat, vs: List<&2, ArD.Dec>, +hw: {ac.allwf(vs) == True{} : Bool}, +hs: {Nat.is_le(SS.top(vs), sc) == True{} : Bool}, +hk: {Nat.is_le(ac.ksum(vs, sc), K) == True{} : Bool}) -> {CO.ac.allgood(K, sc, vs) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case v <> +t:
      match v:
        case ArD.Dec{+n, +ds, +s}:
          +d = {ArD.Dec{n, ds, s} : ArD.Dec}
          +X = SD.shift(Nat.sub(sc, s), SD.num(ds))
          +ws = CN.ac.and_l(SD.Wf(d), ac.allwf(t), hw)
          +wt = CN.ac.and_r(SD.Wf(d), ac.allwf(t), hw)
          +ls = CN.ac.le_trans(s, Nat.max(s, SS.top(t)), sc, ac.max_l(s, SS.top(t)), hs)
          +lt = CN.ac.le_trans(SS.top(t), Nat.max(s, SS.top(t)), sc, ac.max_r(s, SS.top(t)), hs)
          +kx = CN.ac.le_trans(X, Nat.add(X, ac.ksum(t, sc)), K, CN.ac.le_add(X, ac.ksum(t, sc)), hk)
          +kt = CN.ac.le_trans(ac.ksum(t, sc), Nat.add(X, ac.ksum(t, sc)), K, CN.ac.le_add_l(X, ac.ksum(t, sc)), hk)
          +gd = CN.ac.and_i(SD.Wf(d), Bool.and(Nat.is_le(s, sc), CZ.ac.rng(K, SS.z(d, sc))), ws, CN.ac.and_i(Nat.is_le(s, sc), CZ.ac.rng(K, SS.z(d, sc)), ls, ac.rng_b(Bool.and(n, Nat.is_ne(SD.num(ds), 0n)), X, K, kx)))
          CN.ac.and_i(CO.ac.good(K, sc, d), CO.ac.allgood(K, sc, t), gd, ac.mk_good(K, sc, t, wt, lt, kt))

def ac.mwf_at(ok: Bool, m: Maybe<&2, ArD.Dec>, +r: List<&2, ArD.Dec>, +hm: {Autoresearch.ar_mwf(m) == True{} : Bool}, +hr: {ac.allwf(r) == True{} : Bool}) -> {ac.allwf(Autoresearch.ar_vals.at(ok, m, r)) == True{} : Bool}:
  match ok:
    case True{}:
      match m:
        case None{}:
          hr
        case Some{x}:
          CN.ac.and_i(SD.Wf(x), ac.allwf(r), hm, hr)
    case False{}:
      hr

# well-formed rows give well-formed metrics
def ac.vals_wf(rs: List<&2, ArS.Row>, +seg: Nat, +h: {Autoresearch.ar_rows_wf(rs) == True{} : Bool}) -> {ac.allwf(Autoresearch.ar_vals(rs, seg)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{i, +sg, +st, +m, ms, ps, fn, +fl, desc} <> +t:
      ac.mwf_at(Bool.and(Nat.is_eq(sg, seg), Bool.and(ArS.has(st), Bool.not(fl))), m, Autoresearch.ar_vals(t, seg), CN.ac.and_l(Autoresearch.ar_mwf(m), Autoresearch.ar_rows_wf(t), h), ac.vals_wf(t, seg, CN.ac.and_r(Autoresearch.ar_mwf(m), Autoresearch.ar_rows_wf(t), h)))

# Baseline and best
# -----------------

def ac.mgood(+K: Nat, +sc: Nat, m: Maybe<&2, ArD.Dec>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{d}:
      CO.ac.good(K, sc, d)

def ac.ag_tail(ok: Bool, m: Maybe<&2, ArD.Dec>, +r: List<&2, ArD.Dec>, +K: Nat, +sc: Nat, +h: {CO.ac.allgood(K, sc, Autoresearch.ar_vals.at(ok, m, r)) == True{} : Bool}) -> {CO.ac.allgood(K, sc, r) == True{} : Bool}:
  match ok:
    case True{}:
      match m:
        case None{}:
          h
        case Some{+x}:
          CN.ac.and_r(CO.ac.good(K, sc, x), CO.ac.allgood(K, sc, r), h)
    case False{}:
      h

# a kept metric of the segment is good
def ac.kept_good(e: Bool, st: Maybe<&2, ArS.Status>, fl: Bool, m: Maybe<&2, ArD.Dec>, +r: List<&2, ArD.Dec>, +K: Nat, +sc: Nat, +h: {CO.ac.allgood(K, sc, Autoresearch.ar_vals.at(Bool.and(e, Bool.and(ArS.has(st), Bool.not(fl))), m, r)) == True{} : Bool}) -> {ac.mgood(K, sc, ArS.kept.of(Bool.and(e, Bool.and(ArS.kept.st(st), Bool.not(fl))), m)) == True{} : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      match st:
        case None{}:
          {==}
        case Some{k}:
          match k:
            case ArS.Discard{}:
              {==}
            case ArS.Crash{}:
              {==}
            case ArS.Checks{}:
              {==}
            case ArS.Keep{}:
              match fl:
                case True{}:
                  {==}
                case False{}:
                  match m:
                    case None{}:
                      {==}
                    case Some{+x}:
                      CN.ac.and_l(CO.ac.good(K, sc, x), CO.ac.allgood(K, sc, r), h)

def ac.first_at(k: Maybe<&2, ArD.Dec>, +f: Maybe<&2, ArD.Dec>, +K: Nat, +sc: Nat, +hk: {ac.mgood(K, sc, k) == True{} : Bool}, +hf: {ac.mgood(K, sc, f) == True{} : Bool}) -> {ac.mgood(K, sc, ArS.first.at(k, f)) == True{} : Bool}:
  match k:
    case None{}:
      hf
    case Some{x}:
      hk

def ac.last_at(+k: Maybe<&2, ArD.Dec>, f: Maybe<&2, ArD.Dec>, +K: Nat, +sc: Nat, +hk: {ac.mgood(K, sc, k) == True{} : Bool}, +hf: {ac.mgood(K, sc, f) == True{} : Bool}) -> {ac.mgood(K, sc, ArS.last.at(k, f)) == True{} : Bool}:
  match f:
    case None{}:
      hk
    case Some{x}:
      hf

# the baseline is one of the metrics: good
def ac.first_good(rs: List<&2, ArS.Row>, +seg: Nat, +K: Nat, +sc: Nat, +h: {CO.ac.allgood(K, sc, Autoresearch.ar_vals(rs, seg)) == True{} : Bool}) -> {ac.mgood(K, sc, ArS.first(rs, seg)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{+i, +sg, +st, +m, +ms, +ps, +fn, +fl, +desc} <> +t:
      +e = Nat.is_eq(sg, seg)
      +V = Autoresearch.ar_vals(t, seg)
      ac.first_at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}, seg), ArS.first(t, seg), K, sc, ac.kept_good(e, st, fl, m, V, K, sc, h), ac.first_good(t, seg, K, sc, ac.ag_tail(Bool.and(e, Bool.and(ArS.has(st), Bool.not(fl))), m, V, K, sc, h)))

# the best is one of the metrics: good
def ac.last_good(rs: List<&2, ArS.Row>, +seg: Nat, +K: Nat, +sc: Nat, +h: {CO.ac.allgood(K, sc, Autoresearch.ar_vals(rs, seg)) == True{} : Bool}) -> {ac.mgood(K, sc, ArS.last(rs, seg)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case ArS.Row{+i, +sg, +st, +m, +ms, +ps, +fn, +fl, +desc} <> +t:
      +e = Nat.is_eq(sg, seg)
      +V = Autoresearch.ar_vals(t, seg)
      ac.last_at(ArS.kept(ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}, seg), ArS.last(t, seg), K, sc, ac.kept_good(e, st, fl, m, V, K, sc, h), ac.last_good(t, seg, K, sc, ac.ag_tail(Bool.and(e, Bool.and(ArS.has(st), Bool.not(fl))), m, V, K, sc, h)))
