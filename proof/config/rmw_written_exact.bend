# eukhe: the proof of LAW rmw_written_exact
# The model's set and delete are the laws' restatements, entry by entry
# (inductions on the document); whether the key is there is the same test.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def pwx.pv(b: Bool, v: Nat, w: Nat) -> {Cf.pick_v(b, v, w) == Config.cf_put_v(b, v, w) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's replace is the laws'
def pwx.rep(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.replace(d, k, v) == Config.cf_replace(d, k, v) : List<&2, Cf.Entry>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+j, +w}:
          %pwx.pv(Nat.is_eq(j, k), v, w) : {Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> Cf.replace(t, k, v) == Cf.Entry{j, _} <> Config.cf_replace(t, k, v) : List<&2, Cf.Entry>}
          %pwx.rep(t, k, v) : {Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> Cf.replace(t, k, v) == Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> _ : List<&2, Cf.Entry>}
          {==}

# d has key k when its keys hold k
def pwx.has(d: List<&2, Cf.Entry>, +k: Nat) -> {Cf.has_key(d, k) == Config.cf_mem(Config.cf_keys(d), k) : Bool}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, v}:
          %pwx.has(rest, k) : {Bool.or(Nat.is_eq(j, k), Cf.has_key(rest, k)) == Bool.or(Nat.is_eq(j, k), _) : Bool}
          {==}

def pwx.del.step(b: Bool, +j: Nat, +w: Nat, r: List<&2, Cf.Entry>, x: List<&2, Cf.Entry>, ih: {r == x : List<&2, Cf.Entry>}) -> {Cf.keep(b, Cf.Entry{j, w}, r) == Config.cf_without.keep(b, Cf.Entry{j, w}, x) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      ih
    case False{}:
      %ih : {Cf.Entry{j, w} <> r == Cf.Entry{j, w} <> _ : List<&2, Cf.Entry>}
      {==}

# the model's delete is the laws'
def pwx.del(d: List<&2, Cf.Entry>, +k: Nat) -> {Cf.del(d, k) == Config.cf_without(d, k) : List<&2, Cf.Entry>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+j, w}:
          pwx.del.step(Nat.is_eq(j, k), j, w, Cf.del(t, k), Config.cf_without(t, k), pwx.del(t, k))

def pwx.set(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.set.go(b, d, k, v) == Config.cf_set_in(b, d, k, v) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      pwx.rep(d, k, v)
    case False{}:
      {==}

def Config.rmw_written_exact(d, e):
  match e:
    case Cf.Set{+k, +v}:
      %pwx.has(d, k) : {Cf.Wrote{Cf.set.go(Cf.has_key(d, k), d, k, v)} == Cf.Wrote{Config.cf_set_in(_, d, k, v)} : Cf.Write}
      %pwx.set(Cf.has_key(d, k), d, k, v) : {Cf.Wrote{Cf.set.go(Cf.has_key(d, k), d, k, v)} == Cf.Wrote{_} : Cf.Write}
      {==}
    case Cf.Del{+k}:
      %pwx.del(d, k) : {Cf.Wrote{Cf.del(d, k)} == Cf.Wrote{_} : Cf.Write}
      {==}
