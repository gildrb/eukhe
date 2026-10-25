# eukhe: the proof of LAW rmw_keeps_place
# A set of a key the document has replaces values in place (the keys do
# not move); a set of a new key appends it; a delete drops its entries.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

# the keys of d hold k when d has an entry of k
def pkp.has(d: List<&2, Cf.Entry>, +k: Nat) -> {Cf.has_key(d, k) == Config.cf_mem(Config.cf_keys(d), k) : Bool}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, v}:
          %pkp.has(rest, k) : {Bool.or(Nat.is_eq(j, k), Cf.has_key(rest, k)) == Bool.or(Nat.is_eq(j, k), _) : Bool}
          {==}

# a replace keeps every key in its place
def pkp.rep(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Config.cf_keys(Cf.replace(d, k, v)) == Config.cf_keys(d) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, w}:
          %pkp.rep(rest, k, v) : {j <> Config.cf_keys(Cf.replace(rest, k, v)) == j <> _ : List<&2, Nat>}
          {==}

# an entry put last puts its key last
def pkp.app(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Config.cf_keys(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}])) == List.append(&2, Nat, Config.cf_keys(d), [k]) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, w}:
          %pkp.app(rest, k, v) : {j <> Config.cf_keys(List.append(&2, Cf.Entry, rest, [Cf.Entry{k, v}])) == j <> _ : List<&2, Nat>}
          {==}

def pkp.del.step(b: Bool, j: Nat, v: Nat, r: List<&2, Cf.Entry>, dr: List<&2, Nat>, ih: {Config.cf_keys(r) == dr : List<&2, Nat>}) -> {Config.cf_keys(Cf.keep(b, Cf.Entry{j, v}, r)) == Config.cf_drop.keep(b, j, dr) : List<&2, Nat>}:
  match b:
    case True{}:
      ih
    case False{}:
      %ih : {j <> Config.cf_keys(r) == j <> _ : List<&2, Nat>}
      {==}

# a delete drops only its key
def pkp.del(d: List<&2, Cf.Entry>, +k: Nat) -> {Config.cf_keys(Cf.del(d, k)) == Config.cf_drop(Config.cf_keys(d), k) : List<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, v}:
          pkp.del.step(Nat.is_eq(j, k), j, v, Cf.del(rest, k), Config.cf_drop(Config.cf_keys(rest), k), pkp.del(rest, k))

def pkp.set(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Config.cf_keys(Cf.set.go(b, d, k, v)) == Config.cf_keys_set(b, Config.cf_keys(d), k) : List<&2, Nat>}:
  match b:
    case True{}:
      pkp.rep(d, k, v)
    case False{}:
      pkp.app(d, k, v)

def Config.rmw_keeps_place(d, e):
  match e:
    case Cf.Set{+k, +v}:
      %pkp.has(d, k) : {Some{Config.cf_keys(Cf.set.go(Cf.has_key(d, k), d, k, v))} == Some{Config.cf_keys_set(_, Config.cf_keys(d), k)} : Maybe<&2, List<&2, Nat>>}
      %pkp.set(Cf.has_key(d, k), d, k, v) : {Some{Config.cf_keys(Cf.set.go(Cf.has_key(d, k), d, k, v))} == Some{_} : Maybe<&2, List<&2, Nat>>}
      {==}
    case Cf.Del{+k}:
      %pkp.del(d, k) : {Some{Config.cf_keys(Cf.del(d, k))} == Some{_} : Maybe<&2, List<&2, Nat>>}
      {==}
