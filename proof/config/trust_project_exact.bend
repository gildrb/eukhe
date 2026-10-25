# eukhe: the proof of LAW trust_project_exact
# Key by key: each key's scope is the laws' (trust_classify_exact), and
# its item applies exactly when the laws say (an induction on the keys).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def ptp.guard(b: Bool, k: Nat, v: Nat, x: List<&2, Cf.Entry>, +r: List<&2, Cf.Entry>, ih: {x == r : List<&2, Cf.Entry>}) -> {Cf.guard(b, Cf.Entry{k, v}, x) == Config.cf_project.put(b, k, v, r) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      %ih : {Cf.Entry{k, v} <> x == Cf.Entry{k, v} <> _ : List<&2, Cf.Entry>}
      {==}
    case False{}:
      ih

def ptp.scope(+t: Cf.Trust, +g: List<&2, Cf.Entry>, s: Cf.Scope, +k: Nat, +v: Nat, +its: List<&2, Cf.Item>, +r: List<&2, Cf.Entry>, ih: {Cf.effective(t, g, its) == r : List<&2, Cf.Entry>}) -> {Cf.effective(t, g, Cf.item.of(s, k, v, its)) == Config.cf_project.put(Config.cf_applies(t, s), k, v, r) : List<&2, Cf.Entry>}:
  match s:
    case Cf.Proj{+c}:
      %LA.pcf.applies(t, Cf.Proj{c}) : {Cf.guard(Cf.admits(t, c), Cf.Entry{k, v}, Cf.effective(t, g, its)) == Config.cf_project.put(_, k, v, r) : List<&2, Cf.Entry>}
      ptp.guard(Cf.admits(t, c), k, v, Cf.effective(t, g, its), r, ih)
    case Cf.GlobalOnly{}:
      %LA.pcf.applies(t, Cf.GlobalOnly{}) : {Cf.effective(t, g, its) == Config.cf_project.put(_, k, v, r) : List<&2, Cf.Entry>}
      ih

def ptp.hit(+t: Cf.Trust, +g: List<&2, Cf.Entry>, h: Cf.Hit, +k: Nat, +v: Nat, +its: List<&2, Cf.Item>, +r: List<&2, Cf.Entry>, ih: {Cf.effective(t, g, its) == r : List<&2, Cf.Entry>}) -> {Cf.effective(t, g, Cf.item.of(Cf.Hit.scope(h), k, v, its)) == Config.cf_project.put(Config.cf_applies(t, Config.cf_scope(h)), k, v, r) : List<&2, Cf.Entry>}:
  match h:
    case Cf.Hit{n, s}:
      ptp.scope(t, g, s, k, v, its, r, ih)

def ptp.go(+t: Cf.Trust, +g: List<&2, Cf.Entry>, ks: List<&2, Cf.PKey>) -> {Cf.project(t, g, ks) == Config.cf_project(t, g, ks) : List<&2, Cf.Entry>}:
  match ks:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.PKey{k, +p, v}:
          %LA.pcf.classify(p) : {Cf.effective(t, g, Cf.item.of(Cf.Hit.scope(Cf.classify(p)), k, v, Cf.items(rest))) == Config.cf_project.put(Config.cf_applies(t, Config.cf_scope(_)), k, v, Config.cf_project(t, g, rest)) : List<&2, Cf.Entry>}
          ptp.hit(t, g, Cf.classify(p), k, v, Cf.items(rest), Config.cf_project(t, g, rest), ptp.go(t, g, rest))

def Config.trust_project_exact(t, g, ks):
  +h = g
  ptp.go(t, h, ks)
