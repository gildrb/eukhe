# eukhe: the proof of LAW trust_withheld_exact
# Key by key, from any warning so far: a key that applies adds nothing, a
# withheld one adds its rule's name unless named before (an induction on
# the keys, over every warning so far).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ./base/config.bend as LA

def pwe.seen(ns: List<&2, String>, +n: String) -> {Cf.named(ns, n) == Config.cf_seen(ns, n) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +x <> +rest:
      %pwe.seen(rest, n) : {Bool.or(String.eq(x, n), Cf.named(rest, n)) == Bool.or(String.eq(x, n), _) : Bool}
      {==}

def pwe.put(b: Bool, n: String, acc: List<&2, String>) -> {Cf.withheld.put(b, n, acc) == Config.cf_once.add(b, n, acc) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pwe.add(b: Bool, +t: Cf.Trust, rest: List<&2, Cf.PKey>, +n: String, +acc: List<&2, String>, ns: List<&2, String>, ih: @a: List<&2, String> -> {Cf.withheld.go(t, rest, a) == Config.cf_once(ns, a) : List<&2, String>}) -> {Cf.withheld.go(t, rest, Cf.withheld.add(b, n, acc)) == Config.cf_once(Config.cf_names.put(b, n, ns), acc) : List<&2, String>}:
  match b:
    case True{}:
      ih(acc)
    case False{}:
      %pwe.seen(acc, n) : {Cf.withheld.go(t, rest, Cf.withheld.put(Cf.named(acc, n), n, acc)) == Config.cf_once(ns, Config.cf_once.add(_, n, acc)) : List<&2, String>}
      %pwe.put(Cf.named(acc, n), n, acc) : {Cf.withheld.go(t, rest, Cf.withheld.put(Cf.named(acc, n), n, acc)) == Config.cf_once(ns, _) : List<&2, String>}
      ih(Cf.withheld.put(Cf.named(acc, n), n, acc))

def pwe.hit(+t: Cf.Trust, h: Cf.Hit, rest: List<&2, Cf.PKey>, +acc: List<&2, String>, ns: List<&2, String>, ih: @a: List<&2, String> -> {Cf.withheld.go(t, rest, a) == Config.cf_once(ns, a) : List<&2, String>}) -> {Cf.withheld.go(t, rest, Cf.withheld.step(t, h, acc)) == Config.cf_once(Config.cf_names.hit(t, h, ns), acc) : List<&2, String>}:
  match h:
    case Cf.Hit{+n, +s}:
      %LA.pcf.applies(t, s) : {Cf.withheld.go(t, rest, Cf.withheld.add(Cf.applies(t, s), n, acc)) == Config.cf_once(Config.cf_names.put(_, n, ns), acc) : List<&2, String>}
      pwe.add(Cf.applies(t, s), t, rest, n, acc, ns, ih)

# the warning so far is acc: the names follow, each once
def pwe.go(+t: Cf.Trust, ks: List<&2, Cf.PKey>, +acc: List<&2, String>) -> {Cf.withheld.go(t, ks, acc) == Config.cf_once(Config.cf_names(t, ks), acc) : List<&2, String>}:
  match ks:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.PKey{k, +p, v}:
          %LA.pcf.classify(p) : {Cf.withheld.go(t, rest, Cf.withheld.step(t, Cf.classify(p), acc)) == Config.cf_once(Config.cf_names.hit(t, _, Config.cf_names(t, rest)), acc) : List<&2, String>}
          pwe.hit(t, Cf.classify(p), rest, acc, Config.cf_names(t, rest), a => pwe.go(t, rest, a))

def Config.trust_withheld_exact(t, ks):
  pwe.go(t, ks, Nil{})
