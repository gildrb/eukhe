# eukhe: the proof of LAW trust_withheld_step
# The warning is built key by key over an accumulator: a key's step adds
# its name when it does not apply and the accumulator lacks it, which is
# what adding the warning of that key alone does.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

# the steps of xs, then those of ys, are the steps of xs then ys
def ptw.go_app(+t: Cf.Trust, xs: List<&2, Cf.PKey>, +ys: List<&2, Cf.PKey>, acc: List<&2, String>) -> {Cf.withheld.go(t, ys, Cf.withheld.go(t, xs, acc)) == Cf.withheld.go(t, List.append(&2, Cf.PKey, xs, ys), acc) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match x:
        case Cf.PKey{k, +p, v}:
          ptw.go_app(t, rest, ys, Cf.withheld.step(t, Cf.classify(p), acc))

# the model's membership is the laws'
def ptw.seen(ns: List<&2, String>, +n: String) -> {Cf.named(ns, n) == Config.cf_seen(ns, n) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +x <> t:
      %ptw.seen(t, n) : {Bool.or(String.eq(x, n), Cf.named(t, n)) == Bool.or(String.eq(x, n), _) : Bool}
      {==}

def ptw.put(b: Bool, n: String, acc: List<&2, String>) -> {Cf.withheld.put(b, n, acc) == Config.cf_name_once.add(b, n, acc) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ptw.add(b: Bool, +n: String, +acc: List<&2, String>) -> {Cf.withheld.add(b, n, acc) == Config.cf_name_once(Cf.withheld.add(b, n, Nil{}), acc) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Cf.named(acc, n), Config.cf_seen(acc, n), ptw.seen(acc, n)) : {Cf.withheld.put(_, n, acc) == Config.cf_name_once.add(Config.cf_seen(acc, n), n, acc) : List<&2, String>}
      ptw.put(Config.cf_seen(acc, n), n, acc)

def ptw.step(+t: Cf.Trust, h: Cf.Hit, +acc: List<&2, String>) -> {Cf.withheld.step(t, h, acc) == Config.cf_name_once(Cf.withheld.step(t, h, Nil{}), acc) : List<&2, String>}:
  match h:
    case Cf.Hit{+n, s}:
      ptw.add(Cf.applies(t, s), n, acc)

def Config.trust_withheld_step(t, ks, x):
  match x:
    case Cf.PKey{+k, +p, +v}:
      %ptw.go_app(t, ks, [Cf.PKey{k, p, v}], Nil{}) : {_ == Config.cf_name_once(Cf.withheld(t, [Cf.PKey{k, p, v}]), Cf.withheld(t, ks)) : List<&2, String>}
      ptw.step(t, Cf.classify(p), Cf.withheld(t, ks))
