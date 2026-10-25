# eukhe: the proof of LAW effective_exact

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../spec/config_rules.bend as CR

def pe.admits(t: Cf.Trust, c: Cf.Class) -> {Cf.admits(t, c) == CR.cr_admits(t, c) : Bool}:
  match t:
    case Cf.Trusted{}:
      {==}
    case Cf.Untrusted{}:
      match c:
        case Cf.Pref{}:
          {==}
        case Cf.Limit{}:
          {==}
        case Cf.Prompt{}:
          {==}
        case Cf.Credential{}:
          {==}
        case Cf.Code{}:
          {==}

def pe.put(b: Bool, +k: Nat, +v: Nat, x: List<&2, Cf.Entry>, y: List<&2, Cf.Entry>, ih: {x == y : List<&2, Cf.Entry>}) -> {Cf.guard(b, Cf.Entry{k, v}, x) == CR.cr_put(b, k, v, y) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      %ih : {Cf.Entry{k, v} <> x == Cf.Entry{k, v} <> _ : List<&2, Cf.Entry>}
      {==}
    case False{}:
      ih

def pe.go(+t: Cf.Trust, +g: List<&2, Cf.Entry>, items: List<&2, Cf.Item>) -> {Cf.effective(t, g, items) == CR.cr_effective(t, g, items) : List<&2, Cf.Entry>}:
  match items:
    case Nil{}:
      {==}
    case i <> +rest:
      match i:
        case Cf.Item{+k, +c, +v}:
          %pe.admits(t, c) : {Cf.guard(Cf.admits(t, c), Cf.Entry{k, v}, Cf.effective(t, g, rest)) == CR.cr_put(_, k, v, CR.cr_effective(t, g, rest)) : List<&2, Cf.Entry>}
          pe.put(Cf.admits(t, c), k, v, Cf.effective(t, g, rest), CR.cr_effective(t, g, rest), pe.go(t, g, rest))

def Config.effective_exact(t, g, items):
  +h = g
  pe.go(t, h, items)
