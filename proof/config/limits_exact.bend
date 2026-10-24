# eukhe: the proof of LAW limits_exact
# One provider at a time: the first slot of the provider decides, as in
# the laws' restatement (an induction on the slots, then on the providers).

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def ple.val(v: Cf.Val) -> {Cf.val_limit(v) == Config.cf_lim_val(v) : Cf.Lim}:
  match v:
    case Cf.Num{n}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case Cf.Malformed{}:
      {==}

def ple.pick(b: Bool, v: Cf.Val, m: Maybe<&2, Cf.Val>, l: Cf.Lim, ih: {Cf.slot_limit(m) == l : Cf.Lim}) -> {Cf.slot_limit(Cf.slot.pick(b, v, m)) == Config.cf_slot_lim.pick(b, v, l) : Cf.Lim}:
  match b:
    case True{}:
      ple.val(v)
    case False{}:
      ih

def ple.slots(es: List<&2, Cf.Slot>, +p: Nat) -> {Cf.slot_limit(Cf.slot(es, p)) == Config.cf_slot_lim(es, p) : Cf.Lim}:
  match es:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Slot{q, v}:
          ple.pick(Nat.is_eq(q, p), v, Cf.slot(rest, p), Config.cf_slot_lim(rest, p), ple.slots(rest, p))

def ple.one(s: Cf.InFlight, +p: Nat) -> {Cf.limit(s, p) == Config.cf_limit(s, p) : Cf.Lim}:
  match s:
    case Cf.Unset{}:
      {==}
    case Cf.Entries{es}:
      ple.slots(es, p)
    case Cf.NotMap{}:
      {==}

def Config.limits_exact(s, qs):
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      %ple.one(s, q) : {Cf.limit(s, q) <> Cf.limits(s, rest) == _ <> Config.cf_limits(s, rest) : List<&2, Cf.Lim>}
      %Config.limits_exact(s, rest) : {Cf.limit(s, q) <> Cf.limits(s, rest) == Cf.limit(s, q) <> _ : List<&2, Cf.Lim>}
      {==}
