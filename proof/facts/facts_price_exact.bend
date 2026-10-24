# eukhe: the proof of LAW facts_price_exact
# price.find of the model's rows and of every model's rows are the spec's
# two scans, row by row (the two tests of a row read in either order).

import Base
import ../../bend/facts.bend as Fx
import ../../laws/facts.bend as Facts

def pfe.pk(x: Bool, y: Bool, -want: Maybe<&2, Nat>, -rt: Nat, -k: Nat, -later: Maybe<&2, Nat>) -> {Fx.price.pick(Bool.and(x, y), Fx.PRow{want, rt, k}, later) == Facts.price_spec.pick(Bool.and(y, x), k, later) : Maybe<&2, Nat>}:
  match x:
    case True{}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

def pfe.model.row(want: Maybe<&2, Nat>, +m: Nat, +rt: Nat, +t: Nat, +k: Nat, +later: Maybe<&2, Nat>) -> {Fx.price.pick(Bool.and(Nat.is_eq(rt, t), Fx.same.model(want, m, True{})), Fx.PRow{want, rt, k}, later) == Facts.price_spec.pick(Bool.and(Facts.price_spec.exact(m, want), Nat.is_eq(rt, t)), k, later) : Maybe<&2, Nat>}:
  match want:
    case None{}:
      pfe.pk(Nat.is_eq(rt, t), False{}, None{}, rt, k, later)
    case Some{x}:
      pfe.pk(Nat.is_eq(rt, t), Nat.is_eq(x, m), Some{x}, rt, k, later)

def pfe.model(rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat) -> {Fx.price.find(rows, m, t, True{}) == Facts.price_spec.of_model(rows, m, t) : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case r <> +more:
      match r:
        case Fx.PRow{want, +rt, +k}:
          %Equal.sym(Maybe<&2, Nat>, Fx.price.find(more, m, t, True{}), Facts.price_spec.of_model(more, m, t), pfe.model(more, m, t)) : {Fx.price.pick(Bool.and(Nat.is_eq(rt, t), Fx.same.model(want, m, True{})), Fx.PRow{want, rt, k}, _) == Facts.price_spec.pick(Bool.and(Facts.price_spec.exact(m, want), Nat.is_eq(rt, t)), k, Facts.price_spec.of_model(more, m, t)) : Maybe<&2, Nat>}
          pfe.model.row(want, m, rt, t, k, Facts.price_spec.of_model(more, m, t))

def pfe.all.row(want: Maybe<&2, Nat>, +m: Nat, +rt: Nat, +t: Nat, +k: Nat, +later: Maybe<&2, Nat>) -> {Fx.price.pick(Bool.and(Nat.is_eq(rt, t), Fx.same.model(want, m, False{})), Fx.PRow{want, rt, k}, later) == Facts.price_spec.pick(Bool.and(Facts.price_spec.wide(want), Nat.is_eq(rt, t)), k, later) : Maybe<&2, Nat>}:
  match want:
    case None{}:
      pfe.pk(Nat.is_eq(rt, t), True{}, None{}, rt, k, later)
    case Some{x}:
      pfe.pk(Nat.is_eq(rt, t), False{}, Some{x}, rt, k, later)

def pfe.all(rows: List<&2, Fx.PRow>, +m: Nat, +t: Nat) -> {Fx.price.find(rows, m, t, False{}) == Facts.price_spec.of_all(rows, t) : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case r <> +more:
      match r:
        case Fx.PRow{want, +rt, +k}:
          %Equal.sym(Maybe<&2, Nat>, Fx.price.find(more, m, t, False{}), Facts.price_spec.of_all(more, t), pfe.all(more, m, t)) : {Fx.price.pick(Bool.and(Nat.is_eq(rt, t), Fx.same.model(want, m, False{})), Fx.PRow{want, rt, k}, _) == Facts.price_spec.pick(Bool.and(Facts.price_spec.wide(want), Nat.is_eq(rt, t)), k, Facts.price_spec.of_all(more, t)) : Maybe<&2, Nat>}
          pfe.all.row(want, m, rt, t, k, Facts.price_spec.of_all(more, t))

def pfe.or(a: Maybe<&2, Nat>, -b: Maybe<&2, Nat>) -> {Fx.price.or(a, b) == Facts.price_spec.or(a, b) : Maybe<&2, Nat>}:
  match a:
    case None{}:
      {==}
    case Some{k}:
      {==}

def Facts.facts_price_exact(rows, m, t):
  %Equal.sym(Maybe<&2, Nat>, Fx.price.find(rows, m, t, True{}), Facts.price_spec.of_model(rows, m, t), pfe.model(rows, m, t)) : {Fx.price.or(_, Fx.price.find(rows, m, t, False{})) == Facts.price_spec(rows, m, t) : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Fx.price.find(rows, m, t, False{}), Facts.price_spec.of_all(rows, t), pfe.all(rows, m, t)) : {Fx.price.or(Facts.price_spec.of_model(rows, m, t), _) == Facts.price_spec(rows, m, t) : Maybe<&2, Nat>}
  pfe.or(Facts.price_spec.of_model(rows, m, t), Facts.price_spec.of_all(rows, t))
