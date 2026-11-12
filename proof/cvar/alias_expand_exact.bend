# eukhe: the proof of LAW alias_expand_exact
# The model gathers commands last first into an accumulator; an expansion
# onto any accumulator is that accumulator's commands, then the expansion
# onto none (PIO.pv.in_order). So, level by level and command by command,
# the model's expansion onto none is the spec's (pxx.go); the body lookup
# is the spec's (pxx.body).

import Base
import ../../bend/cvar.bend as Cv
import ../../laws/cvar/entry.bend as Cvar
import ../../laws/cvar/model.bend as CvarModel
import ./alias_expands_in_order.bend as PIO

def pxx.body_step(b: Bool, +m: Nat, +bd: List<&2, Cv.Cmd>, +rest: List<&2, Cv.Alias>, +n: Nat, ih: {Cv.body(rest, n) == Cvar.spec_body_orig(rest, n) : List<&2, Cv.Cmd>}) -> {Cv.body.go(Cv.Alias{m, bd} <> rest, n, b) == Cvar.spec_body.pick(b, bd, Cvar.spec_body_orig(rest, n)) : List<&2, Cv.Cmd>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pxx.body(as: List<&2, Cv.Alias>, +n: Nat) -> {Cv.body(as, n) == Cvar.spec_body_orig(as, n) : List<&2, Cv.Cmd>}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{+m, +bd} <> +rest:
      pxx.body_step(Nat.is_eq(m, n), m, bd, rest, n, pxx.body(rest, n))

def pxx.go(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.fin(Cv.expand.go(d, cs, as, Cv.Flat{Nil{}})) == Cvar.spec_expand.go(d, cs, as) : Cv.Exp}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{[Cv.CSet{i, v}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CSet{i, v}]}, 0n, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cvar.spec_expand.go(0n, rest, as)) : Cv.Exp}
              %pxx.go(0n, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, _) : Cv.Exp}
              {==}
            case Cv.CToggle{+i}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{[Cv.CToggle{i}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CToggle{i}]}, 0n, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, Cvar.spec_expand.go(0n, rest, as)) : Cv.Exp}
              %pxx.go(0n, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, _) : Cv.Exp}
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+(+e):
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{[Cv.CSet{i, v}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CSet{i, v}]}, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, _) : Cv.Exp}
              {==}
            case Cv.CToggle{+i}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{[Cv.CToggle{i}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CToggle{i}]}, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, _) : Cv.Exp}
              {==}
            case Cv.CRun{+n}:
              +inner = Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{Nil{}})
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, inner)), CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(inner, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cvar.spec_expand.go(e, Cvar.spec_body_orig(as, n), as), Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cvar.spec_expand.go(e, Cvar.spec_body_orig(as, n), as), _) : Cv.Exp}
              %pxx.body(as, n) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cvar.spec_expand.go(e, _, as), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) : Cv.Exp}
              %pxx.go(e, Cv.body(as, n), as) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(_, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) : Cv.Exp}
              {==}
            case Cv.CGone{n}:
              {==}

def pxx.expand(cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.expand(cs, as) == Cvar.spec_expand(cs, as) : Cv.Exp}:
  pxx.go(1n+List.length(&2, Cv.Alias, as), cs, as)

def Cvar.alias_expand_exact(cs, as, n):
  (pxx.expand(cs, as), pxx.body(as, n))

def pxx.body_step_orig(b: Bool, +m: Nat, +bd: List<&2, Cv.Cmd>, +rest: List<&2, Cv.Alias>, +n: Nat, ih: {Cv.body(rest, n) == Cvar.spec_body_orig(rest, n) : List<&2, Cv.Cmd>}) -> {Cv.body.go(Cv.Alias{m, bd} <> rest, n, b) == Cvar.spec_body.pick(b, bd, Cvar.spec_body_orig(rest, n)) : List<&2, Cv.Cmd>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pxx.body_orig(as: List<&2, Cv.Alias>, +n: Nat) -> {Cv.body(as, n) == Cvar.spec_body_orig(as, n) : List<&2, Cv.Cmd>}:
  match as:
    case Nil{}:
      {==}
    case Cv.Alias{+m, +bd} <> +rest:
      pxx.body_step_orig(Nat.is_eq(m, n), m, bd, rest, n, pxx.body_orig(rest, n))

def pxx.go_orig(d: Nat, cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.fin(Cv.expand.go(d, cs, as, Cv.Flat{Nil{}})) == Cvar.spec_expand.go(d, cs, as) : Cv.Exp}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{[Cv.CSet{i, v}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CSet{i, v}]}, 0n, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cvar.spec_expand.go(0n, rest, as)) : Cv.Exp}
              %pxx.go_orig(0n, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, _) : Cv.Exp}
              {==}
            case Cv.CToggle{+i}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{[Cv.CToggle{i}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CToggle{i}]}, 0n, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, Cvar.spec_expand.go(0n, rest, as)) : Cv.Exp}
              %pxx.go_orig(0n, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(0n, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, _) : Cv.Exp}
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+(+e):
      match cs:
        case Nil{}:
          {==}
        case c <> +rest:
          match c:
            case Cv.CSet{+i, +v}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{[Cv.CSet{i, v}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CSet{i, v}]}, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go_orig(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CSet{i, v}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CSet{i, v}]}, _) : Cv.Exp}
              {==}
            case Cv.CToggle{+i}:
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{[Cv.CToggle{i}]})), CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(Cv.Flat{[Cv.CToggle{i}]}, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go_orig(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(Cv.Flat{[Cv.CToggle{i}]}), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cv.Flat{[Cv.CToggle{i}]}, _) : Cv.Exp}
              {==}
            case Cv.CRun{+n}:
              +inner = Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{Nil{}})
              %Equal.sym(Cv.Exp, Cv.fin(Cv.expand.go(1n+e, rest, as, inner)), CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))), PIO.pv.in_order(inner, 1n+e, rest, as)) : {_ == CvarModel.cvar_cat(Cvar.spec_expand.go(e, Cvar.spec_body_orig(as, n), as), Cvar.spec_expand.go(1n+e, rest, as)) : Cv.Exp}
              %pxx.go_orig(1n+e, rest, as) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cvar.spec_expand.go(e, Cvar.spec_body_orig(as, n), as), _) : Cv.Exp}
              %pxx.body_orig(as, n) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(Cvar.spec_expand.go(e, _, as), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) : Cv.Exp}
              %pxx.go_orig(e, Cv.body(as, n), as) : {CvarModel.cvar_cat(Cv.fin(inner), Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) == CvarModel.cvar_cat(_, Cv.fin(Cv.expand.go(1n+e, rest, as, Cv.Flat{Nil{}}))) : Cv.Exp}
              {==}
            case Cv.CGone{n}:
              {==}

def pxx.expand_orig(cs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.expand(cs, as) == Cvar.spec_expand(cs, as) : Cv.Exp}:
  pxx.go_orig(1n+List.length(&2, Cv.Alias, as), cs, as)
