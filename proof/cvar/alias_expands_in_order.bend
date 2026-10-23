# eukhe: the proof of LAW alias_expands_in_order

import Base
import ../../bend/cvar.bend as Cv
import ../../LAWS.bend as Laws

# reversing a concatenation: the second, reversed onto the first reversed
def pv.rev_app(z: List<&2, Cv.Cmd>, +y: List<&2, Cv.Cmd>, +p: List<&2, Cv.Cmd>) -> {Cv.rev(List.append(&2, Cv.Cmd, z, y), p) == Cv.rev(y, Cv.rev(z, p)) : List<&2, Cv.Cmd>}:
  match z:
    case Nil{}:
      {==}
    case +x <> rest:
      pv.rev_app(rest, y, x <> p)

# appending is associative
def pv.app_assoc(xs: List<&2, Cv.Cmd>, +ys: List<&2, Cv.Cmd>, +zs: List<&2, Cv.Cmd>) -> {List.append(&2, Cv.Cmd, List.append(&2, Cv.Cmd, xs, ys), zs) == List.append(&2, Cv.Cmd, xs, List.append(&2, Cv.Cmd, ys, zs)) : List<&2, Cv.Cmd>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> r:
      %pv.app_assoc(r, ys, zs) : {h <> List.append(&2, Cv.Cmd, List.append(&2, Cv.Cmd, r, ys), zs) == h <> _ : List<&2, Cv.Cmd>}
      {==}

# reversing onto q is reversing, then q
def pv.rev_out(y: List<&2, Cv.Cmd>, +q: List<&2, Cv.Cmd>) -> {Cv.rev(y, q) == List.append(&2, Cv.Cmd, Cv.rev(y, Nil{}), q) : List<&2, Cv.Cmd>}:
  match y:
    case Nil{}:
      {==}
    case +x <> +rest:
      +r = Cv.rev(rest, Nil{})
      +a = pv.rev_out(rest, x <> q)
      +b = pv.rev_out(rest, [x])
      %Equal.sym(List<&2, Cv.Cmd>, Cv.rev(rest, [x]), List.append(&2, Cv.Cmd, r, [x]), b) : {Cv.rev(rest, x <> q) == List.append(&2, Cv.Cmd, _, q) : List<&2, Cv.Cmd>}
      %Equal.sym(List<&2, Cv.Cmd>, List.append(&2, Cv.Cmd, List.append(&2, Cv.Cmd, r, [x]), q), List.append(&2, Cv.Cmd, r, x <> q), pv.app_assoc(r, [x], q)) : {Cv.rev(rest, x <> q) == _ : List<&2, Cv.Cmd>}
      a

# Expansion
# ---------

# an expansion that failed stays failed
def pv.go_cycle(d: Nat, xs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +m: Nat) -> {Cv.expand.go(d, xs, as, Cv.Cycle{m}) == Cv.Cycle{m} : Cv.Exp}:
  match d:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+e:
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}

def pv.go_unknown(d: Nat, xs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, +m: Nat) -> {Cv.expand.go(d, xs, as, Cv.Unknown{m}) == Cv.Unknown{m} : Cv.Exp}:
  match d:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}
    case 1n+e:
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              {==}
            case Cv.CToggle{i}:
              {==}
            case Cv.CRun{n}:
              {==}
            case Cv.CGone{n}:
              {==}

# In order
# --------

# an expansion of cs ++ more goes on from the expansion of cs
def pv.go_app(d: Nat, cs: List<&2, Cv.Cmd>, +more: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, acc: Cv.Exp) -> {Cv.expand.go(d, List.append(&2, Cv.Cmd, cs, more), as, acc) == Cv.expand.go(d, more, as, Cv.expand.go(d, cs, as, acc)) : Cv.Exp}:
  match d:
    case 0n:
      match cs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_app(0n, rest, more, as, Cv.Flat{Cv.CSet{i, v} <> out})
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(0n, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(0n, more, as, m))
            case Cv.CToggle{i}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_app(0n, rest, more, as, Cv.Flat{Cv.CToggle{i} <> out})
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(0n, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(0n, more, as, m))
            case Cv.CRun{+n}:
              match acc:
                case Cv.Flat{out}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Cycle{n}), Cv.Cycle{n}, pv.go_cycle(0n, more, as, n))
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(0n, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(0n, more, as, m))
            case Cv.CGone{+n}:
              match acc:
                case Cv.Flat{out}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Unknown{n}), Cv.Unknown{n}, pv.go_unknown(0n, more, as, n))
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(0n, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(0n, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(0n, more, as, m))
    case 1n+(+e):
      match cs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_app(1n+e, rest, more, as, Cv.Flat{Cv.CSet{i, v} <> out})
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(1n+e, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(1n+e, more, as, m))
            case Cv.CToggle{i}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_app(1n+e, rest, more, as, Cv.Flat{Cv.CToggle{i} <> out})
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(1n+e, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(1n+e, more, as, m))
            case Cv.CRun{+n}:
              match acc:
                case Cv.Flat{out}:
                  pv.go_app(1n+e, rest, more, as, Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{out}))
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(1n+e, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(1n+e, more, as, m))
            case Cv.CGone{+n}:
              match acc:
                case Cv.Flat{out}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Unknown{n}), Cv.Unknown{n}, pv.go_unknown(1n+e, more, as, n))
                case Cv.Cycle{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(1n+e, more, as, m))
                case Cv.Unknown{+m}:
                  Equal.sym(Cv.Exp, Cv.expand.go(1n+e, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(1n+e, more, as, m))

# the commands gathered of an expansion, with out after them
def pv.shift(e: Cv.Exp, +out: List<&2, Cv.Cmd>) -> Cv.Exp:
  match e:
    case Cv.Flat{y}:
      Cv.Flat{List.append(&2, Cv.Cmd, y, out)}
    case Cv.Cycle{m}:
      Cv.Cycle{m}
    case Cv.Unknown{m}:
      Cv.Unknown{m}

# an expansion onto an accumulator with out under it is the expansion
# with out under its result
def pv.go_shift(d: Nat, xs: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>, a: Cv.Exp, +out: List<&2, Cv.Cmd>) -> {Cv.expand.go(d, xs, as, pv.shift(a, out)) == pv.shift(Cv.expand.go(d, xs, as, a), out) : Cv.Exp}:
  match d:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match a:
                case Cv.Flat{y}:
                  pv.go_shift(0n, rest, as, Cv.Flat{Cv.CSet{i, v} <> y}, out)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CToggle{i}:
              match a:
                case Cv.Flat{y}:
                  pv.go_shift(0n, rest, as, Cv.Flat{Cv.CToggle{i} <> y}, out)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CRun{n}:
              match a:
                case Cv.Flat{y}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CGone{n}:
              match a:
                case Cv.Flat{y}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
    case 1n+(+e):
      match xs:
        case Nil{}:
          {==}
        case c <> rest:
          match c:
            case Cv.CSet{i, v}:
              match a:
                case Cv.Flat{y}:
                  pv.go_shift(1n+e, rest, as, Cv.Flat{Cv.CSet{i, v} <> y}, out)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CToggle{i}:
              match a:
                case Cv.Flat{y}:
                  pv.go_shift(1n+e, rest, as, Cv.Flat{Cv.CToggle{i} <> y}, out)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CRun{+n}:
              match a:
                case Cv.Flat{+y}:
                  +g = Cv.expand.go(e, Cv.body(as, n), as, Cv.Flat{y})
                  %Equal.sym(Cv.Exp, Cv.expand.go(e, Cv.body(as, n), as, pv.shift(Cv.Flat{y}, out)), pv.shift(g, out), pv.go_shift(e, Cv.body(as, n), as, Cv.Flat{y}, out)) : {Cv.expand.go(1n+e, rest, as, _) == pv.shift(Cv.expand.go(1n+e, rest, as, g), out) : Cv.Exp}
                  pv.go_shift(1n+e, rest, as, g, out)
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}
            case Cv.CGone{n}:
              match a:
                case Cv.Flat{y}:
                  {==}
                case Cv.Cycle{m}:
                  {==}
                case Cv.Unknown{m}:
                  {==}

# fin of the rest's expansion with the first's commands under it
def pv.fin_shift(m: Cv.Exp, +y: List<&2, Cv.Cmd>) -> {Cv.fin(pv.shift(m, y)) == Laws.cvar_cat(Cv.Flat{Cv.rev(y, Nil{})}, Cv.fin(m)) : Cv.Exp}:
  match m:
    case Cv.Flat{+z}:
      %Equal.sym(List<&2, Cv.Cmd>, Cv.rev(List.append(&2, Cv.Cmd, z, y), Nil{}), Cv.rev(y, Cv.rev(z, Nil{})), pv.rev_app(z, y, Nil{})) : {Cv.Flat{_} == Cv.Flat{List.append(&2, Cv.Cmd, Cv.rev(y, Nil{}), Cv.rev(z, Nil{}))} : Cv.Exp}
      Equal.cong(List<&2, Cv.Cmd>, Cv.Exp, l => Cv.Flat{l}, Cv.rev(y, Cv.rev(z, Nil{})), List.append(&2, Cv.Cmd, Cv.rev(y, Nil{}), Cv.rev(z, Nil{})), pv.rev_out(y, Cv.rev(z, Nil{})))
    case Cv.Cycle{m}:
      {==}
    case Cv.Unknown{m}:
      {==}

# the expansion of the rest after the first's, put in order
def pv.in_order(c: Cv.Exp, +d: Nat, +more: List<&2, Cv.Cmd>, +as: List<&2, Cv.Alias>) -> {Cv.fin(Cv.expand.go(d, more, as, c)) == Laws.cvar_cat(Cv.fin(c), Cv.fin(Cv.expand.go(d, more, as, Cv.Flat{Nil{}}))) : Cv.Exp}:
  match c:
    case Cv.Flat{+y}:
      %Equal.sym(Cv.Exp, Cv.expand.go(d, more, as, pv.shift(Cv.Flat{Nil{}}, y)), pv.shift(Cv.expand.go(d, more, as, Cv.Flat{Nil{}}), y), pv.go_shift(d, more, as, Cv.Flat{Nil{}}, y)) : {Cv.fin(_) == Laws.cvar_cat(Cv.Flat{Cv.rev(y, Nil{})}, Cv.fin(Cv.expand.go(d, more, as, Cv.Flat{Nil{}}))) : Cv.Exp}
      pv.fin_shift(Cv.expand.go(d, more, as, Cv.Flat{Nil{}}), y)
    case Cv.Cycle{+m}:
      %Equal.sym(Cv.Exp, Cv.expand.go(d, more, as, Cv.Cycle{m}), Cv.Cycle{m}, pv.go_cycle(d, more, as, m)) : {Cv.fin(_) == Cv.Cycle{m} : Cv.Exp}
      {==}
    case Cv.Unknown{+m}:
      %Equal.sym(Cv.Exp, Cv.expand.go(d, more, as, Cv.Unknown{m}), Cv.Unknown{m}, pv.go_unknown(d, more, as, m)) : {Cv.fin(_) == Cv.Unknown{m} : Cv.Exp}
      {==}

def Laws.alias_expands_in_order(cs, more, as):
  +d = {1n+List.length(&2, Cv.Alias, as) : Nat}
  %Equal.sym(Cv.Exp, Cv.expand.go(d, List.append(&2, Cv.Cmd, cs, more), as, Cv.Flat{Nil{}}), Cv.expand.go(d, more, as, Cv.expand.go(d, cs, as, Cv.Flat{Nil{}})), pv.go_app(d, cs, more, as, Cv.Flat{Nil{}})) : {Cv.fin(_) == Laws.cvar_cat(Cv.expand(cs, as), Cv.expand(more, as)) : Cv.Exp}
  pv.in_order(Cv.expand.go(d, cs, as, Cv.Flat{Nil{}}), d, more, as)
