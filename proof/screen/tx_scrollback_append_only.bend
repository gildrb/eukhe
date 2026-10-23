# eukhe: the proof of LAW tx_scrollback_append_only

import Base
import ../../bend/screen.bend as Sc
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def screen.ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      L.screen.ps.absurdF({False{} == True{} : Bool}, h)

def screen.ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      L.screen.ps.absurdF({b == True{} : Bool}, h)

# Numbers
# -------

def screen.ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      screen.ps.eq_refl(p)

# 1. The transcript
# -----------------

def ps.lcons(-x: Sc.Line, -a: List<&2, Sc.Line>, -b: List<&2, Sc.Line>, e: {a == b : List<&2, Sc.Line>}) -> {x <> a == x <> b : List<&2, Sc.Line>}:
  %e : {x <> a == x <> _ : List<&2, Sc.Line>}
  {==}

def ps.run_app(pre: List<&2, Sc.Ev>, -post: List<&2, Sc.Ev>, +t: Sc.Tx) -> {Sc.run(post, Sc.run(pre, t)) == Sc.run(List.append(&2, Sc.Ev, pre, post), t) : Sc.Tx}:
  match pre:
    case Nil{}:
      {==}
    case +e <> rest:
      ps.run_app(rest, post, Sc.step(t, e))

# a new active block at the end changes no scrollback
def ps.sapp(bs: List<&2, Sc.Blk>, +i: Nat, +l: Nat) -> {Sc.scroll(bs) == Sc.scroll(List.append(&2, Sc.Blk, bs, [Sc.Blk{i, Sc.Active{}, l}])) : List<&2, Sc.Line>}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{+bi, s, +bl}:
          match s:
            case Sc.Comm{}:
              ps.lcons(Sc.Line{bi, bl}, Sc.scroll(rest), Sc.scroll(List.append(&2, Sc.Blk, rest, [Sc.Blk{i, Sc.Active{}, l}])), ps.sapp(rest, i, l))
            case Sc.Final{}:
              {==}
            case Sc.Active{}:
              {==}

# a growth or a final changes no scrollback
def ps.sedit(bs: List<&2, Sc.Blk>, +x: Nat, hit: Bool, +g: Maybe<&2, Nat>) -> {Sc.scroll(bs) == Sc.scroll(Sc.edit.go(bs, x, g, hit)) : List<&2, Sc.Line>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Sc.Blk{+i, s, +l}:
          match s:
            case Sc.Comm{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      ps.lcons(Sc.Line{i, l}, Sc.scroll(rest), Sc.scroll(Sc.edit.go(rest, x, None{}, Sc.bid.at(rest, x))), ps.sedit(rest, x, Sc.bid.at(rest, x), None{}))
                    case Some{+n}:
                      ps.lcons(Sc.Line{i, l}, Sc.scroll(rest), Sc.scroll(Sc.edit.go(rest, x, Some{n}, Sc.bid.at(rest, x))), ps.sedit(rest, x, Sc.bid.at(rest, x), Some{n}))
                case False{}:
                  ps.lcons(Sc.Line{i, l}, Sc.scroll(rest), Sc.scroll(Sc.edit.go(rest, x, g, Sc.bid.at(rest, x))), ps.sedit(rest, x, Sc.bid.at(rest, x), g))
            case Sc.Final{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      {==}
                    case Some{n}:
                      {==}
                case False{}:
                  {==}
            case Sc.Active{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      {==}
                    case Some{n}:
                      {==}
                case False{}:
                  {==}

# a flush keeps every prefix of the scrollback
def ps.flush_pre(bs: List<&2, Sc.Blk>, X: List<&2, Sc.Line>, +h: {Sc.pre(X, Sc.scroll(bs)) == True{} : Bool}) -> {Sc.pre(X, Sc.scroll(Sc.flush(bs))) == True{} : Bool}:
  match bs:
    case Nil{}:
      h
    case b <> +rest:
      match b:
        case Sc.Blk{+i, s, +l}:
          match s:
            case Sc.Comm{}:
              match X:
                case Nil{}:
                  {==}
                case Sc.Line{+a, +c} <> +xr:
                  +q = Bool.and(Nat.is_eq(a, i), Nat.is_eq(c, l))
                  LA.screen.ps.and_t(q, Sc.pre(xr, Sc.scroll(Sc.flush(rest))), screen.ps.and_l(q, Sc.pre(xr, Sc.scroll(rest)), h), ps.flush_pre(rest, xr, screen.ps.and_r(q, Sc.pre(xr, Sc.scroll(rest)), h)))
            case Sc.Final{}:
              match X:
                case Nil{}:
                  {==}
                case Sc.Line{a, c} <> xr:
                  L.screen.ps.absurdF({Sc.pre(Sc.Line{a, c} <> xr, Sc.scroll(Sc.flush(Sc.Blk{i, Sc.Final{}, l} <> rest))) == True{} : Bool}, h)
            case Sc.Active{}:
              h

def ps.sstep(+t: Sc.Tx, +e: Sc.Ev, +X: List<&2, Sc.Line>, h: {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(t))) == True{} : Bool}) -> {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(Sc.step(t, e)))) == True{} : Bool}:
  match t:
    case Sc.Tx{+bs, +n, w}:
      match e:
        case Sc.Open{}:
          %ps.sapp(bs, n, 0n) : {Sc.pre(X, _) == True{} : Bool}
          h
        case Sc.Grow{+x, k}:
          %ps.sedit(bs, x, Sc.bid.at(bs, x), Some{k}) : {Sc.pre(X, _) == True{} : Bool}
          h
        case Sc.Fin{+x}:
          %ps.sedit(bs, x, Sc.bid.at(bs, x), None{}) : {Sc.pre(X, _) == True{} : Bool}
          h
        case Sc.Flush{}:
          ps.flush_pre(bs, X, h)
        case Sc.Resize{v}:
          h

def ps.srun(post: List<&2, Sc.Ev>, +t: Sc.Tx, +X: List<&2, Sc.Line>, h: {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(t))) == True{} : Bool}) -> {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(Sc.run(post, t)))) == True{} : Bool}:
  match post:
    case Nil{}:
      h
    case +e <> rest:
      ps.srun(rest, Sc.step(t, e), X, ps.sstep(t, e, X, h))

def ps.pre_refl(X: List<&2, Sc.Line>) -> {Sc.pre(X, X) == True{} : Bool}:
  match X:
    case Nil{}:
      {==}
    case Sc.Line{+a, +c} <> +xr:
      %screen.ps.eq_refl(a) : {Bool.and(Bool.and(_, Nat.is_eq(c, c)), Sc.pre(xr, xr)) == True{} : Bool}
      %screen.ps.eq_refl(c) : {Bool.and(Bool.and(True{}, _), Sc.pre(xr, xr)) == True{} : Bool}
      ps.pre_refl(xr)

def ps.tx_scrollback_append_only(+pre: List<&2, Sc.Ev>, post: List<&2, Sc.Ev>, +w: Nat) -> {Sc.pre(Sc.scroll(Sc.Tx.blocks(Sc.run(pre, Sc.Tx{Nil{}, 0n, w}))), Sc.scroll(Sc.Tx.blocks(Sc.run(List.append(&2, Sc.Ev, pre, post), Sc.Tx{Nil{}, 0n, w})))) == True{} : Bool}:
  +t = Sc.run(pre, Sc.Tx{Nil{}, 0n, w})
  +X = Sc.scroll(Sc.Tx.blocks(t))
  %ps.run_app(pre, post, Sc.Tx{Nil{}, 0n, w}) : {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(_))) == True{} : Bool}
  ps.srun(post, t, X, ps.pre_refl(X))

def Laws.tx_scrollback_append_only(pre, post, w):
  ps.tx_scrollback_append_only(pre, post, w)
