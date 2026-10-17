# proof_screen: the S8 laws (docs/harness.md) of the interface model in
# bend/screen.bend: the scrollback has no gap and only grows, a resize and
# a flush keep it in order, the pacer never runs ahead nor back and drains
# a backlog, only checked frames reach the terminal, and a vertical stack
# keeps its children inside the viewport, apart, and whole when they fit.

import Base
import ./screen.bend as Sc

# Logic
# -----

def ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ps.BD(_, A, Unit)
  Unit{}

def ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ps.absurdF({False{} == True{} : Bool}, h)

def ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ps.absurdF({b == True{} : Bool}, h)

def ps.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def ps.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# Numbers
# -------

def ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      ps.eq_refl(p)

def ps.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def ps.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ps.le_refl(p)

def ps.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ps.le_succ(p)

def ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le0(c)
    case 1n+ap 0n _:
      ps.absurdF({Nat.is_le(1n+ap, c) == True{} : Bool}, ab)
    case 1n+ap 1n+bp 0n:
      ps.absurdF({Nat.is_le(1n+ap, 0n) == True{} : Bool}, bc)
    case 1n+ap 1n+bp 1n+cp:
      ps.le_trans(ap, bp, cp, ab, bc)

# s is at most s + x
def ps.le_add_self(s: Nat, +x: Nat) -> {Nat.is_le(s, Nat.add(s, x)) == True{} : Bool}:
  match s:
    case 0n:
      ps.le0(x)
    case 1n+p:
      ps.le_add_self(p, x)

def ps.le_add_r(s: Nat, r: Nat, +n: Nat, h: {Nat.is_le(s, r) == True{} : Bool}) -> {Nat.is_le(s, Nat.add(r, n)) == True{} : Bool}:
  match s r:
    case 0n _:
      ps.le0(Nat.add(r, n))
    case 1n+sp 0n:
      ps.absurdF({Nat.is_le(1n+sp, Nat.add(0n, n)) == True{} : Bool}, h)
    case 1n+sp 1n+rp:
      ps.le_add_r(sp, rp, n, h)

def ps.le_add_l(y: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, a), Nat.add(y, b)) == True{} : Bool}:
  match y:
    case 0n:
      h
    case 1n+p:
      ps.le_add_l(p, a, b, h)

def ps.le_assoc(y: Nat, +h: Nat, +s: Nat, rows: Nat, f: {Nat.is_le(Nat.add(y, Nat.add(h, s)), rows) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(y, h), s), rows) == True{} : Bool}:
  match y rows:
    case 0n _:
      f
    case 1n+p 0n:
      ps.absurdF({Nat.is_le(Nat.add(Nat.add(1n+p, h), s), 0n) == True{} : Bool}, f)
    case 1n+p 1n+rp:
      ps.le_assoc(p, h, s, rp, f)

def ps.le_addl(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(n, m) == True{} : Bool}:
  match n m:
    case 0n _:
      ps.le0(m)
    case 1n+np 0n:
      ps.absurdF({Nat.is_le(1n+np, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      ps.le_addl(np, p, mp, h)

def ps.le_sub(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(m, n)) == True{} : Bool}:
  match n m:
    case 0n 0n:
      h
    case 0n 1n+mp:
      h
    case 1n+np 0n:
      ps.absurdF({Nat.is_le(p, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      ps.le_sub(np, p, mp, h)

def ps.sub_le(+n: Nat, +m: Nat) -> {Nat.is_le(Nat.sub(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      ps.le_refl(1n+np)
    case 1n+np 1n+mp:
      ps.le_trans(Nat.sub(np, mp), np, 1n+np, ps.sub_le(np, mp), ps.le_succ(np))

def ps.sub_sub(c: Nat, k: Nat, +n: Nat) -> {Nat.sub(Nat.sub(c, k), n) == Nat.sub(c, Nat.add(k, n)) : Nat}:
  match c k:
    case 0n _:
      {==}
    case 1n+cp 0n:
      {==}
    case 1n+cp 1n+kp:
      ps.sub_sub(cp, kp, n)

def ps.min_le_l(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      ps.min_le_l(np, mp)

def ps.min_le_r(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n m:
    case 0n _:
      ps.le0(m)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      ps.min_le_r(np, mp)

def ps.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {Nat.min(n, m) == n : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      ps.absurdF({Nat.min(1n+np, 0n) == 1n+np : Nat}, h)
    case 1n+np 1n+mp:
      %ps.min_of_le(np, mp, h) : {1n+Nat.min(np, mp) == 1n+_ : Nat}
      {==}

# a maximum with a positive side is positive
def ps.max_ge(min: Nat, x: Nat, one: {Nat.is_le(1n, min) == True{} : Bool}) -> {Nat.is_le(1n, Nat.max(min, x)) == True{} : Bool}:
  match min x:
    case 0n _:
      ps.absurdF({Nat.is_le(1n, Nat.max(0n, x)) == True{} : Bool}, one)
    case 1n+mp 0n:
      ps.le0(mp)
    case 1n+mp 1n+xp:
      ps.le0(Nat.max(mp, xp))

def ps.eq_of(s: Nat, r: Nat, h1: {Nat.is_le(s, r) == True{} : Bool}, h2: {Nat.is_le(Nat.sub(r, s), 0n) == True{} : Bool}) -> {s == r : Nat}:
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n+rp:
      ps.absurdF({0n == 1n+rp : Nat}, h2)
    case 1n+sp 0n:
      ps.absurdF({1n+sp == 0n : Nat}, h1)
    case 1n+sp 1n+rp:
      %ps.eq_of(sp, rp, h1, h2) : {1n+sp == 1n+_ : Nat}
      {==}

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

# a new active block at the end changes no gap
def ps.gapp(bs: List<&2, Sc.Blk>, +i: Nat, +l: Nat, +seen: Bool) -> {Sc.gapless.go(bs, seen) == Sc.gapless.go(List.append(&2, Sc.Blk, bs, [Sc.Blk{i, Sc.Active{}, l}]), seen) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{bi, s, bl}:
          match s:
            case Sc.Comm{}:
              match seen:
                case True{}:
                  {==}
                case False{}:
                  ps.gapp(rest, i, l, False{})
            case Sc.Final{}:
              ps.gapp(rest, i, l, True{})
            case Sc.Active{}:
              ps.gapp(rest, i, l, True{})

# a growth or a final changes no gap
def ps.gedit(bs: List<&2, Sc.Blk>, +x: Nat, hit: Bool, +g: Maybe<&2, Nat>, +seen: Bool) -> {Sc.gapless.go(bs, seen) == Sc.gapless.go(Sc.edit.go(bs, x, g, hit), seen) : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      match seen:
                        case True{}:
                          {==}
                        case False{}:
                          ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, False{})
                    case Some{n}:
                      match seen:
                        case True{}:
                          {==}
                        case False{}:
                          ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, False{})
                case False{}:
                  match seen:
                    case True{}:
                      {==}
                    case False{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), g, False{})
            case Sc.Final{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, True{})
                    case Some{n}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, True{})
                case False{}:
                  ps.gedit(rest, x, Sc.bid.at(rest, x), g, True{})
            case Sc.Active{}:
              match hit:
                case True{}:
                  match g:
                    case None{}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), None{}, True{})
                    case Some{n}:
                      ps.gedit(rest, x, Sc.bid.at(rest, x), Some{n}, True{})
                case False{}:
                  ps.gedit(rest, x, Sc.bid.at(rest, x), g, True{})

# a flush of blocks without a gap after `seen` leaves no gap
def ps.gflush(bs: List<&2, Sc.Blk>, seen: Bool, h: {Sc.gapless.go(bs, seen) == True{} : Bool}) -> {Sc.gapless.go(Sc.flush(bs), False{}) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              match seen:
                case True{}:
                  ps.absurdF({Sc.gapless.go(Sc.flush(Sc.Blk{i, Sc.Comm{}, l} <> rest), False{}) == True{} : Bool}, h)
                case False{}:
                  ps.gflush(rest, False{}, h)
            case Sc.Final{}:
              ps.gflush(rest, True{}, h)
            case Sc.Active{}:
              h

def ps.gstep(+t: Sc.Tx, +e: Sc.Ev, h: {Sc.gapless(Sc.Tx.blocks(t)) == True{} : Bool}) -> {Sc.gapless(Sc.Tx.blocks(Sc.step(t, e))) == True{} : Bool}:
  match t:
    case Sc.Tx{+bs, +n, w}:
      match e:
        case Sc.Open{}:
          %ps.gapp(bs, n, 0n, False{}) : {_ == True{} : Bool}
          h
        case Sc.Grow{+x, k}:
          %ps.gedit(bs, x, Sc.bid.at(bs, x), Some{k}, False{}) : {_ == True{} : Bool}
          h
        case Sc.Fin{+x}:
          %ps.gedit(bs, x, Sc.bid.at(bs, x), None{}, False{}) : {_ == True{} : Bool}
          h
        case Sc.Flush{}:
          ps.gflush(bs, False{}, h)
        case Sc.Resize{v}:
          h

def ps.grun(es: List<&2, Sc.Ev>, +t: Sc.Tx, h: {Sc.gapless(Sc.Tx.blocks(t)) == True{} : Bool}) -> {Sc.gapless(Sc.Tx.blocks(Sc.run(es, t))) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ps.grun(rest, Sc.step(t, e), ps.gstep(t, e, h))

def ps.tx_gapless(es: List<&2, Sc.Ev>, +w: Nat) -> {Sc.gapless(Sc.Tx.blocks(Sc.run(es, Sc.Tx{Nil{}, 0n, w}))) == True{} : Bool}:
  ps.grun(es, Sc.Tx{Nil{}, 0n, w}, {==})

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
                  ps.and_t(q, Sc.pre(xr, Sc.scroll(Sc.flush(rest))), ps.and_l(q, Sc.pre(xr, Sc.scroll(rest)), h), ps.flush_pre(rest, xr, ps.and_r(q, Sc.pre(xr, Sc.scroll(rest)), h)))
            case Sc.Final{}:
              match X:
                case Nil{}:
                  {==}
                case Sc.Line{a, c} <> xr:
                  ps.absurdF({Sc.pre(Sc.Line{a, c} <> xr, Sc.scroll(Sc.flush(Sc.Blk{i, Sc.Final{}, l} <> rest))) == True{} : Bool}, h)
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
      %ps.eq_refl(a) : {Bool.and(Bool.and(_, Nat.is_eq(c, c)), Sc.pre(xr, xr)) == True{} : Bool}
      %ps.eq_refl(c) : {Bool.and(Bool.and(True{}, _), Sc.pre(xr, xr)) == True{} : Bool}
      ps.pre_refl(xr)

def ps.tx_scrollback_append_only(+pre: List<&2, Sc.Ev>, post: List<&2, Sc.Ev>, +w: Nat) -> {Sc.pre(Sc.scroll(Sc.Tx.blocks(Sc.run(pre, Sc.Tx{Nil{}, 0n, w}))), Sc.scroll(Sc.Tx.blocks(Sc.run(List.append(&2, Sc.Ev, pre, post), Sc.Tx{Nil{}, 0n, w})))) == True{} : Bool}:
  +t = Sc.run(pre, Sc.Tx{Nil{}, 0n, w})
  +X = Sc.scroll(Sc.Tx.blocks(t))
  %ps.run_app(pre, post, Sc.Tx{Nil{}, 0n, w}) : {Sc.pre(X, Sc.scroll(Sc.Tx.blocks(_))) == True{} : Bool}
  ps.srun(post, t, X, ps.pre_refl(X))

def ps.tx_resize_keeps(+t: Sc.Tx, +w: Nat) -> {Sc.Tx.blocks(Sc.step(t, Sc.Resize{w})) == Sc.Tx.blocks(t) : List<&2, Sc.Blk>}:
  match t:
    case Sc.Tx{bs, n, v}:
      {==}

def ps.flushed_flush(bs: List<&2, Sc.Blk>) -> {Sc.flushed(Sc.flush(bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              ps.flushed_flush(rest)
            case Sc.Final{}:
              ps.flushed_flush(rest)
            case Sc.Active{}:
              {==}

def ps.tx_flush_settles(+t: Sc.Tx) -> {Sc.flushed(Sc.Tx.blocks(Sc.step(t, Sc.Flush{}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      ps.flushed_flush(bs)

# 2. Pacing
# ---------

# a frame shows no more than the backlog
def ps.bound(s: Nat, r: Nat, +x: Nat, h: {Nat.is_le(s, r) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, Nat.min(Nat.sub(r, s), x)), r) == True{} : Bool}:
  match s r:
    case 0n 0n:
      {==}
    case 0n 1n+rp:
      ps.min_le_l(1n+rp, x)
    case 1n+sp 0n:
      ps.absurdF({Nat.is_le(Nat.add(1n+sp, Nat.min(Nat.sub(0n, 1n+sp), x)), 0n) == True{} : Bool}, h)
    case 1n+sp 1n+rp:
      ps.bound(sp, rp, x, h)

def ps.step_ahead(+min: Nat, +k: Nat, p: Sc.Pace, e: Sc.PEv, h: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.step(min, k, p, e)), Sc.Pace.recv(Sc.pace.step(min, k, p, e))) == True{} : Bool}:
  match p:
    case Sc.Pace{+r, +s}:
      match e:
        case Sc.Chunk{n}:
          ps.le_add_r(s, r, n, h)
        case Sc.Frame{}:
          ps.bound(s, r, Nat.max(min, Nat.div(Nat.sub(r, s), 1n+k)), h)

def ps.run_ahead(es: List<&2, Sc.PEv>, +min: Nat, +k: Nat, +p: Sc.Pace, h: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, p)), Sc.Pace.recv(Sc.pace.run(es, min, k, p))) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      ps.run_ahead(rest, min, k, Sc.pace.step(min, k, p, e), ps.step_ahead(min, k, p, e, h))

def ps.pace_never_ahead(es: List<&2, Sc.PEv>, +min: Nat, +k: Nat) -> {Nat.is_le(Sc.Pace.shown(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n})), Sc.Pace.recv(Sc.pace.run(es, min, k, Sc.Pace{0n, 0n}))) == True{} : Bool}:
  ps.run_ahead(es, min, k, Sc.Pace{0n, 0n}, {==})

def ps.pace_never_back(+min: Nat, +k: Nat, +p: Sc.Pace, e: Sc.PEv) -> {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.shown(Sc.pace.step(min, k, p, e))) == True{} : Bool}:
  match p:
    case Sc.Pace{+r, +s}:
      match e:
        case Sc.Chunk{n}:
          ps.le_refl(s)
        case Sc.Frame{}:
          ps.le_add_self(s, Sc.reveal(min, k, Nat.sub(r, s)))

# a frame with a positive step takes at least one character off a
# backlog of at most 1 + m
def ps.drop(+b: Nat, +m: Nat, +x: Nat, hb: {Nat.is_le(b, 1n+m) == True{} : Bool}, hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_le(Nat.sub(b, Nat.min(b, x)), m) == True{} : Bool}:
  match b x:
    case 0n _:
      ps.le0(m)
    case 1n+bp 0n:
      ps.absurdF({Nat.is_le(Nat.sub(1n+bp, Nat.min(1n+bp, 0n)), m) == True{} : Bool}, hx)
    case 1n+bp 1n+xp:
      ps.le_trans(Nat.sub(bp, Nat.min(bp, xp)), bp, m, ps.sub_le(bp, Nat.min(bp, xp)), hb)

def ps.drop_after(+r: Nat, +s: Nat, +m: Nat, +x: Nat, hb: {Nat.is_le(Nat.sub(r, s), 1n+m) == True{} : Bool}, hx: {Nat.is_le(1n, x) == True{} : Bool}) -> {Nat.is_le(Nat.sub(r, Nat.add(s, Nat.min(Nat.sub(r, s), x))), m) == True{} : Bool}:
  %ps.sub_sub(r, s, Nat.min(Nat.sub(r, s), x)) : {Nat.is_le(_, m) == True{} : Bool}
  ps.drop(Nat.sub(r, s), m, x, hb, hx)

def ps.drains_go(+n: Nat, +min: Nat, +k: Nat, +p: Sc.Pace, +one: {Nat.is_le(1n, min) == True{} : Bool}, behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}, enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}) -> {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}:
  match n:
    case 0n:
      match p:
        case Sc.Pace{r, s}:
          ps.eq_of(s, r, behind, enough)
    case 1n+m:
      match p:
        case Sc.Pace{+r, +s}:
          +x = Nat.max(min, Nat.div(Nat.sub(r, s), 1n+k))
          ps.drains_go(m, min, k, Sc.Pace{r, Nat.add(s, Nat.min(Nat.sub(r, s), x))}, one, ps.bound(s, r, x, behind), ps.drop_after(r, s, m, x, enough, ps.max_ge(min, Nat.div(Nat.sub(r, s), 1n+k), one)))

def ps.pace_drains(+min: Nat, +k: Nat, +p: Sc.Pace, +n: Nat, one: {Nat.is_le(1n, min) == True{} : Bool}, behind: {Nat.is_le(Sc.Pace.shown(p), Sc.Pace.recv(p)) == True{} : Bool}, enough: {Nat.is_le(Nat.sub(Sc.Pace.recv(p), Sc.Pace.shown(p)), n) == True{} : Bool}) -> {Sc.Pace.shown(Sc.pace.run(Sc.frames(n), min, k, p)) == Sc.Pace.recv(p) : Nat}:
  ps.drains_go(n, min, k, p, one, behind, enough)

# 3. Off-screen verification
# --------------------------

def ps.verify_only_checked(f: Nat, g: Nat, +ok1: Bool, +ok2: Bool) -> {Sc.checked(Sc.present(f, g, ok1, ok2), ok1, ok2) == True{} : Bool}:
  match ok1:
    case True{}:
      {==}
    case False{}:
      match ok2:
        case True{}:
          {==}
        case False{}:
          {==}

# 4. Layout
# ---------

# one child placed at row y ends inside the viewport, or is not shown
def ps.inside_one(+y: Nat, +rows: Nat, +h: Nat) -> {Bool.or(Nat.is_eq(Nat.min(h, Nat.sub(rows, y)), 0n), Nat.is_le(Nat.add(y, Nat.min(h, Nat.sub(rows, y))), rows)) == True{} : Bool}:
  match y rows:
    case 0n 0n:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          {==}
    case 0n 1n+rp:
      ps.or_tr(Nat.is_eq(Nat.min(h, 1n+rp), 0n), Nat.is_le(Nat.min(h, 1n+rp), 1n+rp), ps.min_le_r(h, 1n+rp))
    case 1n+yp 0n:
      match h:
        case 0n:
          {==}
        case 1n+hp:
          {==}
    case 1n+yp 1n+rp:
      ps.inside_one(yp, rp, h)

def ps.layout_inside(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> {Sc.inside(Sc.vstack(hs, y, rows), rows) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +m = Nat.min(h, Nat.sub(rows, y))
      ps.and_t(Bool.or(Nat.is_eq(m, 0n), Nat.is_le(Nat.add(y, m), rows)), Sc.inside(Sc.vstack(rest, Nat.add(y, h), rows), rows), ps.inside_one(y, rows, h), ps.layout_inside(rest, Nat.add(y, h), rows))

# children placed from row y keep apart from any row z at or above y
def ps.apart_go(hs: List<&2, Nat>, +y: Nat, +rows: Nat, +z: Nat, hz: {Nat.is_le(z, y) == True{} : Bool}) -> {Sc.apart(Sc.vstack(hs, y, rows), z) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +m = Nat.min(h, Nat.sub(rows, y))
      ps.and_t(Nat.is_le(z, y), Sc.apart(Sc.vstack(rest, Nat.add(y, h), rows), Nat.add(y, m)), hz, ps.apart_go(rest, Nat.add(y, h), rows, Nat.add(y, m), ps.le_add_l(y, m, h, ps.min_le_l(h, Nat.sub(rows, y)))))

def ps.layout_apart(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> {Sc.apart(Sc.vstack(hs, y, rows), y) == True{} : Bool}:
  ps.apart_go(hs, y, rows, y, ps.le_refl(y))

def ps.ncons(-a: Nat, -b: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>, e1: {a == b : Nat}, e2: {xs == ys : List<&2, Nat>}) -> {a <> xs == b <> ys : List<&2, Nat>}:
  %e1 : {a <> xs == _ <> ys : List<&2, Nat>}
  %e2 : {a <> xs == a <> _ : List<&2, Nat>}
  {==}

def ps.layout_whole_when_room(+hs: List<&2, Nat>, +y: Nat, +rows: Nat, fits: {Nat.is_le(Nat.add(y, Sc.sum(hs)), rows) == True{} : Bool}) -> {Sc.heights(Sc.vstack(hs, y, rows)) == hs : List<&2, Nat>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      +f2 = ps.le_assoc(y, h, Sc.sum(rest), rows, fits)
      +hl = ps.le_sub(y, h, rows, ps.le_addl(Nat.add(y, h), Sc.sum(rest), rows, f2))
      ps.ncons(Nat.min(h, Nat.sub(rows, y)), h, Sc.heights(Sc.vstack(rest, Nat.add(y, h), rows)), rest, ps.min_of_le(h, Nat.sub(rows, y), hl), ps.layout_whole_when_room(rest, Nat.add(y, h), rows, f2))
