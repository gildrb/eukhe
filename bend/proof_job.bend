# proof_job: the S2 laws (docs/harness.md) of the job model in
# bend/job.bend: output caps and drops, one end per job, ended jobs stay
# ended, a blocking call never outlives its budget, a tool call's stream
# journals one final record carrying everything, and a rewind stops
# exactly the orphan jobs. Each job lemma speaks of a job at any state,
# by induction on the events it sees.

import Base
import ./job.bend as Jb

# Logic
# -----

def pj.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pj.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pj.BD(_, A, Unit)
  Unit{}

def pj.beq_refl(r: Bool) -> {True{} == Jb.b.eq(r, r) : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def pj.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pj.eq_refl(p)

# Arithmetic
# ----------

def pj.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pj.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pj.le_refl(p)

def pj.add_zero(x: Nat) -> {x == Nat.add(x, 0n) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def pj.add_succ(a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_succ(p, b) : {1n+1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def pj.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def pj.swap(+x: Nat, +y: Nat, +s: Nat) -> {Nat.add(x, Nat.add(y, s)) == Nat.add(y, Nat.add(x, s)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %pj.add_succ(y, Nat.add(p, s)) : {1n+Nat.add(p, Nat.add(y, s)) == _ : Nat}
      %pj.swap(p, y, s) : {1n+Nat.add(p, Nat.add(y, s)) == 1n+_ : Nat}
      {==}

def pj.swap4(k: Nat, +t: Nat, +d: Nat, +s: Nat) -> {Nat.add(Nat.add(k, d), Nat.add(t, s)) == Nat.add(Nat.add(k, t), Nat.add(d, s)) : Nat}:
  match k:
    case 0n:
      pj.swap(d, t, s)
    case 1n+p:
      %pj.swap4(p, t, d, s) : {1n+Nat.add(Nat.add(p, d), Nat.add(t, s)) == 1n+_ : Nat}
      {==}

def pj.sub_zero(c: Nat) -> {c == Nat.sub(c, 0n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pj.sub_self(n: Nat) -> {0n == Nat.sub(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pj.sub_self(p)

def pj.sub_sub(c: Nat, k: Nat, +n: Nat) -> {Nat.sub(Nat.sub(c, k), n) == Nat.sub(c, Nat.add(k, n)) : Nat}:
  match c k:
    case 0n _:
      {==}
    case 1n+cp 0n:
      {==}
    case 1n+cp 1n+kp:
      pj.sub_sub(cp, kp, n)

def pj.add_sub(t: Nat, n: Nat, le: {Nat.is_le(t, n) == True{} : Bool}) -> {n == Nat.add(t, Nat.sub(n, t)) : Nat}:
  match t n:
    case 0n _:
      pj.sub_zero(n)
    case 1n+tp 0n:
      pj.absurdF({0n == Nat.add(1n+tp, Nat.sub(0n, 1n+tp)) : Nat}, le)
    case 1n+tp 1n+np:
      %pj.add_sub(tp, np, le) : {1n+np == 1n+_ : Nat}
      {==}

def pj.min_le_l(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), n) == True{} : Bool}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      pj.min_le_l(np, mp)

def pj.min_le_r(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n m:
    case 0n _:
      pj.le0(m)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      pj.min_le_r(np, mp)

def pj.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {n == Nat.min(n, m) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      pj.absurdF({1n+np == Nat.min(1n+np, 0n) : Nat}, h)
    case 1n+np 1n+mp:
      %pj.min_of_le(np, mp, h) : {1n+np == 1n+_ : Nat}
      {==}

def pj.le_addl(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(n, m) == True{} : Bool}:
  match n m:
    case 0n _:
      pj.le0(m)
    case 1n+np 0n:
      pj.absurdF({Nat.is_le(1n+np, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      pj.le_addl(np, p, mp, h)

def pj.le_sub(n: Nat, +p: Nat, m: Nat, h: {Nat.is_le(Nat.add(n, p), m) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(m, n)) == True{} : Bool}:
  match n m:
    case 0n 0n:
      h
    case 0n 1n+mp:
      h
    case 1n+np 0n:
      pj.absurdF({Nat.is_le(p, 0n) == True{} : Bool}, h)
    case 1n+np 1n+mp:
      pj.le_sub(np, p, mp, h)

# a kept count under the cap stays under it after any output
def pj.bound(k: Nat, c: Nat, +n: Nat, h: {Nat.is_le(k, c) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, Nat.min(n, Nat.sub(c, k))), c) == True{} : Bool}:
  match k c:
    case 0n 0n:
      pj.min_le_r(n, 0n)
    case 0n 1n+cp:
      pj.min_le_r(n, 1n+cp)
    case 1n+kp 0n:
      pj.absurdF({Nat.is_le(Nat.add(1n+kp, Nat.min(n, Nat.sub(0n, 1n+kp))), 0n) == True{} : Bool}, h)
    case 1n+kp 1n+cp:
      pj.bound(kp, cp, n, h)

def pj.take_le(cap: Maybe<&2, Nat>, +k: Nat, +n: Nat) -> {Nat.is_le(Jb.take(cap, k, n), n) == True{} : Bool}:
  match cap:
    case None{}:
      pj.le_refl(n)
    case Some{c}:
      pj.min_le_l(n, Nat.sub(c, k))

# an output of n bytes adds n to the bytes kept plus dropped
def pj.split(+k: Nat, +d: Nat, +t: Nat, +n: Nat, le: {Nat.is_le(t, n) == True{} : Bool}) -> {Nat.add(Nat.add(k, d), n) == Nat.add(Nat.add(k, t), Nat.add(d, Nat.sub(n, t))) : Nat}:
  %pj.swap4(k, t, d, Nat.sub(n, t)) : {Nat.add(Nat.add(k, d), n) == _ : Nat}
  %pj.add_sub(t, n, le) : {Nat.add(Nat.add(k, d), n) == Nat.add(Nat.add(k, d), _) : Nat}
  {==}

# the room left under the cap shrinks by the output that fits
def pj.fit_room(+c: Nat, +k: Nat, +n: Nat, +p: Nat, h: {Nat.is_le(Nat.add(n, p), Nat.sub(c, k)) == True{} : Bool}) -> {Nat.is_le(p, Nat.sub(c, Nat.add(k, n))) == True{} : Bool}:
  %pj.sub_sub(c, k, n) : {Nat.is_le(p, _) == True{} : Bool}
  pj.le_sub(n, p, Nat.sub(c, k), h)

def pj.room0(+c: Nat, -es: List<&2, Jb.JEv>, fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}) -> {Nat.is_le(Jb.produced(es), Nat.sub(c, 0n)) == True{} : Bool}:
  %pj.sub_zero(c) : {Nat.is_le(Jb.produced(es), _) == True{} : Bool}
  fits

# Jobs
# ----

# an ended job stays as it ended
def pj.ended(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Jb.Ended{k, d, x} == Jb.go(es, cap, Jb.Ended{k, d, x}) : Jb.J}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.ended(rest, cap, k, d, x)

# an ended job reports no more ends
def pj.ends_ended(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Nil{} == Jb.ends.go(es, cap, Jb.Ended{k, d, x}) : List<&2, Jb.End>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.ends_ended(rest, cap, k, d, x)

def pj.same(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End) -> {Jb.go(xs, cap, Jb.Ended{k, d, x}) == Jb.go(ys, cap, Jb.Ended{k, d, x}) : Jb.J}:
  %pj.ended(xs, cap, k, d, x) : {_ == Jb.go(ys, cap, Jb.Ended{k, d, x}) : Jb.J}
  pj.ended(ys, cap, k, d, x)

def pj.quit_end(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, j: Jb.J, +q: Nat) -> {Jb.go(xs, cap, Jb.step(cap, j, Jb.Quit{q})) == Jb.go(ys, cap, Jb.step(cap, j, Jb.Quit{q})) : Jb.J}:
  match j:
    case Jb.Live{k, d}:
      pj.same(xs, ys, cap, k, d, Jb.Exited{q})
    case Jb.Ended{k, d, x}:
      pj.same(xs, ys, cap, k, d, x)

def pj.kill_end(+xs: List<&2, Jb.JEv>, +ys: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, j: Jb.J) -> {Jb.go(xs, cap, Jb.step(cap, j, Jb.Kill{})) == Jb.go(ys, cap, Jb.step(cap, j, Jb.Kill{})) : Jb.J}:
  match j:
    case Jb.Live{k, d}:
      pj.same(xs, ys, cap, k, d, Jb.Killed{})
    case Jb.Ended{k, d, x}:
      pj.same(xs, ys, cap, k, d, x)

# once a prefix holds an end, the rest changes nothing
def pj.final(pre: List<&2, Jb.JEv>, post: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +j: Jb.J, h: {Jb.has_end(pre) == True{} : Bool}) -> {Jb.go(List.append(&2, Jb.JEv, pre, post), cap, j) == Jb.go(pre, cap, j) : Jb.J}:
  match pre:
    case Nil{}:
      pj.absurdF({Jb.go(post, cap, j) == j : Jb.J}, h)
    case e <> +rest:
      match e:
        case Jb.Out{n}:
          pj.final(rest, post, cap, Jb.step(cap, j, Jb.Out{n}), h)
        case Jb.Quit{q}:
          pj.quit_end(List.append(&2, Jb.JEv, rest, post), rest, cap, j, q)
        case Jb.Kill{}:
          pj.kill_end(List.append(&2, Jb.JEv, rest, post), rest, cap, j)
        case Jb.Tick{}:
          pj.final(rest, post, cap, Jb.step(cap, j, Jb.Tick{}), h)

# one step keeps the kept bytes under the cap
def pj.step_bd(+c: Nat, j: Jb.J, e: Jb.JEv, h: {Nat.is_le(Jb.J.kept(j), c) == True{} : Bool}) -> {Nat.is_le(Jb.J.kept(Jb.step(Some{c}, j, e)), c) == True{} : Bool}:
  match j:
    case Jb.Live{+k, d}:
      match e:
        case Jb.Out{+n}:
          pj.bound(k, c, n, h)
        case Jb.Quit{q}:
          h
        case Jb.Kill{}:
          h
        case Jb.Tick{}:
          h
    case Jb.Ended{k, d, x}:
      h

def pj.bounded(es: List<&2, Jb.JEv>, +c: Nat, +j: Jb.J, h: {Nat.is_le(Jb.J.kept(j), c) == True{} : Bool}) -> {Nat.is_le(Jb.J.kept(Jb.go(es, Some{c}, j)), c) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      pj.bounded(rest, c, Jb.step(Some{c}, j, e), pj.step_bd(c, j, e, h))

# the bytes kept plus dropped grow by every byte written before the end
def pj.loss(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {Nat.add(Nat.add(k, d), Jb.produced(es)) == Nat.add(Jb.J.kept(Jb.go(es, cap, Jb.Live{k, d})), Jb.J.dropped(Jb.go(es, cap, Jb.Live{k, d}))) : Nat}:
  match es:
    case Nil{}:
      %pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          +t = Jb.take(cap, k, n)
          +p = Jb.produced(rest)
          %pj.loss(rest, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t))) : {Nat.add(Nat.add(k, d), Nat.add(n, p)) == _ : Nat}
          %pj.split(k, d, t, n, pj.take_le(cap, k, n)) : {Nat.add(Nat.add(k, d), Nat.add(n, p)) == Nat.add(_, p) : Nat}
          %pj.add_assoc(Nat.add(k, d), n, p) : {_ == Nat.add(Nat.add(Nat.add(k, d), n), p) : Nat}
          {==}
        case Jb.Quit{q}:
          %pj.ended(rest, cap, k, d, Jb.Exited{q}) : {Nat.add(Nat.add(k, d), 0n) == Nat.add(Jb.J.kept(_), Jb.J.dropped(_)) : Nat}
          %pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
          {==}
        case Jb.Kill{}:
          %pj.ended(rest, cap, k, d, Jb.Killed{}) : {Nat.add(Nat.add(k, d), 0n) == Nat.add(Jb.J.kept(_), Jb.J.dropped(_)) : Nat}
          %pj.add_zero(Nat.add(k, d)) : {_ == Nat.add(k, d) : Nat}
          {==}
        case Jb.Tick{}:
          pj.loss(rest, cap, k, d)

# with the opt-out, nothing is dropped
def pj.optout(es: List<&2, Jb.JEv>, +k: Nat) -> {Jb.J.dropped(Jb.go(es, None{}, Jb.Live{k, 0n})) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          %pj.sub_self(n) : {Jb.J.dropped(Jb.go(rest, None{}, Jb.Live{Nat.add(k, n), _})) == 0n : Nat}
          pj.optout(rest, Nat.add(k, n))
        case Jb.Quit{q}:
          %pj.ended(rest, None{}, k, 0n, Jb.Exited{q}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Kill{}:
          %pj.ended(rest, None{}, k, 0n, Jb.Killed{}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Tick{}:
          pj.optout(rest, k)

# output that fits the room left under the cap drops nothing
def pj.fit(es: List<&2, Jb.JEv>, +c: Nat, +k: Nat, +h: {Nat.is_le(Jb.produced(es), Nat.sub(c, k)) == True{} : Bool}) -> {Jb.J.dropped(Jb.go(es, Some{c}, Jb.Live{k, 0n})) == 0n : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          %pj.min_of_le(n, Nat.sub(c, k), pj.le_addl(n, Jb.produced(rest), Nat.sub(c, k), h)) : {Jb.J.dropped(Jb.go(rest, Some{c}, Jb.Live{Nat.add(k, _), Nat.sub(n, _)})) == 0n : Nat}
          %pj.sub_self(n) : {Jb.J.dropped(Jb.go(rest, Some{c}, Jb.Live{Nat.add(k, n), _})) == 0n : Nat}
          pj.fit(rest, c, Nat.add(k, n), pj.fit_room(c, k, n, Jb.produced(rest), h))
        case Jb.Quit{q}:
          %pj.ended(rest, Some{c}, k, 0n, Jb.Exited{q}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Kill{}:
          %pj.ended(rest, Some{c}, k, 0n, Jb.Killed{}) : {Jb.J.dropped(_) == 0n : Nat}
          {==}
        case Jb.Tick{}:
          pj.fit(rest, c, k, h)

# a live job reports one end iff its events hold one
def pj.once(es: List<&2, Jb.JEv>, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {List.length(&2, Jb.End, Jb.ends.go(es, cap, Jb.Live{k, d})) == Jb.once(Jb.has_end(es)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          +t = Jb.take(cap, k, n)
          pj.once(rest, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t)))
        case Jb.Quit{q}:
          %pj.ends_ended(rest, cap, k, d, Jb.Exited{q}) : {1n+List.length(&2, Jb.End, _) == 1n : Nat}
          {==}
        case Jb.Kill{}:
          %pj.ends_ended(rest, cap, k, d, Jb.Killed{}) : {1n+List.length(&2, Jb.End, _) == 1n : Nat}
          {==}
        case Jb.Tick{}:
          pj.once(rest, cap, k, d)

# Blocking calls
# --------------

def pj.blocks(es: List<&2, Jb.JEv>, +b: Nat, long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}) -> {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}:
  match es:
    case Nil{}:
      match b:
        case 0n:
          {==}
        case 1n+l:
          pj.absurdF({Maybe.is_some(&2, Jb.Wait, Jb.wait(Nil{}, 1n+l)) == True{} : Bool}, long)
    case e <> rest:
      match e:
        case Jb.Out{n}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              pj.blocks(rest, 1n+l, long)
        case Jb.Quit{q}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              {==}
        case Jb.Kill{}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              {==}
        case Jb.Tick{}:
          match b:
            case 0n:
              {==}
            case 1n+l:
              pj.blocks(rest, l, long)

def pj.is_settled(m: Maybe<&2, Jb.Wait>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      match w:
        case Jb.Settled{x}:
          True{}
        case Jb.Detached{}:
          False{}

def pj.end_of(m: Maybe<&2, Jb.Wait>) -> Jb.End:
  match m:
    case None{}:
      Jb.Killed{}
    case Some{w}:
      match w:
        case Jb.Settled{x}:
          x
        case Jb.Detached{}:
          Jb.Killed{}

# an answer that settled is a settle
def pj.settled(-m: Maybe<&2, Jb.Wait>, -x: Jb.End, s: {m == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {pj.is_settled(m) == True{} : Bool}:
  Equal.cong(Maybe<&2, Jb.Wait>, Bool, w => pj.is_settled(w), m, Some{Jb.Settled{x}}, s)

# an answer that settled carries its end
def pj.end_eq(-m: Maybe<&2, Jb.Wait>, -x: Jb.End, s: {m == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {pj.end_of(m) == x : Jb.End}:
  Equal.cong(Maybe<&2, Jb.Wait>, Jb.End, w => pj.end_of(w), m, Some{Jb.Settled{x}}, s)

def pj.settle(es: List<&2, Jb.JEv>, +b: Nat, +cap: Maybe<&2, Nat>, +k: Nat, +d: Nat, +x: Jb.End, s: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {Jb.ends.go(es, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}:
  match es:
    case Nil{}:
      match b:
        case 0n:
          pj.absurdF({Nil{} == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
        case 1n+l:
          pj.absurdF({Nil{} == [x] : List<&2, Jb.End>}, pj.settled(None{}, x, s))
    case e <> +rest:
      match e:
        case Jb.Out{+n}:
          match b:
            case 0n:
              pj.absurdF({Jb.ends.go(Jb.Out{n} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              +t = Jb.take(cap, k, n)
              pj.settle(rest, 1n+l, cap, Nat.add(k, t), Nat.add(d, Nat.sub(n, t)), x, s)
        case Jb.Quit{+q}:
          match b:
            case 0n:
              pj.absurdF({Jb.ends.go(Jb.Quit{q} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              %pj.ends_ended(rest, cap, k, d, Jb.Exited{q}) : {Jb.Exited{q} <> _ == [x] : List<&2, Jb.End>}
              %pj.end_eq(Some{Jb.Settled{Jb.Exited{q}}}, x, s) : {[Jb.Exited{q}] == [_] : List<&2, Jb.End>}
              {==}
        case Jb.Kill{}:
          match b:
            case 0n:
              pj.absurdF({Jb.ends.go(Jb.Kill{} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              %pj.ends_ended(rest, cap, k, d, Jb.Killed{}) : {Jb.Killed{} <> _ == [x] : List<&2, Jb.End>}
              %pj.end_eq(Some{Jb.Settled{Jb.Killed{}}}, x, s) : {[Jb.Killed{}] == [_] : List<&2, Jb.End>}
              {==}
        case Jb.Tick{}:
          match b:
            case 0n:
              pj.absurdF({Jb.ends.go(Jb.Tick{} <> rest, cap, Jb.Live{k, d}) == [x] : List<&2, Jb.End>}, pj.settled(Some{Jb.Detached{}}, x, s))
            case 1n+l:
              pj.settle(rest, l, cap, k, d, x, s)

# Streams
# -------

# a settled call journals nothing more
def pj.cshut(es: List<&2, Jb.CEv>) -> {Nil{} == Jb.c.go(es, Jb.Shut{}) : List<&2, Jb.CRec>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      pj.cshut(rest)

def pj.two(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat) -> {Nat.is_le(List.length(&2, Jb.CRec, Jb.c.go(es, Jb.Open{b, w, u})), 1n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Delta{n}:
          pj.two(rest, Nat.add(b, n), w, u)
        case Jb.Warn{}:
          pj.two(rest, b, 1n+w, u)
        case Jb.Use{n}:
          pj.two(rest, b, w, Nat.add(u, n))
        case Jb.Final{}:
          %pj.cshut(rest) : {Nat.is_le(1n+List.length(&2, Jb.CRec, _), 1n) == True{} : Bool}
          {==}
        case Jb.Cancel{}:
          %pj.cshut(rest) : {Nat.is_le(1n+List.length(&2, Jb.CRec, _), 1n) == True{} : Bool}
          {==}

def pj.sett(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat) -> {Jb.settles(Jb.c.go(es, Jb.Open{b, w, u})) == Jb.once(Jb.c.ends(es)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Jb.Delta{n}:
          pj.sett(rest, Nat.add(b, n), w, u)
        case Jb.Warn{}:
          pj.sett(rest, b, 1n+w, u)
        case Jb.Use{n}:
          pj.sett(rest, b, w, Nat.add(u, n))
        case Jb.Final{}:
          %pj.cshut(rest) : {1n+Jb.settles(_) == 1n : Nat}
          {==}
        case Jb.Cancel{}:
          %pj.cshut(rest) : {1n+Jb.settles(_) == 1n : Nat}
          {==}

def pj.carry(es: List<&2, Jb.CEv>, +b: Nat, +w: Nat, +u: Nat, h: {Jb.c.ends(es) == True{} : Bool}) -> {Jb.carried(Jb.c.go(es, Jb.Open{b, w, u})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(es)), Nat.add(w, Jb.c.warns(es)), Nat.add(u, Jb.c.usage(es))}} : Maybe<&2, Jb.Tally>}:
  match es:
    case Nil{}:
      pj.absurdF({Jb.carried(Nil{}) == Some{Jb.Tally{Nat.add(b, 0n), Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}, h)
    case e <> +rest:
      match e:
        case Jb.Delta{+n}:
          %pj.add_assoc(b, n, Jb.c.bytes(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{Nat.add(b, n), w, u})) == Some{Jb.Tally{_, Nat.add(w, Jb.c.warns(rest)), Nat.add(u, Jb.c.usage(rest))}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, Nat.add(b, n), w, u, h)
        case Jb.Warn{}:
          %pj.add_succ(w, Jb.c.warns(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{b, 1n+w, u})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(rest)), _, Nat.add(u, Jb.c.usage(rest))}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, b, 1n+w, u, h)
        case Jb.Use{+n}:
          %pj.add_assoc(u, n, Jb.c.usage(rest)) : {Jb.carried(Jb.c.go(rest, Jb.Open{b, w, Nat.add(u, n)})) == Some{Jb.Tally{Nat.add(b, Jb.c.bytes(rest)), Nat.add(w, Jb.c.warns(rest)), _}} : Maybe<&2, Jb.Tally>}
          pj.carry(rest, b, w, Nat.add(u, n), h)
        case Jb.Final{}:
          %pj.add_zero(b) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{_, Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %pj.add_zero(w) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, _, Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %pj.add_zero(u) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, w, _}} : Maybe<&2, Jb.Tally>}
          {==}
        case Jb.Cancel{}:
          %pj.add_zero(b) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{_, Nat.add(w, 0n), Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %pj.add_zero(w) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, _, Nat.add(u, 0n)}} : Maybe<&2, Jb.Tally>}
          %pj.add_zero(u) : {Some{Jb.Tally{b, w, u}} == Some{Jb.Tally{b, w, _}} : Maybe<&2, Jb.Tally>}
          {==}

# Rewinds
# -------

def pj.id_stop(h: Bool, +i: Nat, +r: Bool) -> {i == Jb.Slot.id(Jb.stop.at(h, Jb.Slot{i, r})) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def pj.ok_run(h: Bool, +i: Nat, r: Bool) -> {True{} == Bool.or(Bool.not(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r}))), h) : Bool}:
  match h:
    case True{}:
      match r:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def pj.ok_keep(h: Bool, +i: Nat, +r: Bool) -> {True{} == Bool.or(Bool.not(h), Bool.and(Nat.is_eq(i, i), Jb.b.eq(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r})), r))) : Bool}:
  match h:
    case True{}:
      %pj.eq_refl(i) : {True{} == Bool.and(_, Jb.b.eq(r, r)) : Bool}
      pj.beq_refl(r)
    case False{}:
      {==}

def pj.stops(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Jb.Slot{+i, +r}:
          +h = Jb.elem(keep, i)
          %pj.id_stop(h, i, r) : {Bool.and(Bool.or(Bool.not(Jb.Slot.running(Jb.stop.at(h, Jb.Slot{i, r}))), Jb.elem(keep, _)), Jb.running_in(Jb.rewind(rest, keep), keep)) == True{} : Bool}
          %pj.ok_run(h, i, r) : {Bool.and(_, Jb.running_in(Jb.rewind(rest, keep), keep)) == True{} : Bool}
          pj.stops(rest, keep)

def pj.keeps(js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}:
  match js:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Jb.Slot{+i, +r}:
          +h = Jb.elem(keep, i)
          +S = Jb.stop.at(h, Jb.Slot{i, r})
          %pj.id_stop(h, i, r) : {Bool.and(Bool.or(Bool.not(Jb.elem(keep, _)), Bool.and(Nat.is_eq(_, i), Jb.b.eq(Jb.Slot.running(S), r))), Jb.kept(Jb.rewind(rest, keep), rest, keep)) == True{} : Bool}
          %pj.ok_keep(h, i, r) : {Bool.and(_, Jb.kept(Jb.rewind(rest, keep), rest, keep)) == True{} : Bool}
          pj.keeps(rest, keep)

# The laws
# --------

def pj.job_output_bounded(+c: Nat, es: List<&2, Jb.JEv>) -> {Nat.is_le(Jb.J.kept(Jb.run(Some{c}, es)), c) == True{} : Bool}:
  pj.bounded(es, c, Jb.Live{0n, 0n}, pj.le0(c))

def pj.job_no_silent_loss(+cap: Maybe<&2, Nat>, +es: List<&2, Jb.JEv>) -> {Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))) == Jb.produced(es) : Nat}:
  Equal.sym(Nat, Jb.produced(es), Nat.add(Jb.J.kept(Jb.run(cap, es)), Jb.J.dropped(Jb.run(cap, es))), pj.loss(es, cap, 0n, 0n))

def pj.job_optout_keeps_all(es: List<&2, Jb.JEv>) -> {Jb.J.dropped(Jb.run(None{}, es)) == 0n : Nat}:
  pj.optout(es, 0n)

def pj.job_cap_drops_only_excess(+c: Nat, +es: List<&2, Jb.JEv>, fits: {Nat.is_le(Jb.produced(es), c) == True{} : Bool}) -> {Jb.J.dropped(Jb.run(Some{c}, es)) == 0n : Nat}:
  pj.fit(es, c, 0n, pj.room0(c, es, fits))

def pj.job_ends_once(+cap: Maybe<&2, Nat>, +es: List<&2, Jb.JEv>) -> {List.length(&2, Jb.End, Jb.ends(cap, es)) == Jb.once(Jb.has_end(es)) : Nat}:
  pj.once(es, cap, 0n, 0n)

def pj.job_end_is_final(+cap: Maybe<&2, Nat>, +pre: List<&2, Jb.JEv>, post: List<&2, Jb.JEv>, ended: {Jb.has_end(pre) == True{} : Bool}) -> {Jb.run(cap, List.append(&2, Jb.JEv, pre, post)) == Jb.run(cap, pre) : Jb.J}:
  pj.final(pre, post, cap, Jb.Live{0n, 0n}, ended)

def pj.job_kill_ends_now(+cap: Maybe<&2, Nat>, +k: Nat, +d: Nat) -> {Jb.step(cap, Jb.Live{k, d}, Jb.Kill{}) == Jb.Ended{k, d, Jb.Killed{}} : Jb.J}:
  {==}

def pj.call_blocks_at_most_budget(+b: Nat, +es: List<&2, Jb.JEv>, long: {Nat.is_le(b, Jb.ticks(es)) == True{} : Bool}) -> {Maybe.is_some(&2, Jb.Wait, Jb.wait(es, b)) == True{} : Bool}:
  pj.blocks(es, b, long)

def pj.call_settles_with_job(+cap: Maybe<&2, Nat>, +b: Nat, +es: List<&2, Jb.JEv>, +x: Jb.End, settled: {Jb.wait(es, b) == Some{Jb.Settled{x}} : Maybe<&2, Jb.Wait>}) -> {Jb.ends(cap, es) == [x] : List<&2, Jb.End>}:
  pj.settle(es, b, cap, 0n, 0n, x, settled)

def pj.stream_journals_two(es: List<&2, Jb.CEv>) -> {Nat.is_le(List.length(&2, Jb.CRec, Jb.journal(es)), 2n) == True{} : Bool}:
  pj.two(es, 0n, 0n, 0n)

def pj.stream_settles_once(+es: List<&2, Jb.CEv>) -> {Jb.settles(Jb.journal(es)) == Jb.once(Jb.c.ends(es)) : Nat}:
  pj.sett(es, 0n, 0n, 0n)

def pj.stream_settle_carries_all(+es: List<&2, Jb.CEv>, ended: {Jb.c.ends(es) == True{} : Bool}) -> {Jb.carried(Jb.journal(es)) == Some{Jb.Tally{Jb.c.bytes(es), Jb.c.warns(es), Jb.c.usage(es)}} : Maybe<&2, Jb.Tally>}:
  pj.carry(es, 0n, 0n, 0n, ended)

def pj.rewind_stops_orphans(+js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.running_in(Jb.rewind(js, keep), keep) == True{} : Bool}:
  pj.stops(js, keep)

def pj.rewind_keeps_target_jobs(+js: List<&2, Jb.Slot>, +keep: List<&2, Nat>) -> {Jb.kept(Jb.rewind(js, keep), js, keep) == True{} : Bool}:
  pj.keeps(js, keep)
