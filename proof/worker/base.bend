# eukhe: lemmas the model proofs of area worker share: Bool and Nat facts
# (absurd premises, order of Nats), list and string appends, and the
# model's pick: its selection splits over an append (wb_after_app,
# wb_seqs_app), its cursor is the largest of the old cursor and the seqs
# (wb_top, wb_top_bound, wb_top_in), its body is the spec's (wb_after,
# wb_body).

import Base
import ../../bend/worker.bend as Wk
import ../../laws/worker/forward.bend as WorkerForward

# ---- Bool ----

def wb_if(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def wb_absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : wb_if(_, G)
  Unit{}

# False is not True
def wb_absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  wb_absurd_tf(G, Equal.sym(Bool, False{}, True{}, e))

# ---- Nat order ----

def wb_le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wb_le_refl(p)

def wb_le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wb_le_succ(p)

def wb_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      wb_eq_refl(p)

# a >= b is b <= a
def wb_ge_le(a: Nat, b: Nat) -> {Nat.is_ge(a, b) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wb_ge_le(p, q)

# a > b is b < a
def wb_gt_lt(a: Nat, b: Nat) -> {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wb_gt_lt(p, q)

def wb_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ 0n:
      {==}
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n _:
      wb_absurd_ft({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      wb_absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      wb_le_trans(p, q, r, h1, h2)

# x <= b < y: x < y
def wb_le_lt(x: Nat, b: Nat, y: Nat, h1: {Nat.is_le(x, b) == True{} : Bool}, h2: {Nat.is_lt(b, y) == True{} : Bool}) -> {Nat.is_lt(x, y) == True{} : Bool}:
  match x b y:
    case 0n 0n 0n:
      wb_absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+q 0n:
      wb_absurd_ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n _ 1n+r:
      {==}
    case 1n+p 0n 0n:
      wb_absurd_ft({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      wb_absurd_ft({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h2)
    case 1n+p 0n 1n+r:
      wb_absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, h1)
    case 1n+p 1n+q 1n+r:
      wb_le_lt(p, q, r, h1, h2)

# x < y: x is not y
def wb_lt_ne(x: Nat, y: Nat, h: {Nat.is_lt(x, y) == True{} : Bool}) -> {Nat.is_eq(x, y) == False{} : Bool}:
  match x y:
    case 0n 0n:
      wb_absurd_ft({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 0n 1n+r:
      {==}
    case 1n+p 1n+r:
      wb_lt_ne(p, r, h)

# ---- appends ----

def wb_app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, List.append(&2, A, r, ys), zs), List.append(&2, A, r, List.append(&2, A, ys, zs)), wb_app_assoc(A, r, ys, zs))

def wb_app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, r, Nil{}), r, wb_app_nil(A, r))

def wb_str_nil(s: String) -> {String.append(s, "") == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(r, ""), r, wb_str_nil(r))

def wb_str_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, +r}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(String.append(r, b), c), String.append(r, String.append(b, c)), wb_str_assoc(r, b, c))

# ---- Bool.and, Bool.or ----

def wb_and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def wb_and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      wb_absurd_ft({b == True{} : Bool}, e)

def wb_and_tt(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# a or b holds when b does
def wb_or_r(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# a or b holds: a or (d or b) holds
def wb_or_skip(a: Bool, d: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, Bool.or(d, b)) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      wb_or_r(d, b, h)

# ---- the pick: which messages ----

def wb_put(b: Bool, -m: Wk.UMsg, -r: List<&2, Wk.UMsg>) -> {Wk.after.put(b, m, r) == WorkerForward.fw_new.put(b, m, r) : List<&2, Wk.UMsg>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's messages past the cursor are the spec's
def wb_after(+c: Nat, ms: List<&2, Wk.UMsg>) -> {Wk.after(c, ms) == WorkerForward.fw_new(c, ms) : List<&2, Wk.UMsg>}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +r}:
      match m:
        case Wk.UMsg{+q, +t}:
          %Equal.sym(Bool, Nat.is_gt(q, c), Nat.is_lt(c, q), wb_gt_lt(q, c)) : {Wk.after.put(Nat.is_lt(c, q), Wk.UMsg{q, t}, Wk.after(c, r)) == WorkerForward.fw_new.put(_, Wk.UMsg{q, t}, WorkerForward.fw_new(c, r)) : List<&2, Wk.UMsg>}
          %wb_after(c, r) : {Wk.after.put(Nat.is_lt(c, q), Wk.UMsg{q, t}, Wk.after(c, r)) == WorkerForward.fw_new.put(Nat.is_lt(c, q), Wk.UMsg{q, t}, _) : List<&2, Wk.UMsg>}
          wb_put(Nat.is_lt(c, q), Wk.UMsg{q, t}, Wk.after(c, r))

# a put before an append is the put, then the append
def wb_put_app(b: Bool, -m: Wk.UMsg, -x: List<&2, Wk.UMsg>, -y: List<&2, Wk.UMsg>) -> {Wk.after.put(b, m, List.append(&2, Wk.UMsg, x, y)) == List.append(&2, Wk.UMsg, Wk.after.put(b, m, x), y) : List<&2, Wk.UMsg>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the messages of ms ++ ns past the cursor: those of ms, then those of ns
def wb_after_app(+c: Nat, ms: List<&2, Wk.UMsg>, -ns: List<&2, Wk.UMsg>) -> {Wk.after(c, List.append(&2, Wk.UMsg, ms, ns)) == List.append(&2, Wk.UMsg, Wk.after(c, ms), Wk.after(c, ns)) : List<&2, Wk.UMsg>}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +r}:
      match m:
        case Wk.UMsg{+q, +t}:
          %Equal.sym(List<&2, Wk.UMsg>, Wk.after(c, List.append(&2, Wk.UMsg, r, ns)), List.append(&2, Wk.UMsg, Wk.after(c, r), Wk.after(c, ns)), wb_after_app(c, r, ns)) : {Wk.after.put(Nat.is_lt(c, q), Wk.UMsg{q, t}, _) == List.append(&2, Wk.UMsg, Wk.after.put(Nat.is_lt(c, q), Wk.UMsg{q, t}, Wk.after(c, r)), Wk.after(c, ns)) : List<&2, Wk.UMsg>}
          wb_put_app(Nat.is_lt(c, q), Wk.UMsg{q, t}, Wk.after(c, r), Wk.after(c, ns))

# the seqs of xs ++ ys: those of xs, then those of ys
def wb_seqs_app(xs: List<&2, Wk.UMsg>, -ys: List<&2, Wk.UMsg>) -> {Wk.seqs(List.append(&2, Wk.UMsg, xs, ys)) == List.append(&2, Nat, Wk.seqs(xs), Wk.seqs(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{m, +r}:
      match m:
        case Wk.UMsg{q, t}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => q <> z, Wk.seqs(List.append(&2, Wk.UMsg, r, ys)), List.append(&2, Nat, Wk.seqs(r), Wk.seqs(ys)), wb_seqs_app(r, ys))

# one message: its seq when the put keeps it, none when it does not
def wb_one(b: Bool, -q: Nat, -t: String) -> {Wk.seqs(Wk.after.put(b, Wk.UMsg{q, t}, Nil{})) == WorkerForward.fw_one(b, q) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# every one of ys is above b
def wb_all_gt(ys: List<&2, Nat>, +b: Nat) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{y, r}:
      Bool.and(Nat.is_lt(b, y), wb_all_gt(r, b))

def wb_new_gt.put(+b: Nat, keep: Bool, +q: Nat, -t: String, -r: List<&2, Wk.UMsg>, e: {Nat.is_lt(b, q) == keep : Bool}, ih: {wb_all_gt(Wk.seqs(r), b) == True{} : Bool}) -> {wb_all_gt(Wk.seqs(Wk.after.put(keep, Wk.UMsg{q, t}, r)), b) == True{} : Bool}:
  match keep:
    case True{}:
      wb_and_tt(Nat.is_lt(b, q), wb_all_gt(Wk.seqs(r), b), e, ih)
    case False{}:
      ih

# every seq past the cursor b is above it
def wb_new_gt(+b: Nat, ms: List<&2, Wk.UMsg>) -> {wb_all_gt(Wk.seqs(Wk.after(b, ms)), b) == True{} : Bool}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +r}:
      match m:
        case Wk.UMsg{+q, +t}:
          wb_new_gt.put(b, Nat.is_lt(b, q), q, t, Wk.after(b, r), {==}, wb_new_gt(b, r))

# ---- the pick: the cursor ----

# the largest of the cursor c and the seqs ps (Base Nat.max)
def wb_cursor(ps: List<&2, Nat>, c: Nat) -> Nat:
  match ps:
    case Nil{}:
      c
    case Con{x, r}:
      wb_cursor(r, Nat.max(c, x))

# higher picks the larger: Base's Nat.max
def wb_higher_succ(b: Bool, -x: Nat, -y: Nat) -> {Wk.higher(b, 1n+x, 1n+y) == 1n+Wk.higher(b, x, y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wb_higher_max(a: Nat, b: Nat) -> {Wk.higher(Nat.is_lt(a, b), a, b) == Nat.max(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      Equal.trans(Nat, Wk.higher(Nat.is_lt(p, q), 1n+p, 1n+q), 1n+Wk.higher(Nat.is_lt(p, q), p, q), 1n+Nat.max(p, q),
        wb_higher_succ(Nat.is_lt(p, q), p, q),
        Equal.cong(Nat, Nat, z => 1n+z, Wk.higher(Nat.is_lt(p, q), p, q), Nat.max(p, q), wb_higher_max(p, q)))

# the model's cursor is the largest of c and the seqs
def wb_top(ms: List<&2, Wk.UMsg>, +c: Nat) -> {Wk.top(ms, c) == wb_cursor(Wk.seqs(ms), c) : Nat}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, r}:
      match m:
        case Wk.UMsg{+q, t}:
          +x = Wk.higher(Nat.is_lt(c, q), c, q)
          %wb_higher_max(c, q) : {Wk.top(r, x) == wb_cursor(Wk.seqs(r), _) : Nat}
          wb_top(r, x)

# c is at most the largest
def wb_cursor_ge(ps: List<&2, Nat>, +c: Nat) -> {Nat.is_le(c, wb_cursor(ps, c)) == True{} : Bool}:
  match ps:
    case Nil{}:
      wb_le_refl(c)
    case Con{+x, +r}:
      +m = Nat.max(c, x)
      wb_le_trans(c, m, wb_cursor(r, m),
        Equal.trans(Bool, Nat.is_le(c, m), Nat.is_ge(m, c), True{}, Equal.sym(Bool, Nat.is_ge(m, c), Nat.is_le(c, m), wb_ge_le(m, c)), Nat.max_ge_l(c, x)),
        wb_cursor_ge(r, m))

# every seq the largest saw is at most it
def wb_all_le_cursor(ps: List<&2, Nat>, +c: Nat) -> {WorkerForward.fw_all_le(ps, wb_cursor(ps, c)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +m = Nat.max(c, x)
      wb_and_tt(Nat.is_le(x, wb_cursor(r, m)), WorkerForward.fw_all_le(r, wb_cursor(r, m)),
        wb_le_trans(x, m, wb_cursor(r, m),
          Equal.trans(Bool, Nat.is_le(x, m), Nat.is_ge(m, x), True{}, Equal.sym(Bool, Nat.is_ge(m, x), Nat.is_le(x, m), wb_ge_le(m, x)), Nat.max_ge_r(c, x)),
          wb_cursor_ge(r, m)),
        wb_all_le_cursor(r, m))

# neither c nor any seq of xs is above the model's cursor
def wb_top_bound(+xs: List<&2, Wk.UMsg>, +c: Nat) -> {WorkerForward.fw_all_le(c <> Wk.seqs(xs), Wk.top(xs, c)) == True{} : Bool}:
  +ps = Wk.seqs(xs)
  %Equal.sym(Nat, Wk.top(xs, c), wb_cursor(ps, c), wb_top(xs, c)) : {WorkerForward.fw_all_le(c <> ps, _) == True{} : Bool}
  wb_and_tt(Nat.is_le(c, wb_cursor(ps, c)), WorkerForward.fw_all_le(ps, wb_cursor(ps, c)), wb_cursor_ge(ps, c), wb_all_le_cursor(ps, c))

# x is one of h <> ys, h is c or q (as b picks): x is one of c <> q <> ys
def wb_in_step(b: Bool, +x: Nat, +c: Nat, +q: Nat, +ys: List<&2, Nat>, h: {WorkerForward.fw_in(x, Wk.higher(b, c, q) <> ys) == True{} : Bool}) -> {WorkerForward.fw_in(x, c <> q <> ys) == True{} : Bool}:
  match b:
    case True{}:
      wb_or_r(Nat.is_eq(x, c), WorkerForward.fw_in(x, q <> ys), h)
    case False{}:
      wb_or_skip(Nat.is_eq(x, c), Nat.is_eq(x, q), WorkerForward.fw_in(x, ys), h)

# the model's cursor is c or one of the seqs of xs
def wb_top_in(xs: List<&2, Wk.UMsg>, +c: Nat) -> {WorkerForward.fw_in(Wk.top(xs, c), c <> Wk.seqs(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(c, c), True{}, wb_eq_refl(c)) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case Con{m, +r}:
      match m:
        case Wk.UMsg{+q, t}:
          +x = Wk.higher(Nat.is_lt(c, q), c, q)
          wb_in_step(Nat.is_lt(c, q), Wk.top(r, x), c, q, Wk.seqs(r), wb_top_in(r, x))

# ---- the pick: no seq twice ----

# x <= b and every y of ys > b: x is none of ys
def wb_not_in(+x: Nat, +b: Nat, ys: List<&2, Nat>, hx: {Nat.is_le(x, b) == True{} : Bool}, hy: {wb_all_gt(ys, b) == True{} : Bool}) -> {WorkerForward.fw_in(x, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +r}:
      +hh = hy
      +hxx = hx
      %Equal.sym(Bool, Nat.is_eq(x, y), False{}, wb_lt_ne(x, y, wb_le_lt(x, b, y, hxx, wb_and_l(Nat.is_lt(b, y), wb_all_gt(r, b), hh)))) : {Bool.or(_, WorkerForward.fw_in(x, r)) == False{} : Bool}
      wb_not_in(x, b, r, hxx, wb_and_r(Nat.is_lt(b, y), wb_all_gt(r, b), hh))

# every x <= b, every y > b: none in common
def wb_disjoint(xs: List<&2, Nat>, +b: Nat, +ys: List<&2, Nat>, hx: {WorkerForward.fw_all_le(xs, b) == True{} : Bool}, hy: {wb_all_gt(ys, b) == True{} : Bool}) -> {WorkerForward.fw_disjoint(xs, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      +hh = hx
      +hyy = hy
      %Equal.sym(Bool, WorkerForward.fw_in(x, ys), False{}, wb_not_in(x, b, ys, wb_and_l(Nat.is_le(x, b), WorkerForward.fw_all_le(r, b), hh), hyy)) : {Bool.and(Bool.not(_), WorkerForward.fw_disjoint(r, ys)) == True{} : Bool}
      wb_disjoint(r, b, ys, wb_and_r(Nat.is_le(x, b), WorkerForward.fw_all_le(r, b), hh), hyy)

# ---- the pick: the text ----

# the texts after a first one, without a note, are Base's join
def wb_more_none(ms: List<&2, Wk.UMsg>, +h: String) -> {String.append(h, Wk.body.more(ms, None{})) == String.join.go(WorkerForward.fw_texts(ms), h, "\n\n") : String}:
  match ms:
    case Nil{}:
      wb_str_nil(h)
    case Con{Wk.UMsg{q, +t}, +r}:
      Equal.cong(String, String, z => String.append(h, String.append("\n\n", z)), String.append(t, Wk.body.more(r, None{})), String.join.go(WorkerForward.fw_texts(r), t, "\n\n"), wb_more_none(r, t))

# ... and with a note n, the join then the note after a blank line
def wb_more_some(ms: List<&2, Wk.UMsg>, +h: String, +n: String) -> {String.append(h, Wk.body.more(ms, Some{n})) == String.append(String.join.go(WorkerForward.fw_texts(ms), h, "\n\n"), String.append("\n\n[note from main] ", n)) : String}:
  match ms:
    case Nil{}:
      {==}
    case Con{Wk.UMsg{q, +t}, +r}:
      +j = String.join.go(WorkerForward.fw_texts(r), t, "\n\n")
      +nn = String.append("\n\n[note from main] ", n)
      %Equal.sym(String, String.append(t, Wk.body.more(r, Some{n})), String.append(j, nn), wb_more_some(r, t, n)) : {String.append(h, String.append("\n\n", _)) == String.append(String.append(h, String.append("\n\n", j)), nn) : String}
      Equal.sym(String, String.append(String.append(h, String.append("\n\n", j)), nn), String.append(h, String.append(String.append("\n\n", j), nn)), wb_str_assoc(h, String.append("\n\n", j), nn))

# the model's body is the spec's
def wb_body(ms: List<&2, Wk.UMsg>, note: Maybe<&2, String>) -> {Wk.body(ms, note) == WorkerForward.fw_body(WorkerForward.fw_texts(ms), note) : String}:
  match ms note:
    case Nil{} None{}:
      {==}
    case Nil{} Some{n}:
      {==}
    case Con{Wk.UMsg{q, t}, r} None{}:
      wb_more_none(r, t)
    case Con{Wk.UMsg{q, t}, r} Some{n}:
      wb_more_some(r, t, n)
