# eukhe: lemmas of the model proofs of area context_order
#
# The order: the window of an assistant picked per call is the spec's
# first result (co.pick_window), so the code's order is the spec's
# (co.order). The split identity: a window never reaches past an
# assistant (co.win_app), so ordering a ++ b orders a, then b at offset
# |a| (co.order_app); an offset shifts every index (co.order_shift). The
# plan, the lead, the contributions, derive and extend: the code's
# functions against the spec's, one by one.

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder

# ---- logic ----

def co.BT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def co.tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : co.BT(_, G)
  Unit{}

def co.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def co.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      co.tf({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def co.and_tt(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

def co.BF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def co.ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : co.BF(_, G)
  Unit{}

def co.add_s(n: Nat, -i: Nat) -> {Nat.add(n, 1n+i) == 1n+Nat.add(n, i) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+i), 1n+Nat.add(p, i), co.add_s(p, i))

def co.add_z(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, co.add_z(p))

def co.app_assoc(-A: Data, xs: List<&2, A>, -ys: List<&2, A>, -zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(List<&2, A>, List<&2, A>, z => x <> z, List.append(&2, A, List.append(&2, A, t, ys), zs), List.append(&2, A, t, List.append(&2, A, ys, zs)), co.app_assoc(A, t, ys, zs))

# ---- the order ----

def co.pw.sel(b: Bool, -k: Nat, -x: Maybe<&2, Nat>, -y: Maybe<&2, Nat>, e: {x == y : Maybe<&2, Nat>}) -> {Co.pick.sel(b, k, x) == ContextOrder.first_res.hit(b, k, y) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

# the first hit of the window is the spec's first result
def co.pick_window(t: List<&2, Co.Msg>, +k: Nat, +c: Nat) -> {Co.pick(Co.window(t, k), c) == ContextOrder.first_res(t, k, c) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          co.pick_window(u, 1n+k, c)
        case Co.MSystem{}:
          co.pick_window(u, 1n+k, c)
        case Co.MAsst{s, cs}:
          {==}
        case Co.MRes{d}:
          co.pw.sel(Nat.is_eq(d, c), k, Co.pick(Co.window(u, 1n+k), c), ContextOrder.first_res(u, 1n+k, c), co.pick_window(u, 1n+k, c))

def co.res_eq(r: Maybe<&2, Nat>, -i: Nat, -j: Nat) -> {Co.res(r, i, j) == ContextOrder.call_step(r, i, j) : Co.Step}:
  match r:
    case None{}:
      {==}
    case Some{k}:
      {==}

# the results of the calls are the spec's
def co.results(cs: List<&2, Nat>, +t: List<&2, Co.Msg>, +i: Nat, +j: Nat) -> {Co.results(cs, Co.window(t, 1n+i), i, j) == ContextOrder.calls_spec(cs, t, i, j) : List<&2, Co.Step>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +u}:
      %co.pick_window(t, 1n+i, c) : {Co.res(Co.pick(Co.window(t, 1n+i), c), i, j) <> Co.results(u, Co.window(t, 1n+i), i, 1n+j) == ContextOrder.call_step(_, i, j) <> ContextOrder.calls_spec(u, t, i, 1n+j) : List<&2, Co.Step>}
      %co.res_eq(Co.pick(Co.window(t, 1n+i), c), i, j) : {Co.res(Co.pick(Co.window(t, 1n+i), c), i, j) <> Co.results(u, Co.window(t, 1n+i), i, 1n+j) == _ <> ContextOrder.calls_spec(u, t, i, 1n+j) : List<&2, Co.Step>}
      %co.results(u, t, i, 1n+j) : {Co.res(Co.pick(Co.window(t, 1n+i), c), i, j) <> Co.results(u, Co.window(t, 1n+i), i, 1n+j) == Co.res(Co.pick(Co.window(t, 1n+i), c), i, j) <> _ : List<&2, Co.Step>}
      {==}

# the code's order is the spec's
def co.order(ms: List<&2, Co.Msg>, +i: Nat) -> {Co.order.go(ms, i) == ContextOrder.order_spec.go(ms, i) : List<&2, Co.Step>}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +t}:
      match m:
        case Co.MUser{}:
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{i} <> z, Co.order.go(t, 1n+i), ContextOrder.order_spec.go(t, 1n+i), co.order(t, 1n+i))
        case Co.MSystem{}:
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{i} <> z, Co.order.go(t, 1n+i), ContextOrder.order_spec.go(t, 1n+i), co.order(t, 1n+i))
        case Co.MAsst{s, +cs}:
          %co.results(cs, t, i, 0n) : {Co.Take{i} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+i), i, 0n), Co.order.go(t, 1n+i)) == Co.Take{i} <> List.append(&2, Co.Step, _, ContextOrder.order_spec.go(t, 1n+i)) : List<&2, Co.Step>}
          %co.order(t, 1n+i) : {Co.Take{i} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+i), i, 0n), Co.order.go(t, 1n+i)) == Co.Take{i} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+i), i, 0n), _) : List<&2, Co.Step>}
          {==}
        case Co.MRes{c}:
          co.order(t, 1n+i)

# ---- the split identity ----

# no window of an assistant reaches into a sequence that starts with an
# assistant
def co.win_asst(b: List<&2, Co.Msg>, -k: Nat, h: {ContextOrder.starts_asst(b) == True{} : Bool}) -> {Co.window(b, k) == Nil{} : List<&2, Co.Hit>}:
  match b:
    case Nil{}:
      co.ft({Co.window(Nil{}, k) == Nil{} : List<&2, Co.Hit>}, h)
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          co.ft({Co.window(Co.MUser{} <> u, k) == Nil{} : List<&2, Co.Hit>}, h)
        case Co.MSystem{}:
          co.ft({Co.window(Co.MSystem{} <> u, k) == Nil{} : List<&2, Co.Hit>}, h)
        case Co.MAsst{s, cs}:
          {==}
        case Co.MRes{c}:
          co.ft({Co.window(Co.MRes{c} <> u, k) == Nil{} : List<&2, Co.Hit>}, h)

def co.win_app(x: List<&2, Co.Msg>, +b: List<&2, Co.Msg>, +k: Nat, +h: {ContextOrder.starts_asst(b) == True{} : Bool}) -> {Co.window(List.append(&2, Co.Msg, x, b), k) == Co.window(x, k) : List<&2, Co.Hit>}:
  match x:
    case Nil{}:
      co.win_asst(b, k, h)
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          co.win_app(u, b, 1n+k, h)
        case Co.MSystem{}:
          co.win_app(u, b, 1n+k, h)
        case Co.MAsst{s, cs}:
          {==}
        case Co.MRes{c}:
          Equal.cong(List<&2, Co.Hit>, List<&2, Co.Hit>, z => Co.Hit{k, c} <> z, Co.window(List.append(&2, Co.Msg, u, b), 1n+k), Co.window(u, 1n+k), co.win_app(u, b, 1n+k, h))

# the order of the rest after the head of a ++ b, from the induction
# hypothesis at offset 1 + i
def co.oa.tail(t: List<&2, Co.Msg>, -b: List<&2, Co.Msg>, +i: Nat, +ih: {Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i) == List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, Nat.add(List.length(&2, Co.Msg, t), 1n+i))) : List<&2, Co.Step>}) -> {Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i) == List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))) : List<&2, Co.Step>}:
  %co.add_s(List.length(&2, Co.Msg, t), i) : {Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i) == List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, _)) : List<&2, Co.Step>}
  ih

# ordering a ++ b orders a, then b at the offset |a| + i, when b starts
# with an assistant
def co.order_app(a: List<&2, Co.Msg>, +b: List<&2, Co.Msg>, +i: Nat, +h: {ContextOrder.starts_asst(b) == True{} : Bool}) -> {Co.order.go(List.append(&2, Co.Msg, a, b), i) == List.append(&2, Co.Step, Co.order.go(a, i), Co.order.go(b, Nat.add(List.length(&2, Co.Msg, a), i))) : List<&2, Co.Step>}:
  match a:
    case Nil{}:
      {==}
    case Con{m, +t}:
      match m:
        case Co.MUser{}:
          +ih = co.oa.tail(t, b, i, co.order_app(t, b, 1n+i, h))
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{i} <> z, Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i), List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))), ih)
        case Co.MSystem{}:
          +ih = co.oa.tail(t, b, i, co.order_app(t, b, 1n+i, h))
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{i} <> z, Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i), List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))), ih)
        case Co.MAsst{s, +cs}:
          +ih = co.oa.tail(t, b, i, co.order_app(t, b, 1n+i, h))
          +rs = Co.results(cs, Co.window(t, 1n+i), i, 0n)
          %Equal.sym(List<&2, Co.Hit>, Co.window(List.append(&2, Co.Msg, t, b), 1n+i), Co.window(t, 1n+i), co.win_app(t, b, 1n+i, h)) : {Co.Take{i} <> List.append(&2, Co.Step, Co.results(cs, _, i, 0n), Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i)) == Co.Take{i} <> List.append(&2, Co.Step, List.append(&2, Co.Step, rs, Co.order.go(t, 1n+i)), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))) : List<&2, Co.Step>}
          %Equal.sym(List<&2, Co.Step>, List.append(&2, Co.Step, List.append(&2, Co.Step, rs, Co.order.go(t, 1n+i)), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))), List.append(&2, Co.Step, rs, List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i)))), co.app_assoc(Co.Step, rs, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i)))) : {Co.Take{i} <> List.append(&2, Co.Step, rs, Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i)) == Co.Take{i} <> _ : List<&2, Co.Step>}
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{i} <> List.append(&2, Co.Step, rs, z), Co.order.go(List.append(&2, Co.Msg, t, b), 1n+i), List.append(&2, Co.Step, Co.order.go(t, 1n+i), Co.order.go(b, 1n+Nat.add(List.length(&2, Co.Msg, t), i))), ih)
        case Co.MRes{c}:
          +ih = co.oa.tail(t, b, i, co.order_app(t, b, 1n+i, h))
          ih

def co.mshift(+n: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      None{}
    case Some{k}:
      Some{Nat.add(n, k)}

def co.ps.sel(b: Bool, +n: Nat, -k: Nat, -x: Maybe<&2, Nat>, -y: Maybe<&2, Nat>, e: {x == co.mshift(n, y) : Maybe<&2, Nat>}) -> {Co.pick.sel(b, Nat.add(n, k), x) == co.mshift(n, Co.pick.sel(b, k, y)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def co.pk.fix(-u: List<&2, Co.Msg>, +n: Nat, +k: Nat, -c: Nat, ih: {Co.pick(Co.window(u, Nat.add(n, 1n+k)), c) == co.mshift(n, Co.pick(Co.window(u, 1n+k), c)) : Maybe<&2, Nat>}) -> {Co.pick(Co.window(u, 1n+Nat.add(n, k)), c) == co.mshift(n, Co.pick(Co.window(u, 1n+k), c)) : Maybe<&2, Nat>}:
  %co.add_s(n, k) : {Co.pick(Co.window(u, _), c) == co.mshift(n, Co.pick(Co.window(u, 1n+k), c)) : Maybe<&2, Nat>}
  ih

# the first hit of a window at offset n + k is the one at k, shifted
def co.pick_shift(t: List<&2, Co.Msg>, +n: Nat, +k: Nat, +c: Nat) -> {Co.pick(Co.window(t, Nat.add(n, k)), c) == co.mshift(n, Co.pick(Co.window(t, k), c)) : Maybe<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{m, +u}:
      match m:
        case Co.MUser{}:
          co.pk.fix(u, n, k, c, co.pick_shift(u, n, 1n+k, c))
        case Co.MSystem{}:
          co.pk.fix(u, n, k, c, co.pick_shift(u, n, 1n+k, c))
        case Co.MAsst{s, cs}:
          {==}
        case Co.MRes{d}:
          co.ps.sel(Nat.is_eq(d, c), n, k, Co.pick(Co.window(u, 1n+Nat.add(n, k)), c), Co.pick(Co.window(u, 1n+k), c), co.pk.fix(u, n, k, c, co.pick_shift(u, n, 1n+k, c)))

def co.res_shift(r: Maybe<&2, Nat>, +n: Nat, -i: Nat, -j: Nat) -> {Co.res(co.mshift(n, r), Nat.add(n, i), j) == ContextOrder.shift_step(n, Co.res(r, i, j)) : Co.Step}:
  match r:
    case None{}:
      {==}
    case Some{k}:
      {==}

# the results of an assistant at offset n + i are those at i, shifted
def co.results_shift(cs: List<&2, Nat>, +t: List<&2, Co.Msg>, +n: Nat, +i: Nat, +j: Nat) -> {Co.results(cs, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), j) == ContextOrder.shift(n, Co.results(cs, Co.window(t, 1n+i), i, j)) : List<&2, Co.Step>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +u}:
      %Equal.sym(Maybe<&2, Nat>, Co.pick(Co.window(t, 1n+Nat.add(n, i)), c), co.mshift(n, Co.pick(Co.window(t, 1n+i), c)), co.pk.fix(t, n, i, c, co.pick_shift(t, n, 1n+i, c))) : {Co.res(_, Nat.add(n, i), j) <> Co.results(u, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 1n+j) == ContextOrder.shift_step(n, Co.res(Co.pick(Co.window(t, 1n+i), c), i, j)) <> ContextOrder.shift(n, Co.results(u, Co.window(t, 1n+i), i, 1n+j)) : List<&2, Co.Step>}
      %co.res_shift(Co.pick(Co.window(t, 1n+i), c), n, i, j) : {Co.res(co.mshift(n, Co.pick(Co.window(t, 1n+i), c)), Nat.add(n, i), j) <> Co.results(u, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 1n+j) == _ <> ContextOrder.shift(n, Co.results(u, Co.window(t, 1n+i), i, 1n+j)) : List<&2, Co.Step>}
      Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.res(co.mshift(n, Co.pick(Co.window(t, 1n+i), c)), Nat.add(n, i), j) <> z, Co.results(u, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 1n+j), ContextOrder.shift(n, Co.results(u, Co.window(t, 1n+i), i, 1n+j)), co.results_shift(u, t, n, i, 1n+j))

def co.shift_app(+n: Nat, xs: List<&2, Co.Step>, -ys: List<&2, Co.Step>) -> {ContextOrder.shift(n, List.append(&2, Co.Step, xs, ys)) == List.append(&2, Co.Step, ContextOrder.shift(n, xs), ContextOrder.shift(n, ys)) : List<&2, Co.Step>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => ContextOrder.shift_step(n, x) <> z, ContextOrder.shift(n, List.append(&2, Co.Step, t, ys)), List.append(&2, Co.Step, ContextOrder.shift(n, t), ContextOrder.shift(n, ys)), co.shift_app(n, t, ys))

def co.os.fix(-t: List<&2, Co.Msg>, +n: Nat, +i: Nat, ih: {Co.order.go(t, Nat.add(n, 1n+i)) == ContextOrder.shift(n, Co.order.go(t, 1n+i)) : List<&2, Co.Step>}) -> {Co.order.go(t, 1n+Nat.add(n, i)) == ContextOrder.shift(n, Co.order.go(t, 1n+i)) : List<&2, Co.Step>}:
  %co.add_s(n, i) : {Co.order.go(t, _) == ContextOrder.shift(n, Co.order.go(t, 1n+i)) : List<&2, Co.Step>}
  ih

# ordering at offset n + i is ordering at i, shifted
def co.order_shift(b: List<&2, Co.Msg>, +n: Nat, +i: Nat) -> {Co.order.go(b, Nat.add(n, i)) == ContextOrder.shift(n, Co.order.go(b, i)) : List<&2, Co.Step>}:
  match b:
    case Nil{}:
      {==}
    case Con{m, +t}:
      match m:
        case Co.MUser{}:
          +ih = co.os.fix(t, n, i, co.order_shift(t, n, 1n+i))
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{Nat.add(n, i)} <> z, Co.order.go(t, 1n+Nat.add(n, i)), ContextOrder.shift(n, Co.order.go(t, 1n+i)), ih)
        case Co.MSystem{}:
          +ih = co.os.fix(t, n, i, co.order_shift(t, n, 1n+i))
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{Nat.add(n, i)} <> z, Co.order.go(t, 1n+Nat.add(n, i)), ContextOrder.shift(n, Co.order.go(t, 1n+i)), ih)
        case Co.MAsst{s, +cs}:
          +ih = co.os.fix(t, n, i, co.order_shift(t, n, 1n+i))
          %Equal.sym(List<&2, Co.Step>, ContextOrder.shift(n, List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+i), i, 0n), Co.order.go(t, 1n+i))), List.append(&2, Co.Step, ContextOrder.shift(n, Co.results(cs, Co.window(t, 1n+i), i, 0n)), ContextOrder.shift(n, Co.order.go(t, 1n+i))), co.shift_app(n, Co.results(cs, Co.window(t, 1n+i), i, 0n), Co.order.go(t, 1n+i))) : {Co.Take{Nat.add(n, i)} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 0n), Co.order.go(t, 1n+Nat.add(n, i))) == Co.Take{Nat.add(n, i)} <> _ : List<&2, Co.Step>}
          %co.results_shift(cs, t, n, i, 0n) : {Co.Take{Nat.add(n, i)} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 0n), Co.order.go(t, 1n+Nat.add(n, i))) == Co.Take{Nat.add(n, i)} <> List.append(&2, Co.Step, _, ContextOrder.shift(n, Co.order.go(t, 1n+i))) : List<&2, Co.Step>}
          Equal.cong(List<&2, Co.Step>, List<&2, Co.Step>, z => Co.Take{Nat.add(n, i)} <> List.append(&2, Co.Step, Co.results(cs, Co.window(t, 1n+Nat.add(n, i)), Nat.add(n, i), 0n), z), Co.order.go(t, 1n+Nat.add(n, i)), ContextOrder.shift(n, Co.order.go(t, 1n+i)), ih)
        case Co.MRes{c}:
          +ih = co.os.fix(t, n, i, co.order_shift(t, n, 1n+i))
          ih

# ---- the plan ----

def co.lsel(r: Maybe<&2, Nat>, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      acc
    case Some{k}:
      Some{k}

def co.ls.no(r: Maybe<&2, Nat>, -i: Nat, -acc: Maybe<&2, Nat>) -> {co.lsel(r, acc) == co.lsel(ContextOrder.last_spec.pick(r, False{}, i), acc) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{k}:
      {==}

def co.ls.yes(r: Maybe<&2, Nat>, -i: Nat, -acc: Maybe<&2, Nat>) -> {co.lsel(r, Some{i}) == co.lsel(ContextOrder.last_spec.pick(r, True{}, i), acc) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{k}:
      {==}

# the code's last assistant is the spec's, else what it had
def co.last(ms: List<&2, Co.Msg>, +i: Nat, +acc: Maybe<&2, Nat>) -> {Co.last_asst(ms, i, acc) == co.lsel(ContextOrder.last_spec(ms, i), acc) : Maybe<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +t}:
      match m:
        case Co.MUser{}:
          %co.ls.no(ContextOrder.last_spec(t, 1n+i), i, acc) : {Co.last_asst(t, 1n+i, acc) == _ : Maybe<&2, Nat>}
          co.last(t, 1n+i, acc)
        case Co.MSystem{}:
          %co.ls.no(ContextOrder.last_spec(t, 1n+i), i, acc) : {Co.last_asst(t, 1n+i, acc) == _ : Maybe<&2, Nat>}
          co.last(t, 1n+i, acc)
        case Co.MAsst{s, cs}:
          %co.ls.yes(ContextOrder.last_spec(t, 1n+i), i, acc) : {Co.last_asst(t, 1n+i, Some{i}) == _ : Maybe<&2, Nat>}
          co.last(t, 1n+i, Some{i})
        case Co.MRes{c}:
          %co.ls.no(ContextOrder.last_spec(t, 1n+i), i, acc) : {Co.last_asst(t, 1n+i, acc) == _ : Maybe<&2, Nat>}
          co.last(t, 1n+i, acc)

def co.split.pos(r: Maybe<&2, Nat>) -> {Co.split.pos(co.lsel(r, None{})) == ContextOrder.split_spec.pos(r) : Maybe<&2, Nat>}:
  match r:
    case None{}:
      {==}
    case Some{k}:
      match k:
        case 0n:
          {==}
        case 1n+p:
          {==}

# the code's split is the spec's
def co.split(+ms: List<&2, Co.Msg>) -> {Co.split(ms) == ContextOrder.split_spec(ms) : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Co.last_asst(ms, 0n, None{}), co.lsel(ContextOrder.last_spec(ms, 0n), None{}), co.last(ms, 0n, None{})) : {Co.split.pos(_) == ContextOrder.split_spec(ms) : Maybe<&2, Nat>}
  co.split.pos(ContextOrder.last_spec(ms, 0n))

def co.take(n: Nat, ms: List<&2, Co.Msg>) -> {Co.take(n, ms) == ContextOrder.prefix(n, ms) : List<&2, Co.Msg>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match ms:
        case Nil{}:
          {==}
        case Con{+m, +t}:
          Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => m <> z, Co.take(p, t), ContextOrder.prefix(p, t), co.take(p, t))

def co.plan.at(sp: Maybe<&2, Nat>, +ms: List<&2, Co.Msg>) -> {Co.plan.at(sp, ms) == ContextOrder.plan_spec.at(sp, ms) : Co.Plan}:
  match sp:
    case None{}:
      Equal.cong(List<&2, Co.Step>, Co.Plan, z => Co.Plan{None{}, 0n, z}, Co.order(ms), ContextOrder.order_spec(ms), co.order(ms, 0n))
    case Some{+k}:
      %co.order(ms, 0n) : {Co.Plan{Some{k}, List.length(&2, Co.Step, Co.order(Co.take(k, ms))), Co.order(ms)} == Co.Plan{Some{k}, List.length(&2, Co.Step, ContextOrder.order_spec(ContextOrder.prefix(k, ms))), _} : Co.Plan}
      %co.order(ContextOrder.prefix(k, ms), 0n) : {Co.Plan{Some{k}, List.length(&2, Co.Step, Co.order(Co.take(k, ms))), Co.order(ms)} == Co.Plan{Some{k}, List.length(&2, Co.Step, _), Co.order(ms)} : Co.Plan}
      %co.take(k, ms) : {Co.Plan{Some{k}, List.length(&2, Co.Step, Co.order(Co.take(k, ms))), Co.order(ms)} == Co.Plan{Some{k}, List.length(&2, Co.Step, Co.order(_)), Co.order(ms)} : Co.Plan}
      {==}

# the code's plan is the spec's
def co.plan(+ms: List<&2, Co.Msg>) -> {Co.plan(ms) == ContextOrder.plan_spec(ms) : Co.Plan}:
  %co.split(ms) : {Co.plan.at(Co.split(ms), ms) == ContextOrder.plan_spec.at(_, ms) : Co.Plan}
  co.plan.at(Co.split(ms), ms)

# ---- the lead ----

def co.L(n: Nat, b: Bool) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+p:
      match b:
        case True{}:
          Some{1n+p}
        case False{}:
          None{}

def co.L.no(i: Nat) -> {None{} == co.L(i, False{}) : Maybe<&2, Nat>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def co.L.sys(i: Nat) -> {Co.lead.sys(i) == co.L(i, True{}) : Maybe<&2, Nat>}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      {==}

def co.lg.fix(t: List<&2, Co.Role>, +i: Nat, ih: {Co.lead.go(t, 1n+i) == co.L(Nat.add(ContextOrder.users(t), 1n+i), ContextOrder.system_at(ContextOrder.users(t), t)) : Maybe<&2, Nat>}) -> {Co.lead.go(t, 1n+i) == co.L(1n+Nat.add(ContextOrder.users(t), i), ContextOrder.system_at(ContextOrder.users(t), t)) : Maybe<&2, Nat>}:
  %co.add_s(ContextOrder.users(t), i) : {Co.lead.go(t, 1n+i) == co.L(_, ContextOrder.system_at(ContextOrder.users(t), t)) : Maybe<&2, Nat>}
  ih

# the code's lead from index i: the first message after the leading
# users, when it is a system message and not first
def co.lead(rs: List<&2, Co.Role>, +i: Nat) -> {Co.lead.go(rs, i) == co.L(Nat.add(ContextOrder.users(rs), i), ContextOrder.system_at(ContextOrder.users(rs), rs)) : Maybe<&2, Nat>}:
  match rs:
    case Nil{}:
      co.L.no(i)
    case Con{r, +t}:
      match r:
        case Co.RUser{}:
          co.lg.fix(t, i, co.lead(t, 1n+i))
        case Co.RSystem{}:
          co.L.sys(i)
        case Co.RAsst{}:
          co.L.no(i)
        case Co.RRes{}:
          co.L.no(i)

def co.L.sb(b: Bool, -p: Nat) -> {co.L(1n+p, b) == ContextOrder.lead_spec.sys(b, 1n+p) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def co.L.at(n: Nat, +rs: List<&2, Co.Role>) -> {co.L(n, ContextOrder.system_at(n, rs)) == ContextOrder.lead_spec.at(n, rs) : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      co.L.sb(ContextOrder.system_at(1n+p, rs), p)

# ---- contributions ----

def co.excluded(s: Co.Stop) -> {Co.excluded(s) == ContextOrder.gone_spec(s) : Bool}:
  match s:
    case Co.SPending{}:
      {==}
    case Co.SStop{}:
      {==}
    case Co.SLength{}:
      {==}
    case Co.SToolUse{}:
      {==}
    case Co.SError{}:
      {==}
    case Co.SAborted{}:
      {==}
    case Co.SDeferred{}:
      {==}

def co.kept(m: Co.Msg) -> {Co.kept(m) == ContextOrder.stays(m) : Bool}:
  match m:
    case Co.MUser{}:
      {==}
    case Co.MSystem{}:
      {==}
    case Co.MAsst{s, cs}:
      Equal.cong(Bool, Bool, z => Bool.not(z), Co.excluded(s), ContextOrder.gone_spec(s), co.excluded(s))
    case Co.MRes{c}:
      {==}

def co.ko(b: Bool, -j: Nat, -x: List<&2, Nat>, -y: List<&2, Nat>, e: {x == y : List<&2, Nat>}) -> {Co.keep.one(b, j, x) == ContextOrder.stay_idx.one(b, j, y) : List<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => j <> z, x, y, e)
    case False{}:
      e

# the indices the code keeps are the spec's
def co.keep(ms: List<&2, Co.Msg>, +j: Nat) -> {Co.keep.go(ms, j) == ContextOrder.stay_idx(ms, j) : List<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      %co.kept(m) : {Co.keep.one(Co.kept(m), j, Co.keep.go(t, 1n+j)) == ContextOrder.stay_idx.one(_, j, ContextOrder.stay_idx(t, 1n+j)) : List<&2, Nat>}
      co.ko(Co.kept(m), j, Co.keep.go(t, 1n+j), ContextOrder.stay_idx(t, 1n+j), co.keep(t, 1n+j))

def co.km(b: Bool, +m: Co.Msg, -x: List<&2, Co.Msg>, -y: List<&2, Co.Msg>, e: {x == y : List<&2, Co.Msg>}) -> {Co.keep.msg(b, m, x) == ContextOrder.stay_msgs.one(b, m, y) : List<&2, Co.Msg>}:
  match b:
    case True{}:
      Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => m <> z, x, y, e)
    case False{}:
      e

# the messages the code keeps are the spec's
def co.msgs(ms: List<&2, Co.Msg>) -> {Co.keep.msgs(ms) == ContextOrder.stay_msgs(ms) : List<&2, Co.Msg>}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +t}:
      %co.kept(m) : {Co.keep.msg(Co.kept(m), m, Co.keep.msgs(t)) == ContextOrder.stay_msgs.one(_, m, ContextOrder.stay_msgs(t)) : List<&2, Co.Msg>}
      co.km(Co.kept(m), m, Co.keep.msgs(t), ContextOrder.stay_msgs(t), co.msgs(t))

def co.contribute(e: Co.Edit, +own: List<&2, Co.Msg>) -> {Co.contribute(e, own) == ContextOrder.keep_spec(e, own) : Co.Keep}:
  match e:
    case Co.NoEdit{}:
      Equal.cong(List<&2, Nat>, Co.Keep, z => Co.Own{z}, Co.keep.go(own, 0n), ContextOrder.stay_idx(own, 0n), co.keep(own, 0n))
    case Co.Omit{}:
      {==}
    case Co.Replace{+ms}:
      Equal.cong(List<&2, Nat>, Co.Keep, z => Co.Alt{z}, Co.keep.go(ms, 0n), ContextOrder.stay_idx(ms, 0n), co.keep(ms, 0n))

def co.contributed(e: Co.Edit, +own: List<&2, Co.Msg>) -> {Co.contributed(e, own) == ContextOrder.given_spec(e, own) : List<&2, Co.Msg>}:
  match e:
    case Co.NoEdit{}:
      co.msgs(own)
    case Co.Omit{}:
      {==}
    case Co.Replace{+ms}:
      co.msgs(ms)

def co.part(+i: Nat, e: Co.Ent) -> {Co.part(i, e) == ContextOrder.part_spec(i, e) : Co.Part}:
  match e:
    case Co.Ent{h, ed, +own}:
      Equal.cong(Co.Keep, Co.Part, z => Co.Part{i, z}, Co.contribute(ed, own), ContextOrder.keep_spec(ed, own), co.contribute(ed, own))

def co.part.msgs(e: Co.Ent) -> {Co.part.msgs(e) == ContextOrder.given_of(e) : List<&2, Co.Msg>}:
  match e:
    case Co.Ent{h, ed, +own}:
      co.contributed(ed, own)

# ---- derive ----

def co.pr.one(h: Bool, +i: Nat, +e: Co.Ent, -x: List<&2, Co.Part>, -y: List<&2, Co.Part>, ex: {x == y : List<&2, Co.Part>}) -> {Co.parts.one(h, i, e, x) == ContextOrder.range_parts.one(h, i, e, y) : List<&2, Co.Part>}:
  match h:
    case True{}:
      ex
    case False{}:
      %co.part(i, e) : {Co.part(i, e) <> x == _ <> y : List<&2, Co.Part>}
      Equal.cong(List<&2, Co.Part>, List<&2, Co.Part>, z => Co.part(i, e) <> z, x, y, ex)

def co.pr.ent(+e: Co.Ent) -> {Bool.and(True{}, Co.is_head(e)) == ContextOrder.marker_of(e) : Bool}:
  match e:
    case Co.Ent{h, ed, own}:
      {==}

# the parts of the range after a marker
def co.range_parts(es: List<&2, Co.Ent>, +i: Nat) -> {Co.parts.go(es, True{}, i) == ContextOrder.range_parts(es, i) : List<&2, Co.Part>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %co.pr.ent(e) : {Co.parts.one(Bool.and(True{}, Co.is_head(e)), i, e, Co.parts.go(t, True{}, 1n+i)) == ContextOrder.range_parts.one(_, i, e, ContextOrder.range_parts(t, 1n+i)) : List<&2, Co.Part>}
      co.pr.one(Bool.and(True{}, Co.is_head(e)), i, e, Co.parts.go(t, True{}, 1n+i), ContextOrder.range_parts(t, 1n+i), co.range_parts(t, 1n+i))

# the parts of every entry without a marker
def co.all_parts(es: List<&2, Co.Ent>, +i: Nat) -> {Co.parts.go(es, False{}, i) == ContextOrder.all_parts(es, i) : List<&2, Co.Part>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %co.part(i, e) : {Co.part(i, e) <> Co.parts.go(t, False{}, 1n+i) == _ <> ContextOrder.all_parts(t, 1n+i) : List<&2, Co.Part>}
      Equal.cong(List<&2, Co.Part>, List<&2, Co.Part>, z => Co.part(i, e) <> z, Co.parts.go(t, False{}, 1n+i), ContextOrder.all_parts(t, 1n+i), co.all_parts(t, 1n+i))

def co.parts(mark: Bool, es: List<&2, Co.Ent>) -> {Co.parts(mark, es) == ContextOrder.parts_spec(mark, es) : List<&2, Co.Part>}:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          {==}
        case Con{+e, +t}:
          %co.part(0n, e) : {Co.part(0n, e) <> Co.parts.go(t, True{}, 1n) == _ <> ContextOrder.range_parts(t, 1n) : List<&2, Co.Part>}
          Equal.cong(List<&2, Co.Part>, List<&2, Co.Part>, z => Co.part(0n, e) <> z, Co.parts.go(t, True{}, 1n), ContextOrder.range_parts(t, 1n), co.range_parts(t, 1n))
    case False{}:
      co.all_parts(es, 0n)

def co.mr.one(h: Bool, +e: Co.Ent, -x: List<&2, Co.Msg>, -y: List<&2, Co.Msg>, ex: {x == y : List<&2, Co.Msg>}) -> {Co.msgs.one(h, e, x) == ContextOrder.range_msgs.one(h, e, y) : List<&2, Co.Msg>}:
  match h:
    case True{}:
      ex
    case False{}:
      %co.part.msgs(e) : {List.append(&2, Co.Msg, Co.part.msgs(e), x) == List.append(&2, Co.Msg, _, y) : List<&2, Co.Msg>}
      Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => List.append(&2, Co.Msg, Co.part.msgs(e), z), x, y, ex)

def co.range_msgs(es: List<&2, Co.Ent>) -> {Co.msgs.go(es, True{}) == ContextOrder.range_msgs(es) : List<&2, Co.Msg>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %co.pr.ent(e) : {Co.msgs.one(Bool.and(True{}, Co.is_head(e)), e, Co.msgs.go(t, True{})) == ContextOrder.range_msgs.one(_, e, ContextOrder.range_msgs(t)) : List<&2, Co.Msg>}
      co.mr.one(Bool.and(True{}, Co.is_head(e)), e, Co.msgs.go(t, True{}), ContextOrder.range_msgs(t), co.range_msgs(t))

def co.all_msgs(es: List<&2, Co.Ent>) -> {Co.msgs.go(es, False{}) == ContextOrder.all_msgs(es) : List<&2, Co.Msg>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %co.part.msgs(e) : {List.append(&2, Co.Msg, Co.part.msgs(e), Co.msgs.go(t, False{})) == List.append(&2, Co.Msg, _, ContextOrder.all_msgs(t)) : List<&2, Co.Msg>}
      Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => List.append(&2, Co.Msg, Co.part.msgs(e), z), Co.msgs.go(t, False{}), ContextOrder.all_msgs(t), co.all_msgs(t))

def co.msgs_of(mark: Bool, es: List<&2, Co.Ent>) -> {Co.msgs(mark, es) == ContextOrder.msgs_spec(mark, es) : List<&2, Co.Msg>}:
  match mark:
    case True{}:
      match es:
        case Nil{}:
          {==}
        case Con{+e, +t}:
          %co.part.msgs(e) : {List.append(&2, Co.Msg, Co.part.msgs(e), Co.msgs.go(t, True{})) == List.append(&2, Co.Msg, _, ContextOrder.range_msgs(t)) : List<&2, Co.Msg>}
          Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => List.append(&2, Co.Msg, Co.part.msgs(e), z), Co.msgs.go(t, True{}), ContextOrder.range_msgs(t), co.range_msgs(t))
    case False{}:
      co.all_msgs(es)

# ---- extend ----

def co.redo3(x: Bool, h: Bool, d: Bool, -r: Bool) -> {Bool.or(Bool.or(x, Bool.or(h, d)), r) == Bool.or(x, Bool.or(h, Bool.or(d, r))) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      match h:
        case True{}:
          {==}
        case False{}:
          match d:
            case True{}:
              {==}
            case False{}:
              {==}

def co.rederive(ads: List<&2, Co.Add>) -> {Co.rederive(ads) == ContextOrder.redo_spec(ads) : Bool}:
  match ads:
    case Nil{}:
      {==}
    case Con{a, +t}:
      match a:
        case Co.Add{+x, +h, +d, own}:
          %co.rederive(t) : {Bool.or(Bool.or(x, Bool.or(h, d)), Co.rederive(t)) == Bool.or(x, Bool.or(h, Bool.or(d, _))) : Bool}
          co.redo3(x, h, d, Co.rederive(t))

def co.keeps(ads: List<&2, Co.Add>) -> {Co.keeps(ads) == ContextOrder.keeps_spec(ads) : List<&2, List<&2, Nat>>}:
  match ads:
    case Nil{}:
      {==}
    case Con{a, +t}:
      match a:
        case Co.Add{x, h, d, +own}:
          %co.keep(own, 0n) : {Co.keep.go(own, 0n) <> Co.keeps(t) == _ <> ContextOrder.keeps_spec(t) : List<&2, List<&2, Nat>>}
          Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => Co.keep.go(own, 0n) <> z, Co.keeps(t), ContextOrder.keeps_spec(t), co.keeps(t))

def co.added(ads: List<&2, Co.Add>) -> {Co.added(ads) == ContextOrder.added_spec(ads) : List<&2, Co.Msg>}:
  match ads:
    case Nil{}:
      {==}
    case Con{a, +t}:
      match a:
        case Co.Add{x, h, d, +own}:
          %co.msgs(own) : {List.append(&2, Co.Msg, Co.keep.msgs(own), Co.added(t)) == List.append(&2, Co.Msg, _, ContextOrder.added_spec(t)) : List<&2, Co.Msg>}
          Equal.cong(List<&2, Co.Msg>, List<&2, Co.Msg>, z => List.append(&2, Co.Msg, Co.keep.msgs(own), z), Co.added(t), ContextOrder.added_spec(t), co.added(t))

def co.ext.pick(b: Bool, +ads: List<&2, Co.Add>, +open: List<&2, Co.Msg>) -> {Co.extend.pick(b, ads, open) == ContextOrder.extend_spec.pick(b, ads, open) : Co.Extended}:
  match b:
    case True{}:
      {==}
    case False{}:
      %co.keeps(ads) : {Co.Extended{Co.keeps(ads), Co.plan(List.append(&2, Co.Msg, open, Co.added(ads)))} == Co.Extended{_, ContextOrder.plan_spec(List.append(&2, Co.Msg, open, ContextOrder.added_spec(ads)))} : Co.Extended}
      %co.added(ads) : {Co.Extended{Co.keeps(ads), Co.plan(List.append(&2, Co.Msg, open, Co.added(ads)))} == Co.Extended{Co.keeps(ads), ContextOrder.plan_spec(List.append(&2, Co.Msg, open, _))} : Co.Extended}
      %co.plan(List.append(&2, Co.Msg, open, Co.added(ads))) : {Co.Extended{Co.keeps(ads), Co.plan(List.append(&2, Co.Msg, open, Co.added(ads)))} == Co.Extended{Co.keeps(ads), _} : Co.Extended}
      {==}
