# eukhe: lemmas shared by the proofs of area privacy, section ip: texts
# and symbol lists, a hex or decimal char's symbol, and the reader over
# the text an address writes (a group, an IPv4, the items of an address)

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp

# Texts and lists
# ---------------

def prd.sym_app(a: String, -b: String) -> {Ip.Sym.list(String.append(a, b)) == List.append(&2, Ip.Sym, Ip.Sym.list(a), Ip.Sym.list(b)) : List<&2, Ip.Sym>}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %prd.sym_app(t, b) : {Ip.Sym.of(h) <> Ip.Sym.list(String.append(t, b)) == Ip.Sym.of(h) <> _ : List<&2, Ip.Sym>}
      {==}

def prd.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %prd.app_nil(t) : {SCon{h, String.append(t, SNil{})} == SCon{h, _} : String}
      {==}

def prd.app_assoc(a: String, -b: String, -c: String) -> {String.append(String.append(a, b), c) == String.append(a, String.append(b, c)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      %prd.app_assoc(t, b, c) : {SCon{h, String.append(String.append(t, b), c)} == SCon{h, _} : String}
      {==}

def prd.len_sym(s: String) -> {List.length(&2, Ip.Sym, Ip.Sym.list(s)) == String.length(s) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      %prd.len_sym(t) : {1n+List.length(&2, Ip.Sym, Ip.Sym.list(t)) == 1n+_ : Nat}
      {==}

def prd.list_len_app(xs: List<&2, Ip.Sym>, +ys: List<&2, Ip.Sym>) -> {List.length(&2, Ip.Sym, List.append(&2, Ip.Sym, xs, ys)) == Nat.add(List.length(&2, Ip.Sym, xs), List.length(&2, Ip.Sym, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      %prd.list_len_app(rest, ys) : {1n+List.length(&2, Ip.Sym, List.append(&2, Ip.Sym, rest, ys)) == 1n+_ : Nat}
      {==}

def prd.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %prd.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def prd.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %prd.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def prd.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def prd.sub_add(+a: Nat, b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, prd.add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      prd.sub_zero(a)
    case 1n+p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), prd.add_succ(a, p)) : {Nat.sub(_, 1n+p) == a : Nat}
      prd.sub_add(a, p)

# Chars
# -----

# a decimal digit's symbol is Dig
def prd.dec_sym(c: Char, +h: {S.dec(c) == True{} : Bool}) -> {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}:
  match c:
    case Chr{+x}:
      %Equal.sym(Bool, Cx.in(x, 48, 57), True{}, h) : {Ip.Sym.when(_, Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))) == Ip.Dig{Chr{x}} : Ip.Sym}
      {==}

def prd.hex3(b: Bool, +x: U32, +h: {b == True{} : Bool}) -> Either<&1, &1, {Ip.Sym.when(b, Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))) == Ip.Dig{Chr{x}} : Ip.Sym}, {Ip.Sym.when(b, Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))) == Ip.Hx{Chr{x}} : Ip.Sym}>:
  match b:
    case True{}:
      Inr{{==}}
    case False{}:
      LIp.pip.absurd_ft(Either<&1, &1, {Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))) == Ip.Dig{Chr{x}} : Ip.Sym}, {Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))) == Ip.Hx{Chr{x}} : Ip.Sym}>, h)

def prd.hex2(b: Bool, +x: U32, +h: {Bool.or(b, S.in(x, 65, 70)) == True{} : Bool}) -> Either<&1, &1, {Ip.Sym.when(b, Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))) == Ip.Dig{Chr{x}} : Ip.Sym}, {Ip.Sym.when(b, Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{}))))))))) == Ip.Hx{Chr{x}} : Ip.Sym}>:
  match b:
    case True{}:
      Inr{{==}}
    case False{}:
      prd.hex3(Cx.in(x, 65, 70), x, h)

def prd.hex1(b: Bool, +x: U32, +h: {Bool.or(b, Bool.or(S.in(x, 97, 102), S.in(x, 65, 70))) == True{} : Bool}) -> Either<&1, &1, {Ip.Sym.when(b, Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))) == Ip.Dig{Chr{x}} : Ip.Sym}, {Ip.Sym.when(b, Ip.Dig{Chr{x}}, Ip.Sym.when(Cx.in(x, 97, 102), Ip.Hx{Chr{x}}, Ip.Sym.when(Cx.in(x, 65, 70), Ip.Hx{Chr{x}}, Ip.Sym.when(U32.is_eq(x, 58), Ip.Col{}, Ip.Sym.when(U32.is_eq(x, 46), Ip.Dot{}, Ip.Sym.when(Cx.in(x, 103, 122), Ip.Let{}, Ip.Sym.when(Cx.in(x, 71, 90), Ip.Let{}, Ip.Sym.when(U32.is_eq(x, 95), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 170), Ip.Und{}, Ip.Sym.when(U32.is_eq(x, 45), Ip.Dash{}, Ip.Oth{})))))))))) == Ip.Hx{Chr{x}} : Ip.Sym}>:
  match b:
    case True{}:
      Inl{{==}}
    case False{}:
      prd.hex2(Cx.in(x, 97, 102), x, h)

# a hex digit's symbol is Dig or Hx
def prd.hex_sym(c: Char, +h: {S.hex(c) == True{} : Bool}) -> Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>:
  match c:
    case Chr{+x}:
      prd.hex1(Cx.in(x, 48, 57), x, h)

# Runs
# ----

def prd.cut_s(r: Ip.Cut) -> String:
  match r:
    case Ip.Cut{s, rest}:
      s

def prd.cut_rest(r: Ip.Cut) -> List<&2, Ip.Sym>:
  match r:
    case Ip.Cut{s, rest}:
      rest

def prd.cut_eta(r: Ip.Cut) -> {r == Ip.Cut{prd.cut_s(r), prd.cut_rest(r)} : Ip.Cut}:
  match r:
    case Ip.Cut{s, rest}:
      {==}

def prd.run_c(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>) -> {Ip.run(Ip.Sym.of(c) <> ys) == Ip.run.cons(c, Ip.run(ys)) : Ip.Cut}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.run(_ <> ys) == Ip.run.cons(c, Ip.run(ys)) : Ip.Cut}
      {==}
    case Inr{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, d) : {Ip.run(_ <> ys) == Ip.run.cons(c, Ip.run(ys)) : Ip.Cut}
      {==}

# the run of hex digits over a text of hex digits, then X
def prd.run_hex(g: String, +X: List<&2, Ip.Sym>, +h: {S.all_hex(g) == True{} : Bool}) -> {Ip.run(List.append(&2, Ip.Sym, Ip.Sym.list(g), X)) == Ip.Cut{String.append(g, prd.cut_s(Ip.run(X))), prd.cut_rest(Ip.run(X))} : Ip.Cut}:
  match g:
    case SNil{}:
      prd.cut_eta(Ip.run(X))
    case SCon{+c, +t}:
      +hc = LIp.pip.and_l(S.hex(c), S.all_hex(t), h)
      +ht = LIp.pip.and_r(S.hex(c), S.all_hex(t), h)
      %Equal.sym(Ip.Cut, Ip.run(Ip.Sym.of(c) <> List.append(&2, Ip.Sym, Ip.Sym.list(t), X)), Ip.run.cons(c, Ip.run(List.append(&2, Ip.Sym, Ip.Sym.list(t), X))), prd.run_c(c, prd.hex_sym(c, hc), List.append(&2, Ip.Sym, Ip.Sym.list(t), X))) : {_ == Ip.Cut{SCon{c, String.append(t, prd.cut_s(Ip.run(X)))}, prd.cut_rest(Ip.run(X))} : Ip.Cut}
      %Equal.sym(Ip.Cut, Ip.run(List.append(&2, Ip.Sym, Ip.Sym.list(t), X)), Ip.Cut{String.append(t, prd.cut_s(Ip.run(X))), prd.cut_rest(Ip.run(X))}, prd.run_hex(t, X, ht)) : {Ip.run.cons(c, _) == Ip.Cut{SCon{c, String.append(t, prd.cut_s(Ip.run(X)))}, prd.cut_rest(Ip.run(X))} : Ip.Cut}
      {==}

# no hex digit, `:` or `.`: no run
def prd.run_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.run(y <> ys) == Ip.Cut{SNil{}, y <> ys} : Ip.Cut}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.run(Ip.Dig{c} <> ys) == Ip.Cut{SNil{}, Ip.Dig{c} <> ys} : Ip.Cut}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.run(Ip.Hx{c} <> ys) == Ip.Cut{SNil{}, Ip.Hx{c} <> ys} : Ip.Cut}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.run(Ip.Col{} <> ys) == Ip.Cut{SNil{}, Ip.Col{} <> ys} : Ip.Cut}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.run(Ip.Dot{} <> ys) == Ip.Cut{SNil{}, Ip.Dot{} <> ys} : Ip.Cut}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def prd.drun_c(c: Char, +ys: List<&2, Ip.Sym>, +h: {S.dec(c) == True{} : Bool}) -> {Ip.drun(Ip.Sym.of(c) <> ys) == Ip.run.cons(c, Ip.drun(ys)) : Ip.Cut}:
  %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, prd.dec_sym(c, h)) : {Ip.drun(_ <> ys) == Ip.run.cons(c, Ip.drun(ys)) : Ip.Cut}
  {==}

# the run of decimal digits over a text of decimal digits, then X
def prd.drun_dec(g: String, +X: List<&2, Ip.Sym>, +h: {S.all_dec(g) == True{} : Bool}) -> {Ip.drun(List.append(&2, Ip.Sym, Ip.Sym.list(g), X)) == Ip.Cut{String.append(g, prd.cut_s(Ip.drun(X))), prd.cut_rest(Ip.drun(X))} : Ip.Cut}:
  match g:
    case SNil{}:
      prd.cut_eta(Ip.drun(X))
    case SCon{+c, +t}:
      +hc = LIp.pip.and_l(S.dec(c), S.all_dec(t), h)
      +ht = LIp.pip.and_r(S.dec(c), S.all_dec(t), h)
      %Equal.sym(Ip.Cut, Ip.drun(Ip.Sym.of(c) <> List.append(&2, Ip.Sym, Ip.Sym.list(t), X)), Ip.run.cons(c, Ip.drun(List.append(&2, Ip.Sym, Ip.Sym.list(t), X))), prd.drun_c(c, List.append(&2, Ip.Sym, Ip.Sym.list(t), X), hc)) : {_ == Ip.Cut{SCon{c, String.append(t, prd.cut_s(Ip.drun(X)))}, prd.cut_rest(Ip.drun(X))} : Ip.Cut}
      %Equal.sym(Ip.Cut, Ip.drun(List.append(&2, Ip.Sym, Ip.Sym.list(t), X)), Ip.Cut{String.append(t, prd.cut_s(Ip.drun(X))), prd.cut_rest(Ip.drun(X))}, prd.drun_dec(t, X, ht)) : {Ip.run.cons(c, _) == Ip.Cut{SCon{c, String.append(t, prd.cut_s(Ip.drun(X)))}, prd.cut_rest(Ip.drun(X))} : Ip.Cut}
      {==}

# no decimal digit: no digit run
def prd.drun_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, +h: {S.k_dec(LIp.pip.kind(y)) == False{} : Bool}) -> {Ip.drun(y <> ys) == Ip.Cut{SNil{}, y <> ys} : Ip.Cut}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.drun(Ip.Dig{c} <> ys) == Ip.Cut{SNil{}, Ip.Dig{c} <> ys} : Ip.Cut}, Equal.sym(Bool, True{}, False{}, h))
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Dot{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

# The reader over a group
# -----------------------

def prd.grp_hex(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +s: List<&2, Ip.Sym>, +p: Nat, +acc: Ip.Acc) -> {Ip.read(Ip.Sym.of(c) <> ys, Ip.Grp{s, 1n+p}, acc) == Ip.read(ys, Ip.Grp{s, p}, acc) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(_ <> ys, Ip.Grp{s, 1n+p}, acc) == Ip.read(ys, Ip.Grp{s, p}, acc) : Ip.Read}
      {==}
    case Inr{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, d) : {Ip.read(_ <> ys, Ip.Grp{s, 1n+p}, acc) == Ip.read(ys, Ip.Grp{s, p}, acc) : Ip.Read}
      {==}

# the hex digits of g read inside a group with room for them
def prd.read_hexes(g: String, +X: List<&2, Ip.Sym>, +s: List<&2, Ip.Sym>, room: Nat, +acc: Ip.Acc, +h: {S.all_hex(g) == True{} : Bool}, +hl: {Nat.is_le(String.length(g), room) == True{} : Bool}) -> {Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(g), X), Ip.Grp{s, room}, acc) == Ip.read(X, Ip.Grp{s, Nat.sub(room, String.length(g))}, acc) : Ip.Read}:
  match g:
    case SNil{}:
      %Equal.sym(Nat, Nat.sub(room, 0n), room, prd.sub_zero(room)) : {Ip.read(X, Ip.Grp{s, room}, acc) == Ip.read(X, Ip.Grp{s, _}, acc) : Ip.Read}
      {==}
    case SCon{+c, +t}:
      match room:
        case 0n:
          LIp.pip.absurd_ft({Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(SCon{c, t}), X), Ip.Grp{s, 0n}, acc) == Ip.read(X, Ip.Grp{s, Nat.sub(0n, String.length(SCon{c, t}))}, acc) : Ip.Read}, hl)
        case 1n++p:
          +hc = LIp.pip.and_l(S.hex(c), S.all_hex(t), h)
          +ht = LIp.pip.and_r(S.hex(c), S.all_hex(t), h)
          Equal.trans(Ip.Read, Ip.read(Ip.Sym.of(c) <> List.append(&2, Ip.Sym, Ip.Sym.list(t), X), Ip.Grp{s, 1n+p}, acc), Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(t), X), Ip.Grp{s, p}, acc), Ip.read(X, Ip.Grp{s, Nat.sub(p, String.length(t))}, acc), prd.grp_hex(c, prd.hex_sym(c, hc), List.append(&2, Ip.Sym, Ip.Sym.list(t), X), s, p, acc), prd.read_hexes(t, X, s, p, acc, ht, hl))

def prd.open_hex(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +acc: Ip.Acc) -> {Ip.read(Ip.Sym.of(c) <> ys, Ip.Open{}, acc) == Ip.read(ys, Ip.Grp{Ip.Sym.of(c) <> ys, 3n}, acc) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(_ <> ys, Ip.Open{}, acc) == Ip.read(ys, Ip.Grp{_ <> ys, 3n}, acc) : Ip.Read}
      {==}
    case Inr{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, d) : {Ip.read(_ <> ys, Ip.Open{}, acc) == Ip.read(ys, Ip.Grp{_ <> ys, 3n}, acc) : Ip.Read}
      {==}

def prd.begin_hex(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +acc: Ip.Acc) -> {Ip.read(Ip.Sym.of(c) <> ys, Ip.Begin{}, acc) == Ip.read(ys, Ip.Grp{Ip.Sym.of(c) <> ys, 3n}, acc) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(_ <> ys, Ip.Begin{}, acc) == Ip.read(ys, Ip.Grp{_ <> ys, 3n}, acc) : Ip.Read}
      {==}
    case Inr{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, d) : {Ip.read(_ <> ys, Ip.Begin{}, acc) == Ip.read(ys, Ip.Grp{_ <> ys, 3n}, acc) : Ip.Read}
      {==}

# the room a group leaves
def prd.room(g: String) -> Nat:
  match g:
    case SNil{}:
      3n
    case SCon{c, t}:
      Nat.sub(3n, String.length(t))

# a group read from where a group may start, up to the char after it
def prd.group_open(g: String, +X: List<&2, Ip.Sym>, +acc: Ip.Acc, +h: {S.group(g) == True{} : Bool}) -> {Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(g), X), Ip.Open{}, acc) == Ip.read(X, Ip.Grp{List.append(&2, Ip.Sym, Ip.Sym.list(g), X), prd.room(g)}, acc) : Ip.Read}:
  match g:
    case SNil{}:
      LIp.pip.absurd_ft({Ip.read(X, Ip.Open{}, acc) == Ip.read(X, Ip.Grp{X, 3n}, acc) : Ip.Read}, h)
    case SCon{+c, +t}:
      +hx = LIp.pip.and_l(S.all_hex(SCon{c, t}), Bool.and(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n)), h)
      +hl = LIp.pip.and_r(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n), LIp.pip.and_r(S.all_hex(SCon{c, t}), Bool.and(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n)), h))
      +hc = LIp.pip.and_l(S.hex(c), S.all_hex(t), hx)
      +ht = LIp.pip.and_r(S.hex(c), S.all_hex(t), hx)
      +ys = List.append(&2, Ip.Sym, Ip.Sym.list(t), X)
      Equal.trans(Ip.Read, Ip.read(Ip.Sym.of(c) <> ys, Ip.Open{}, acc), Ip.read(ys, Ip.Grp{Ip.Sym.of(c) <> ys, 3n}, acc), Ip.read(X, Ip.Grp{Ip.Sym.of(c) <> ys, Nat.sub(3n, String.length(t))}, acc), prd.open_hex(c, prd.hex_sym(c, hc), ys, acc), prd.read_hexes(t, X, Ip.Sym.of(c) <> ys, 3n, acc, ht, hl))

# a group read from the start of the text, up to the char after it
def prd.group_begin(g: String, +X: List<&2, Ip.Sym>, +acc: Ip.Acc, +h: {S.group(g) == True{} : Bool}) -> {Ip.read(List.append(&2, Ip.Sym, Ip.Sym.list(g), X), Ip.Begin{}, acc) == Ip.read(X, Ip.Grp{List.append(&2, Ip.Sym, Ip.Sym.list(g), X), prd.room(g)}, acc) : Ip.Read}:
  match g:
    case SNil{}:
      LIp.pip.absurd_ft({Ip.read(X, Ip.Begin{}, acc) == Ip.read(X, Ip.Grp{X, 3n}, acc) : Ip.Read}, h)
    case SCon{+c, +t}:
      +hx = LIp.pip.and_l(S.all_hex(SCon{c, t}), Bool.and(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n)), h)
      +hl = LIp.pip.and_r(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n), LIp.pip.and_r(S.all_hex(SCon{c, t}), Bool.and(Nat.is_le(1n, String.length(SCon{c, t})), Nat.is_le(String.length(SCon{c, t}), 4n)), h))
      +hc = LIp.pip.and_l(S.hex(c), S.all_hex(t), hx)
      +ht = LIp.pip.and_r(S.hex(c), S.all_hex(t), hx)
      +ys = List.append(&2, Ip.Sym, Ip.Sym.list(t), X)
      Equal.trans(Ip.Read, Ip.read(Ip.Sym.of(c) <> ys, Ip.Begin{}, acc), Ip.read(ys, Ip.Grp{Ip.Sym.of(c) <> ys, 3n}, acc), Ip.read(X, Ip.Grp{Ip.Sym.of(c) <> ys, Nat.sub(3n, String.length(t))}, acc), prd.begin_hex(c, prd.hex_sym(c, hc), ys, acc), prd.read_hexes(t, X, Ip.Sym.of(c) <> ys, 3n, acc, ht, hl))

# the group that started at start is g
def prd.group_is(+g: String, +X: List<&2, Ip.Sym>, +h: {S.all_hex(g) == True{} : Bool}, +hr: {Ip.run(X) == Ip.Cut{SNil{}, X} : Ip.Cut}) -> {Ip.group(List.append(&2, Ip.Sym, Ip.Sym.list(g), X)) == g : String}:
  %Equal.sym(Ip.Cut, Ip.run(List.append(&2, Ip.Sym, Ip.Sym.list(g), X)), Ip.Cut{String.append(g, prd.cut_s(Ip.run(X))), prd.cut_rest(Ip.run(X))}, prd.run_hex(g, X, h)) : {Ip.group.of(_) == g : String}
  %Equal.sym(Ip.Cut, Ip.run(X), Ip.Cut{SNil{}, X}, hr) : {String.append(g, prd.cut_s(_)) == g : String}
  prd.app_nil(g)

# The end of a group
# ------------------

def prd.grp_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, -start: List<&2, Ip.Sym>, -r: Nat, -acc: Ip.Acc, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.read(y <> ys, Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, y <> ys) : Ip.Read}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dig{c} <> ys, Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Dig{c} <> ys) : Ip.Read}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Hx{c} <> ys, Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Hx{c} <> ys) : Ip.Read}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> ys, Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Col{} <> ys) : Ip.Read}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dot{} <> ys, Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Dot{} <> ys) : Ip.Read}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def prd.open_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, -acc: Ip.Acc, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.read(y <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, y <> ys) : Ip.Read}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dig{c} <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Dig{c} <> ys) : Ip.Read}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Hx{c} <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Hx{c} <> ys) : Ip.Read}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Col{} <> ys) : Ip.Read}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dot{} <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Dot{} <> ys) : Ip.Read}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def prd.begin_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, -acc: Ip.Acc, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.read(y <> ys, Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dig{c} <> ys, Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Hx{c} <> ys, Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> ys, Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dot{} <> ys, Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def prd.stop_kind(+c: Char, +h: {S.k_stop6(S.kind(c)) == True{} : Bool}) -> {S.k_stop6(LIp.pip.kind(Ip.Sym.of(c))) == True{} : Bool}:
  %Equal.sym(S.CKind, LIp.pip.kind(Ip.Sym.of(c)), S.kind(c), LIp.pip.kind_of(c)) : {S.k_stop6(_) == True{} : Bool}
  h

def prd.grp_end(t: String, +start: List<&2, Ip.Sym>, +r: Nat, +acc: Ip.Acc, +h: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(t), Ip.Grp{start, r}, acc) == Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Sym.list(t)) : Ip.Read}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      prd.grp_stop(Ip.Sym.of(c), Ip.Sym.list(u), start, r, acc, prd.stop_kind(c, h))

def prd.open_end(t: String, +acc: Ip.Acc, +h: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(t), Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Sym.list(t)) : Ip.Read}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      prd.open_stop(Ip.Sym.of(c), Ip.Sym.list(u), acc, prd.stop_kind(c, h))

def prd.begin_end(t: String, +acc: Ip.Acc, +h: {S.stops6(t) == True{} : Bool}) -> {Ip.read(Ip.Sym.list(t), Ip.Begin{}, acc) == Ip.Bad{} : Ip.Read}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      prd.begin_stop(Ip.Sym.of(c), Ip.Sym.list(u), acc, prd.stop_kind(c, h))

def prd.run_end(t: String, +h: {S.stops6(t) == True{} : Bool}) -> {Ip.run(Ip.Sym.list(t)) == Ip.Cut{SNil{}, Ip.Sym.list(t)} : Ip.Cut}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      prd.run_stop(Ip.Sym.of(c), Ip.Sym.list(u), prd.stop_kind(c, h))

def prd.grp_sep(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +start: List<&2, Ip.Sym>, +r: Nat, +acc: Ip.Acc) -> {Ip.read(Ip.Col{} <> (Ip.Sym.of(c) <> ys), Ip.Grp{start, r}, acc) == Ip.read(Ip.Sym.of(c) <> ys, Ip.Open{}, Ip.Acc.push(acc, Ip.group(start))) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(Ip.Col{} <> (_ <> ys), Ip.Grp{start, r}, acc) == Ip.read(_ <> ys, Ip.Open{}, Ip.Acc.push(acc, Ip.group(start))) : Ip.Read}
      {==}
    case Inr{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, d) : {Ip.read(Ip.Col{} <> (_ <> ys), Ip.Grp{start, r}, acc) == Ip.read(_ <> ys, Ip.Open{}, Ip.Acc.push(acc, Ip.group(start))) : Ip.Read}
      {==}

# no hex digit, `:` or `.` is no decimal digit
def prd.stop6_dec(k: S.CKind, +h: {S.k_stop6(k) == True{} : Bool}) -> {S.k_dec(k) == False{} : Bool}:
  match k:
    case S.KDec{}:
      LIp.pip.absurd_ft({S.k_dec(S.KDec{}) == False{} : Bool}, h)
    case S.KHex{}:
      {==}
    case S.KCol{}:
      {==}
    case S.KDot{}:
      {==}
    case S.KLet{}:
      {==}
    case S.KUnd{}:
      {==}
    case S.KDash{}:
      {==}
    case S.KOth{}:
      {==}

def prd.not_true(b: Bool, +h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LIp.pip.absurd_ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# what does not go on with an IPv4 starts with no decimal digit
def prd.drun_end4(t: String, +h: {S.stops4(t) == True{} : Bool}) -> {Ip.drun(Ip.Sym.list(t)) == Ip.Cut{SNil{}, Ip.Sym.list(t)} : Ip.Cut}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +hk = prd.not_true(S.k_dec(S.kind(c)), h)
      prd.drun_stop(Ip.Sym.of(c), Ip.Sym.list(u), Equal.trans(Bool, S.k_dec(LIp.pip.kind(Ip.Sym.of(c))), S.k_dec(S.kind(c)), False{}, Equal.cong(S.CKind, Bool, k => S.k_dec(k), LIp.pip.kind(Ip.Sym.of(c)), S.kind(c), LIp.pip.kind_of(c)), hk))

def prd.stops6_4(t: String, +h: {S.stops6(t) == True{} : Bool}) -> {S.stops4(t) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, u}:
      %Equal.sym(Bool, S.k_dec(S.kind(c)), False{}, prd.stop6_dec(S.kind(c), h)) : {Bool.not(_) == True{} : Bool}
      {==}
