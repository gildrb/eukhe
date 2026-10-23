# eukhe: lemmas the proofs of area command share
#
# Shared lemmas of the proofs of LAWS.bend section commands
# (bend/command.bend): the logic and list kit, the model's helpers equal
# to the spec helpers (same/cmd_eq, by_path/cmd_lookup, kid/cmd_is_kid,
# lows/cmd_lower, join/cmd_render, ...), the words of a rendered line,
# and the walk over the names of a declared path. Lemma names: cb_.

import Base
import ../../bend/command.bend as Cmd
import ../../bend/ffi_command.bend as FCmd
import ../../bend/wire.bend as Wr
import ../../laws/command.bend as Command
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool.bend as LBool
import ../base/command.bend as LCommand
import ../base/list.bend as LList
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/wire.bend as LWire

def cb_absurd2(-G: Type, e: {True{} == False{} : Bool}) -> G:
  LLogicLogic.cb_absurd(G, Equal.sym(Bool, True{}, False{}, e))

def cb_or_false_l(+a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      cb_absurd2({True{} == False{} : Bool}, e)

def cb_or_false_r(+a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case False{}:
      e
    case True{}:
      cb_absurd2({b == False{} : Bool}, e)

def cb_not_true(+a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      LLogicLogic.cb_absurd({True{} == False{} : Bool}, e)

# Lists
# -----

def cb_app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %cb_app_nil(A, t) : {h <> List.append(&2, A, t, Nil{}) == h <> _ : List<&2, A>}
      {==}

def cb_nat_sym(x: Nat, y: Nat) -> {Nat.is_eq(x, y) == Nat.is_eq(y, x) : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cb_nat_sym(p, q)

def cb_eq_sym(a: List<&2, Nat>, b: List<&2, Nat>) -> {Command.cmd_eq(a, b) == Command.cmd_eq(b, a) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+y, +ys}:
      %cb_nat_sym(x, y) : {Bool.and(Nat.is_eq(x, y), Command.cmd_eq(xs, ys)) == Bool.and(_, Command.cmd_eq(ys, xs)) : Bool}
      %cb_eq_sym(xs, ys) : {Bool.and(Nat.is_eq(x, y), Command.cmd_eq(xs, ys)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
      {==}

# Lowercase
# ---------

def cb_le_lt(a: Nat, b: Nat) -> {Nat.is_le(a, b) == Bool.not(Nat.is_lt(b, a)) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cb_le_lt(p, q)

def cb_lt_zero(p: Nat) -> {False{} == Nat.is_lt(p, 0n) : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+r:
      {==}

def cb_le_succ(c: Nat, n: Nat) -> {Nat.is_le(c, n) == Nat.is_lt(c, 1n+n) : Bool}:
  match c n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      cb_lt_zero(p)
    case 1n+p 1n+q:
      cb_le_succ(p, q)

def cb_pick_up(b: Bool, -c: Nat) -> {Cmd.low.pick(b, c) == Command.cmd_lower.up(b, c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's low is cmd_lower.c
def cb_low(+c: Nat) -> {Cmd.low(c) == Command.cmd_lower.c(c) : Nat}:
  %cb_le_lt(65n, c) : {Cmd.low(c) == Command.cmd_lower.up(Bool.and(_, Nat.is_lt(c, 91n)), c) : Nat}
  %cb_le_succ(c, 90n) : {Cmd.low(c) == Command.cmd_lower.up(Bool.and(Nat.is_le(65n, c), _), c) : Nat}
  cb_pick_up(Bool.and(Nat.is_le(65n, c), Nat.is_le(c, 90n)), c)

# the model's lows is cmd_lower
def cb_lows(w: List<&2, Nat>) -> {Cmd.lows(w) == Command.cmd_lower(w) : List<&2, Nat>}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      %cb_lows(r) : {Cmd.low(c) <> Cmd.lows(r) == Command.cmd_lower.c(c) <> _ : List<&2, Nat>}
      %cb_low(c) : {Cmd.low(c) <> Cmd.lows(r) == _ <> Cmd.lows(r) : List<&2, Nat>}
      {==}

# a name is its own lowercase
def cb_name_low(+w: List<&2, Nat>, h: {Command.cmd_name_ok(w) == True{} : Bool}) -> {Command.cmd_lower(w) == w : List<&2, Nat>}:
  LLogicNat.cb_eq(Command.cmd_lower(w), w, LLogicBool.cb_and_r(Command.cmd_typed(w), Command.cmd_eq(Command.cmd_lower(w), w), h))

def cb_name_lows(+w: List<&2, Nat>, h: {Command.cmd_name_ok(w) == True{} : Bool}) -> {Cmd.lows(w) == w : List<&2, Nat>}:
  Equal.trans(List<&2, Nat>, Cmd.lows(w), Command.cmd_lower(w), w, cb_lows(w), cb_name_low(w, h))

# a typed word has no space
def cb_typed_spaceless(w: List<&2, Nat>, h: {Command.cmd_typed(w) == True{} : Bool}) -> {Command.cmd_spaceless(w) == True{} : Bool}:
  match w:
    case Nil{}:
      LLogicLogic.cb_absurd({Command.cmd_spaceless(Nil{}) == True{} : Bool}, h)
    case Con{c, r}:
      h

def cb_name_spaceless(+w: List<&2, Nat>, h: {Command.cmd_name_ok(w) == True{} : Bool}) -> {Command.cmd_spaceless(w) == True{} : Bool}:
  cb_typed_spaceless(w, LLogicBool.cb_and_l(Command.cmd_typed(w), Command.cmd_eq(Command.cmd_lower(w), w), h))

# Words
# -----

# the chars of w put before the first word of ws
def cb_put(w: List<&2, Nat>, ws: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match w:
    case Nil{}:
      ws
    case Con{c, r}:
      Cmd.put_word(c, cb_put(r, ws))

# the words of a spaceless w and then s: w joins the first word of s
def cb_words_app(w: List<&2, Nat>, -s: List<&2, Nat>, +h: {Command.cmd_spaceless(w) == True{} : Bool}) -> {Cmd.words(List.append(&2, Nat, w, s)) == cb_put(w, Cmd.words(s)) : List<&2, List<&2, Nat>>}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      +hc = LLogicBool.cb_and_l(Bool.not(Nat.is_eq(c, 32n)), Command.cmd_spaceless(r), h)
      %Equal.sym(Bool, Nat.is_eq(c, 32n), False{}, cb_not_true(Nat.is_eq(c, 32n), hc)) : {Cmd.words.at(_, c, Cmd.words(List.append(&2, Nat, r, s))) == Cmd.put_word(c, cb_put(r, Cmd.words(s))) : List<&2, List<&2, Nat>>}
      %cb_words_app(r, s, LLogicBool.cb_and_r(Bool.not(Nat.is_eq(c, 32n)), Command.cmd_spaceless(r), h)) : {Cmd.put_word(c, Cmd.words(List.append(&2, Nat, r, s))) == Cmd.put_word(c, _) : List<&2, List<&2, Nat>>}
      {==}

def cb_put_con(w: List<&2, Nat>, -v: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>) -> {cb_put(w, v <> rest) == List.append(&2, Nat, w, v) <> rest : List<&2, List<&2, Nat>>}:
  match w:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      %Equal.sym(List<&2, List<&2, Nat>>, cb_put(r, v <> rest), List.append(&2, Nat, r, v) <> rest, cb_put_con(r, v, rest)) : {Cmd.put_word(c, _) == (c <> List.append(&2, Nat, r, v)) <> rest : List<&2, List<&2, Nat>>}
      {==}

# the words of a space and then the rendered words of rest
def cb_words_sep(rest: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(rest) == True{} : Bool}) -> {Cmd.words(Command.cmd_sep(rest)) == Nil{} <> rest : List<&2, List<&2, Nat>>}:
  match rest:
    case Nil{}:
      {==}
    case Con{+v, +r}:
      +hv = LLogicBool.cb_and_l(Command.cmd_spaceless(v), Command.cmd_all_spaceless(r), h)
      %cb_app_nil(Nat, v) : {Nil{} <> Cmd.words(List.append(&2, Nat, v, Command.cmd_sep(r))) == Nil{} <> (_ <> r) : List<&2, List<&2, Nat>>}
      %cb_put_con(v, Nil{}, r) : {Nil{} <> Cmd.words(List.append(&2, Nat, v, Command.cmd_sep(r))) == Nil{} <> _ : List<&2, List<&2, Nat>>}
      %cb_words_sep(r, LLogicBool.cb_and_r(Command.cmd_spaceless(v), Command.cmd_all_spaceless(r), h)) : {Nil{} <> Cmd.words(List.append(&2, Nat, v, Command.cmd_sep(r))) == Nil{} <> cb_put(v, _) : List<&2, List<&2, Nat>>}
      %cb_words_app(v, Command.cmd_sep(r), hv) : {Nil{} <> Cmd.words(List.append(&2, Nat, v, Command.cmd_sep(r))) == Nil{} <> _ : List<&2, List<&2, Nat>>}
      {==}

# the words of a rendered nonempty list of spaceless words are the list
def cb_words_render(+x: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(x <> rest) == True{} : Bool}) -> {Cmd.words(Command.cmd_render(x <> rest)) == x <> rest : List<&2, List<&2, Nat>>}:
  %cb_app_nil(Nat, x) : {Cmd.words(Command.cmd_render(x <> rest)) == _ <> rest : List<&2, List<&2, Nat>>}
  %cb_put_con(x, Nil{}, rest) : {Cmd.words(Command.cmd_render(x <> rest)) == _ : List<&2, List<&2, Nat>>}
  %cb_words_sep(rest, LLogicBool.cb_and_r(Command.cmd_spaceless(x), Command.cmd_all_spaceless(rest), h)) : {Cmd.words(Command.cmd_render(x <> rest)) == cb_put(x, _) : List<&2, List<&2, Nat>>}
  cb_words_app(x, Command.cmd_sep(rest), LLogicBool.cb_and_l(Command.cmd_spaceless(x), Command.cmd_all_spaceless(rest), h))

# the words of q and then the words of r, spaceless, render to q ++ r
def cb_words_render_app(q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, h: {Command.cmd_all_spaceless(List.append(&2, List<&2, Nat>, q, w <> more)) == True{} : Bool}) -> {Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, w <> more))) == List.append(&2, List<&2, Nat>, q, w <> more) : List<&2, List<&2, Nat>>}:
  match q:
    case Nil{}:
      cb_words_render(w, more, h)
    case Con{+y, +ys}:
      cb_words_render(y, List.append(&2, List<&2, Nat>, ys, w <> more), h)

def cb_all_spaceless_app(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, +ha: {Command.cmd_all_spaceless(a) == True{} : Bool}, hb: {Command.cmd_all_spaceless(b) == True{} : Bool}) -> {Command.cmd_all_spaceless(List.append(&2, List<&2, Nat>, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      hb
    case Con{+w, +r}:
      LBool.cb_and_intro(Command.cmd_spaceless(w), Command.cmd_all_spaceless(List.append(&2, List<&2, Nat>, r, b)), LLogicBool.cb_and_l(Command.cmd_spaceless(w), Command.cmd_all_spaceless(r), ha), cb_all_spaceless_app(r, b, LLogicBool.cb_and_r(Command.cmd_spaceless(w), Command.cmd_all_spaceless(r), ha), hb))

# names are spaceless words
def cb_names_spaceless(ws: List<&2, List<&2, Nat>>, +h: {Command.cmd_names_ok(ws) == True{} : Bool}) -> {Command.cmd_all_spaceless(ws) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      LBool.cb_and_intro(Command.cmd_spaceless(w), Command.cmd_all_spaceless(r), cb_name_spaceless(w, LLogicBool.cb_and_l(Command.cmd_name_ok(w), Command.cmd_names_ok(r), h)), cb_names_spaceless(r, LLogicBool.cb_and_r(Command.cmd_name_ok(w), Command.cmd_names_ok(r), h)))

def cb_names_app_r(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, h: {Command.cmd_names_ok(List.append(&2, List<&2, Nat>, a, b)) == True{} : Bool}) -> {Command.cmd_names_ok(b) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case Con{+w, +r}:
      cb_names_app_r(r, b, LLogicBool.cb_and_r(Command.cmd_name_ok(w), Command.cmd_names_ok(List.append(&2, List<&2, Nat>, r, b)), h))

# the last name of a path of names is a name
def cb_names_last(+q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, h: {Command.cmd_names_ok(List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}) -> {Command.cmd_name_ok(x) == True{} : Bool}:
  LLogicBool.cb_and_l(Command.cmd_name_ok(x), True{}, cb_names_app_r(q, [x], h))

# the words before the last, and the last
def cb_cut_go(ws: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, -w: List<&2, Nat>) -> {Cmd.cut.go(List.append(&2, List<&2, Nat>, ws, [p]), w) == (w <> ws, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+v, +r}:
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(List.append(&2, List<&2, Nat>, r, [p]), v), (v <> r, p), cb_cut_go(r, p, v)) : {Cmd.cut.cons(w, _) == (w <> (v <> r), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}
      {==}

def cb_cut(ws: List<&2, List<&2, Nat>>, -p: List<&2, Nat>) -> {Cmd.cut(List.append(&2, List<&2, Nat>, ws, [p])) == (ws, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      cb_cut_go(r, p, w)

def cb_join_go(rest: List<&2, List<&2, Nat>>, +w: List<&2, Nat>) -> {Cmd.join.go(rest, w) == List.append(&2, Nat, w, Command.cmd_sep(rest)) : List<&2, Nat>}:
  match rest:
    case Nil{}:
      Equal.sym(List<&2, Nat>, List.append(&2, Nat, w, Nil{}), w, cb_app_nil(Nat, w))
    case Con{+v, +r}:
      %cb_join_go(r, v) : {List.append(&2, Nat, w, 32n <> Cmd.join.go(r, v)) == List.append(&2, Nat, w, 32n <> _) : List<&2, Nat>}
      {==}

# the model's join is cmd_render
def cb_join(ws: List<&2, List<&2, Nat>>) -> {Cmd.join(ws) == Command.cmd_render(ws) : List<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      cb_join_go(r, w)

# The table
# ---------

def cb_ent_path(e: Cmd.Ent) -> {Cmd.Ent.path(e) == Command.cmd_ent_path(e) : List<&2, List<&2, Nat>>}:
  match e:
    case Cmd.Ent{p, a, r, f, g}:
      {==}

def cb_pick(b: Bool, -e: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>) -> {Cmd.pick(b, e, m) == Command.cmd_first.at(b, e, m) : Maybe<&2, Cmd.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's by_path is cmd_lookup
def cb_by_path(t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> {Cmd.by_path(t, p) == Command.cmd_lookup(t, p) : Maybe<&2, Cmd.Ent>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      %cb_by_path(rest, p) : {Cmd.pick(Cmd.same_path(Cmd.Ent.path(e), p), e, Cmd.by_path(rest, p)) == Command.cmd_first.at(Command.cmd_path_eq(Command.cmd_ent_path(e), p), e, _) : Maybe<&2, Cmd.Ent>}
      %cb_ent_path(e) : {Cmd.pick(Cmd.same_path(Cmd.Ent.path(e), p), e, Cmd.by_path(rest, p)) == Command.cmd_first.at(Command.cmd_path_eq(_, p), e, Cmd.by_path(rest, p)) : Maybe<&2, Cmd.Ent>}
      %LCommand.cb_same_path(Cmd.Ent.path(e), p) : {Cmd.pick(Cmd.same_path(Cmd.Ent.path(e), p), e, Cmd.by_path(rest, p)) == Command.cmd_first.at(_, e, Cmd.by_path(rest, p)) : Maybe<&2, Cmd.Ent>}
      cb_pick(Cmd.same_path(Cmd.Ent.path(e), p), e, Cmd.by_path(rest, p))

def cb_and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def cb_kid_nil(q: List<&2, List<&2, Nat>>) -> {Cmd.kid(q, Nil{}) == False{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{x, xs}:
      {==}

def cb_kid_root(-y: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> {Cmd.kid(Nil{}, y <> ys) == Command.cmd_path_eq(Command.cmd_init.go(ys, y), Nil{}) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{z, zs}:
      {==}

# the model's kid is cmd_is_kid
def cb_kid(q: List<&2, List<&2, Nat>>, p: List<&2, List<&2, Nat>>) -> {Cmd.kid(q, p) == Command.cmd_is_kid(q, p) : Bool}:
  match q p:
    case Nil{} Nil{}:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Nil{} Con{+y, +ys}:
      cb_kid_root(y, ys)
    case Con{+x, +xs} Con{+y, Nil{}}:
      %Equal.sym(Bool, Cmd.kid(xs, Nil{}), False{}, cb_kid_nil(xs)) : {Bool.and(Cmd.same(x, y), _) == False{} : Bool}
      cb_and_false(Cmd.same(x, y))
    case Con{+x, +xs} Con{+y, Con{+z, +zs}}:
      %cb_kid(xs, z <> zs) : {Bool.and(Cmd.same(x, y), Cmd.kid(xs, z <> zs)) == Bool.and(Command.cmd_eq(y, x), _) : Bool}
      %cb_eq_sym(x, y) : {Bool.and(Cmd.same(x, y), Cmd.kid(xs, z <> zs)) == Bool.and(_, Cmd.kid(xs, z <> zs)) : Bool}
      %LCommand.cb_same(x, y) : {Bool.and(Cmd.same(x, y), Cmd.kid(xs, z <> zs)) == Bool.and(_, Cmd.kid(xs, z <> zs)) : Bool}
      {==}

# the model's kids.any is cmd_has_kid
def cb_kids_any(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>) -> {Cmd.kids.any(t, q) == Command.cmd_has_kid(t, q) : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{Cmd.Ent{+p, a, r, f, g}, +rest}:
      %cb_kids_any(rest, q) : {Bool.or(Cmd.kid(q, p), Cmd.kids.any(rest, q)) == Bool.or(Command.cmd_is_kid(q, p), _) : Bool}
      %cb_kid(q, p) : {Bool.or(Cmd.kid(q, p), Cmd.kids.any(rest, q)) == Bool.or(_, Cmd.kids.any(rest, q)) : Bool}
      {==}

# the model's has is cmd_in
def cb_has(xs: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.has(xs, x) == Command.cmd_in(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %cb_has(rest, x) : {Bool.or(Cmd.same(x, y), Cmd.has(rest, x)) == Bool.or(Command.cmd_eq(x, y), _) : Bool}
      %LCommand.cb_same(x, y) : {Bool.or(Cmd.same(x, y), Cmd.has(rest, x)) == Bool.or(_, Cmd.has(rest, x)) : Bool}
      {==}

def cb_last_go(p: List<&2, List<&2, Nat>>, -x: List<&2, Nat>) -> {Cmd.last.go(p, x) == Command.cmd_last.go(p, x) : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, rest}:
      cb_last_go(rest, y)

# the model's last is cmd_last
def cb_last(p: List<&2, List<&2, Nat>>) -> {Cmd.last(p) == Command.cmd_last(p) : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, rest}:
      cb_last_go(rest, x)

def cb_pick_false(-b: Bool, -e: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, h: {b == False{} : Bool}) -> {Cmd.pick(b, e, m) == m : Maybe<&2, Cmd.Ent>}:
  %Equal.sym(Bool, b, False{}, h) : {Cmd.pick(_, e, m) == m : Maybe<&2, Cmd.Ent>}
  {==}

def cb_alias_cond(+q: List<&2, List<&2, Nat>>, +p: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Bool.and(Cmd.kid(q, p), Cmd.has(a, x)) == Bool.and(Command.cmd_is_kid(q, p), Command.cmd_in(x, a)) : Bool}:
  %cb_has(a, x) : {Bool.and(Cmd.kid(q, p), Cmd.has(a, x)) == Bool.and(Command.cmd_is_kid(q, p), _) : Bool}
  %cb_kid(q, p) : {Bool.and(Cmd.kid(q, p), Cmd.has(a, x)) == Bool.and(_, Cmd.has(a, x)) : Bool}
  {==}

# no child of q has the alias x: by_alias finds none
def cb_alias_none(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +h: {Command.cmd_alias_kid(t, q, x) == False{} : Bool}) -> {Cmd.by_alias(t, q, x) == None{} : Maybe<&2, Cmd.Ent>}:
  match t:
    case Nil{}:
      {==}
    case Con{Cmd.Ent{+p, +a, +r, +f, +g}, +rest}:
      +b = Bool.and(Cmd.kid(q, p), Cmd.has(a, x))
      +c = Bool.and(Command.cmd_is_kid(q, p), Command.cmd_in(x, a))
      +hb = Equal.trans(Bool, b, c, False{}, cb_alias_cond(q, p, a, x), cb_or_false_l(c, Command.cmd_alias_kid(rest, q, x), h))
      Equal.trans(Maybe<&2, Cmd.Ent>, Cmd.pick(b, Cmd.Ent{p, a, r, f, g}, Cmd.by_alias(rest, q, x)), Cmd.by_alias(rest, q, x), None{}, cb_pick_false(b, Cmd.Ent{p, a, r, f, g}, Cmd.by_alias(rest, q, x), hb), cb_alias_none(rest, q, x, cb_or_false_r(c, Command.cmd_alias_kid(rest, q, x), h)))

# Declared paths
# --------------

def cb_some_none(m: Maybe<&2, Cmd.Ent>, h: {Command.cmd_some(m) == False{} : Bool}) -> {m == None{} : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      cb_absurd2({Some{e} == None{} : Maybe<&2, Cmd.Ent>}, h)

# the entry m (an answer of cmd_lookup) has the path p
def cb_fits(m: Maybe<&2, Cmd.Ent>, p: List<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      Command.cmd_path_eq(Command.cmd_ent_path(e), p)

def cb_fits_at(b: Bool, -e: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, -p: List<&2, List<&2, Nat>>, hb: {Command.cmd_path_eq(Command.cmd_ent_path(e), p) == b : Bool}, ih: {cb_fits(m, p) == True{} : Bool}) -> {cb_fits(Command.cmd_first.at(b, e, m), p) == True{} : Bool}:
  match b:
    case True{}:
      hb
    case False{}:
      ih

# cmd_lookup answers an entry of the path it was asked for
def cb_lookup_fits(t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>) -> {cb_fits(Command.cmd_lookup(t, p), p) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      cb_fits_at(Command.cmd_path_eq(Command.cmd_ent_path(e), p), e, Command.cmd_lookup(rest, p), p, {==}, cb_lookup_fits(rest, p))

def cb_decl_names_at(b: Bool, +q: List<&2, List<&2, Nat>>, +p: List<&2, List<&2, Nat>>, -e: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, hb: {Command.cmd_path_eq(q, p) == b : Bool}, hq: {Command.cmd_names_ok(q) == True{} : Bool}, d: {Command.cmd_some(Command.cmd_first.at(b, e, m)) == True{} : Bool}, ih: {Command.cmd_some(m) == True{} : Bool} -> {Command.cmd_names_ok(p) == True{} : Bool}) -> {Command.cmd_names_ok(p) == True{} : Bool}:
  match b:
    case True{}:
      %LLogicNat.cb_path_eq(q, p, hb) : {Command.cmd_names_ok(_) == True{} : Bool}
      hq
    case False{}:
      ih(d)

# in a well-formed table every name of a declared path is a name
def cb_decl_names(t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, d: {Command.cmd_declared(t, p) == True{} : Bool}) -> {Command.cmd_names_ok(p) == True{} : Bool}:
  match t:
    case Nil{}:
      LLogicLogic.cb_absurd({Command.cmd_names_ok(p) == True{} : Bool}, d)
    case Con{Cmd.Ent{+q, +a, +r, +f, +g}, +rest}:
      +hh = LLogicBool.cb_and_l(Bool.and(Command.cmd_names_ok(q), Command.cmd_names_ok(a)), Command.cmd_wf(rest), ok)
      cb_decl_names_at(Command.cmd_path_eq(q, p), q, p, Cmd.Ent{q, a, r, f, g}, Command.cmd_lookup(rest, p), {==}, LLogicBool.cb_and_l(Command.cmd_names_ok(q), Command.cmd_names_ok(a), hh), d, d2 => cb_decl_names(rest, p, LLogicBool.cb_and_r(Bool.and(Command.cmd_names_ok(q), Command.cmd_names_ok(a)), Command.cmd_wf(rest), ok), d2))

# every name of a walked path is a name
def cb_walks_names(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, ok: {Command.cmd_wf(t) == True{} : Bool}, h: {Command.cmd_walks(t, q) == True{} : Bool}) -> {Command.cmd_names_ok(q) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      cb_decl_names(t, x <> rest, ok, LList.cb_walks_decl(rest, x, t, Nil{}, h))

# the words of the line of a walked path q and a spaceless last word p
def cb_words_last(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, hp: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))) == List.append(&2, List<&2, Nat>, q, [p]) : List<&2, List<&2, Nat>>}:
  cb_words_render_app(q, p, Nil{}, cb_all_spaceless_app(q, [p], cb_names_spaceless(q, cb_walks_names(t, q, ok, on)), LBool.cb_and_intro(Command.cmd_spaceless(p), True{}, hp, {==})))

# ... and its cut: the path, and the last word
def cb_cut_last(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, hp: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.cut(Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])))) == (q, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p]))), List.append(&2, List<&2, Nat>, q, [p]), cb_words_last(t, q, p, ok, on, hp)) : {Cmd.cut(_) == (q, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}
  cb_cut(q, p)

# The walk
# --------

def cb_st.of(m: Maybe<&2, Cmd.Ent>, p: List<&2, List<&2, Nat>>) -> Cmd.St:
  match m:
    case None{}:
      Cmd.Stray{}
    case Some{e}:
      Cmd.Walk{p, e}

# the state of the walk at path q: the root, or q with its entry
def cb_st(t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>) -> Cmd.St:
  match q:
    case Nil{}:
      Cmd.Top{}
    case Con{+x, +rest}:
      cb_st.of(Command.cmd_lookup(t, x <> rest), x <> rest)

# q is the root or declared
def cb_at(t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Command.cmd_declared(t, x <> rest)

def cb_at_app(-t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, -x: List<&2, Nat>, d: {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}) -> {cb_at(t, List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}:
  match q:
    case Nil{}:
      d
    case Con{y, ys}:
      d

# a walked path is the root or declared
def cb_walks_at(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, h: {Command.cmd_walks(t, q) == True{} : Bool}) -> {cb_at(t, q) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      LList.cb_walks_decl(rest, x, t, Nil{}, h)

def cb_found(+e: Cmd.Ent, +p: List<&2, List<&2, Nat>>, h: {Command.cmd_path_eq(Command.cmd_ent_path(e), p) == True{} : Bool}) -> {Cmd.Ent.path(e) == p : List<&2, List<&2, Nat>>}:
  Equal.trans(List<&2, List<&2, Nat>>, Cmd.Ent.path(e), Command.cmd_ent_path(e), p, cb_ent_path(e), LLogicNat.cb_path_eq(Command.cmd_ent_path(e), p, h))

def cb_land_walk(m: Maybe<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, -f: Bool, -w: List<&2, Nat>, +p: List<&2, List<&2, Nat>>, hs: {Command.cmd_some(m) == True{} : Bool}, hf: {cb_fits(m, p) == True{} : Bool}) -> {Cmd.step.walk(m, q, f, w) == cb_st.of(m, p) : Cmd.St}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.step.walk(None{}, q, f, w) == cb_st.of(None{}, p) : Cmd.St}, hs)
    case Some{+e}:
      %cb_found(e, p, hf) : {Cmd.Walk{Cmd.Ent.path(e), e} == Cmd.Walk{_, e} : Cmd.St}
      {==}

def cb_land_top(m: Maybe<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, hs: {Command.cmd_some(m) == True{} : Bool}, hf: {cb_fits(m, p) == True{} : Bool}) -> {Cmd.step.top(m) == cb_st.of(m, p) : Cmd.St}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.step.top(None{}) == cb_st.of(None{}, p) : Cmd.St}, hs)
    case Some{+e}:
      %cb_found(e, p, hf) : {Cmd.Walk{Cmd.Ent.path(e), e} == Cmd.Walk{_, e} : Cmd.St}
      {==}

def cb_alias_some(m: Maybe<&2, Cmd.Ent>, -t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, -x: List<&2, Nat>, h: {Command.cmd_some(m) == True{} : Bool}) -> {Cmd.search.alias(m, t, q, x) == m : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.search.alias(None{}, t, q, x) == None{} : Maybe<&2, Cmd.Ent>}, h)
    case Some{e}:
      {==}

# a word whose lowercase x names a declared child of q finds it
def cb_search_hit(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +x: List<&2, Nat>, hl: {Cmd.lows(w) == x : List<&2, Nat>}, hd: {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}) -> {Cmd.search(t, q, Cmd.lows(w)) == Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])) : Maybe<&2, Cmd.Ent>}:
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  %Equal.sym(List<&2, Nat>, Cmd.lows(w), x, hl) : {Cmd.search(t, q, _) == Command.cmd_lookup(t, qx) : Maybe<&2, Cmd.Ent>}
  %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.by_path(t, qx), Command.cmd_lookup(t, qx), cb_by_path(t, qx)) : {Cmd.search.alias(_, t, q, x) == Command.cmd_lookup(t, qx) : Maybe<&2, Cmd.Ent>}
  cb_alias_some(Command.cmd_lookup(t, qx), t, q, x, hd)

# a word whose lowercase x names no child of q finds none
def cb_search_miss(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +x: List<&2, Nat>, hl: {Cmd.lows(w) == x : List<&2, Nat>}, +miss: {Command.cmd_takes(t, q, x) == False{} : Bool}) -> {Cmd.search(t, q, Cmd.lows(w)) == None{} : Maybe<&2, Cmd.Ent>}:
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  +hn = cb_or_false_l(Command.cmd_declared(t, qx), Command.cmd_alias_kid(t, q, x), miss)
  %Equal.sym(List<&2, Nat>, Cmd.lows(w), x, hl) : {Cmd.search(t, q, _) == None{} : Maybe<&2, Cmd.Ent>}
  %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.by_path(t, qx), Command.cmd_lookup(t, qx), cb_by_path(t, qx)) : {Cmd.search.alias(_, t, q, x) == None{} : Maybe<&2, Cmd.Ent>}
  %Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, qx), None{}, cb_some_none(Command.cmd_lookup(t, qx), hn)) : {Cmd.search.alias(_, t, q, x) == None{} : Maybe<&2, Cmd.Ent>}
  cb_alias_none(t, q, x, cb_or_false_r(Command.cmd_declared(t, qx), Command.cmd_alias_kid(t, q, x), miss))

# a step on a typed word is a step on a nonempty word
def cb_step_word(w: List<&2, Nat>, -s: Cmd.St, -t: List<&2, Cmd.Ent>, h: {Command.cmd_typed(w) == True{} : Bool}) -> {Cmd.step(s, t, w) == Cmd.step.word(s, t, w) : Cmd.St}:
  match w:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.step(s, t, Nil{}) == Cmd.step.word(s, t, Nil{}) : Cmd.St}, h)
    case Con{c, r}:
      {==}

def cb_step_walk(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hs: {Command.cmd_some(m) == True{} : Bool}, +hx: {Command.cmd_name_ok(x) == True{} : Bool}, +d: {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}) -> {Cmd.step(cb_st.of(m, q), t, x) == cb_st.of(Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])), List.append(&2, List<&2, Nat>, q, [x])) : Cmd.St}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.step(cb_st.of(None{}, q), t, x) == cb_st.of(Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])), List.append(&2, List<&2, Nat>, q, [x])) : Cmd.St}, hs)
    case Some{+e}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{q, e}, t, x), Cmd.step.word(Cmd.Walk{q, e}, t, x), cb_step_word(x, Cmd.Walk{q, e}, t, LLogicBool.cb_and_l(Command.cmd_typed(x), Command.cmd_eq(Command.cmd_lower(x), x), hx))) : {_ == cb_st.of(Command.cmd_lookup(t, qx), qx) : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, q, Cmd.lows(x)), Command.cmd_lookup(t, qx), cb_search_hit(t, q, x, x, cb_name_lows(x, hx), d)) : {Cmd.step.walk(_, q, Cmd.Ent.free(e), x) == cb_st.of(Command.cmd_lookup(t, qx), qx) : Cmd.St}
      cb_land_walk(Command.cmd_lookup(t, qx), q, Cmd.Ent.free(e), x, qx, d, cb_lookup_fits(t, qx))

# one step of the walk: from the state of q, a declared child's name
# lands on the state of the child
def cb_step(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +ok: {Command.cmd_wf(t) == True{} : Bool}, at: {cb_at(t, q) == True{} : Bool}, +d: {Command.cmd_declared(t, List.append(&2, List<&2, Nat>, q, [x])) == True{} : Bool}) -> {Cmd.step(cb_st(t, q), t, x) == cb_st(t, List.append(&2, List<&2, Nat>, q, [x])) : Cmd.St}:
  match q:
    case Nil{}:
      +hx = cb_names_last(Nil{}, x, cb_decl_names(t, [x], ok, d))
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Top{}, t, x), Cmd.step.word(Cmd.Top{}, t, x), cb_step_word(x, Cmd.Top{}, t, LLogicBool.cb_and_l(Command.cmd_typed(x), Command.cmd_eq(Command.cmd_lower(x), x), hx))) : {_ == cb_st.of(Command.cmd_lookup(t, [x]), [x]) : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, Nil{}, Cmd.lows(x)), Command.cmd_lookup(t, [x]), cb_search_hit(t, Nil{}, x, x, cb_name_lows(x, hx), d)) : {Cmd.step.top(_) == cb_st.of(Command.cmd_lookup(t, [x]), [x]) : Cmd.St}
      cb_land_top(Command.cmd_lookup(t, [x]), [x], d, cb_lookup_fits(t, [x]))
    case Con{+y, +ys}:
      +hx = cb_names_last(y <> ys, x, cb_decl_names(t, List.append(&2, List<&2, Nat>, y <> ys, [x]), ok, d))
      cb_step_walk(Command.cmd_lookup(t, y <> ys), t, y <> ys, x, at, hx, d)

# the walk lemma: from the state of q (the root, or q declared), the
# names of r whose prefixes after q are declared land on the state of
# q ++ r
def cb_walk(r: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, at: {cb_at(t, q) == True{} : Bool}, +h: {Command.cmd_walks.go(r, t, q) == True{} : Bool}) -> {Cmd.walk(r, t, cb_st(t, q)) == cb_st(t, List.append(&2, List<&2, Nat>, q, r)) : Cmd.St}:
  match r:
    case Nil{}:
      %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, q, Nil{}), q, cb_app_nil(List<&2, Nat>, q)) : {cb_st(t, q) == cb_st(t, _) : Cmd.St}
      {==}
    case Con{+x, +more}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      +d = LLogicBool.cb_and_l(Command.cmd_declared(t, qx), Command.cmd_walks.go(more, t, qx), h)
      %Equal.sym(Cmd.St, Cmd.step(cb_st(t, q), t, x), cb_st(t, qx), cb_step(t, q, x, ok, at, d)) : {Cmd.walk(more, t, _) == cb_st(t, List.append(&2, List<&2, Nat>, q, x <> more)) : Cmd.St}
      %LList.cb_app_assoc(List<&2, Nat>, q, [x], more) : {Cmd.walk(more, t, cb_st(t, qx)) == cb_st(t, _) : Cmd.St}
      cb_walk(more, t, qx, ok, cb_at_app(t, q, x, d), LLogicBool.cb_and_r(Command.cmd_declared(t, qx), Command.cmd_walks.go(more, t, qx), h))

# the walk of a walked path from the root lands on its state
def cb_walk_root(r: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, ok: {Command.cmd_wf(t) == True{} : Bool}, h: {Command.cmd_walks(t, r) == True{} : Bool}) -> {Cmd.walk(r, t, Cmd.Top{}) == cb_st(t, r) : Cmd.St}:
  cb_walk(r, t, Nil{}, ok, {==}, h)

# a walk over a ++ b is a walk over a, then over b
def cb_walk_app(a: List<&2, List<&2, Nat>>, -b: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, s: Cmd.St) -> {Cmd.walk(List.append(&2, List<&2, Nat>, a, b), t, s) == Cmd.walk(b, t, Cmd.walk(a, t, s)) : Cmd.St}:
  match a:
    case Nil{}:
      {==}
    case Con{+w, r}:
      cb_walk_app(r, b, t, Cmd.step(s, t, w))

def cb_step_rest(w: List<&2, Nat>, -t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, -ws: List<&2, List<&2, Nat>>) -> {Cmd.step(Cmd.Rest{q, ws}, t, w) == Cmd.Rest{q, List.append(&2, List<&2, Nat>, ws, [w])} : Cmd.St}:
  match w:
    case Nil{}:
      {==}
    case Con{c, r}:
      {==}

# argument text takes every word after it
def cb_walk_rest(r: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +ws: List<&2, List<&2, Nat>>) -> {Cmd.walk(r, t, Cmd.Rest{q, ws}) == Cmd.Rest{q, List.append(&2, List<&2, Nat>, ws, r)} : Cmd.St}:
  match r:
    case Nil{}:
      %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, ws, Nil{}), ws, cb_app_nil(List<&2, Nat>, ws)) : {Cmd.Rest{q, ws} == Cmd.Rest{q, _} : Cmd.St}
      {==}
    case Con{+w, +more}:
      +ww = List.append(&2, List<&2, Nat>, ws, [w])
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Rest{q, ws}, t, w), Cmd.Rest{q, ww}, cb_step_rest(w, t, q, ws)) : {Cmd.walk(more, t, _) == Cmd.Rest{q, List.append(&2, List<&2, Nat>, ws, w <> more)} : Cmd.St}
      %LList.cb_app_assoc(List<&2, Nat>, ws, [w], more) : {Cmd.walk(more, t, Cmd.Rest{q, ww}) == Cmd.Rest{q, _} : Cmd.St}
      cb_walk_rest(more, t, q, ww)

def cb_step_lost(w: List<&2, Nat>, -t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, -x: List<&2, Nat>) -> {Cmd.step(Cmd.Lost{q, x}, t, w) == Cmd.Lost{q, x} : Cmd.St}:
  match w:
    case Nil{}:
      {==}
    case Con{c, r}:
      {==}

# an unknown word stays
def cb_walk_lost(r: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, -x: List<&2, Nat>) -> {Cmd.walk(r, t, Cmd.Lost{q, x}) == Cmd.Lost{q, x} : Cmd.St}:
  match r:
    case Nil{}:
      {==}
    case Con{+w, more}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Lost{q, x}, t, w), Cmd.Lost{q, x}, cb_step_lost(w, t, q, x)) : {Cmd.walk(more, t, _) == Cmd.Lost{q, x} : Cmd.St}
      cb_walk_lost(more, t, q, x)

def cb_step_stray(w: List<&2, Nat>, -t: List<&2, Cmd.Ent>) -> {Cmd.step(Cmd.Stray{}, t, w) == Cmd.Stray{} : Cmd.St}:
  match w:
    case Nil{}:
      {==}
    case Con{c, r}:
      {==}

# a stray first word stays
def cb_walk_stray(r: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>) -> {Cmd.walk(r, t, Cmd.Stray{}) == Cmd.Stray{} : Cmd.St}:
  match r:
    case Nil{}:
      {==}
    case Con{+w, more}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Stray{}, t, w), Cmd.Stray{}, cb_step_stray(w, t)) : {Cmd.walk(more, t, _) == Cmd.Stray{} : Cmd.St}
      cb_walk_stray(more, t)

# where a word that names no child of q lands: a stray first word, or
# below a declared q the start of its text or an unknown word
def cb_miss(t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, w: List<&2, Nat>) -> Cmd.St:
  match q:
    case Nil{}:
      Cmd.Stray{}
    case Con{+x, +rest}:
      Cmd.step.miss(Command.cmd_free(t, x <> rest), x <> rest, w)

def cb_miss_walk(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, hs: {Command.cmd_some(m) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.step(cb_st.of(m, q), t, w) == Cmd.step.miss(Command.cmd_free.of(m), q, w) : Cmd.St}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.step(cb_st.of(None{}, q), t, w) == Cmd.step.miss(Command.cmd_free.of(None{}), q, w) : Cmd.St}, hs)
    case Some{Cmd.Ent{+p, +a, +r, +f, +g}}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{q, Cmd.Ent{p, a, r, f, g}}, t, w), Cmd.step.word(Cmd.Walk{q, Cmd.Ent{p, a, r, f, g}}, t, w), cb_step_word(w, Cmd.Walk{q, Cmd.Ent{p, a, r, f, g}}, t, hw)) : {_ == Cmd.step.miss(f, q, w) : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, q, Cmd.lows(w)), None{}, cb_search_miss(t, q, w, Command.cmd_lower(w), cb_lows(w), miss)) : {Cmd.step.walk(_, q, f, w) == Cmd.step.miss(f, q, w) : Cmd.St}
      {==}

# the miss step: from the state of q (the root, or q declared), a typed
# word that names no child of q lands on cb_miss
def cb_step_miss(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, at: {cb_at(t, q) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.step(cb_st(t, q), t, w) == cb_miss(t, q, w) : Cmd.St}:
  match q:
    case Nil{}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Top{}, t, w), Cmd.step.word(Cmd.Top{}, t, w), cb_step_word(w, Cmd.Top{}, t, hw)) : {_ == Cmd.Stray{} : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, Nil{}, Cmd.lows(w)), None{}, cb_search_miss(t, Nil{}, w, Command.cmd_lower(w), cb_lows(w), miss)) : {Cmd.step.top(_) == Cmd.Stray{} : Cmd.St}
      {==}
    case Con{+y, +ys}:
      cb_miss_walk(Command.cmd_lookup(t, y <> ys), t, y <> ys, w, at, hw, miss)

# the names of a walked path q, a typed word w that names no child of
# q, then more: the walk lands on cb_miss, then takes more
def cb_walk_miss(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_typed(w) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.walk(List.append(&2, List<&2, Nat>, q, w <> more), t, Cmd.Top{}) == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}:
  %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, q, w <> more), t, Cmd.Top{}), Cmd.walk(w <> more, t, Cmd.walk(q, t, Cmd.Top{})), cb_walk_app(q, w <> more, t, Cmd.Top{})) : {_ == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(q, t, Cmd.Top{}), cb_st(t, q), cb_walk_root(q, t, ok, on)) : {Cmd.walk(w <> more, t, _) == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.step(cb_st(t, q), t, w), cb_miss(t, q, w), cb_step_miss(t, q, w, cb_walks_at(t, q, on), word, miss)) : {Cmd.walk(more, t, _) == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}
  {==}

# the same from the line of those words (all spaceless)
def cb_line_miss(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +more: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, +word: {Command.cmd_typed(w) == True{} : Bool}, after: {Command.cmd_all_spaceless(more) == True{} : Bool}, miss: {Command.cmd_takes(t, q, Command.cmd_lower(w)) == False{} : Bool}) -> {Cmd.walk(Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, w <> more))), t, Cmd.Top{}) == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}:
  +line = List.append(&2, List<&2, Nat>, q, w <> more)
  +hs = cb_all_spaceless_app(q, w <> more, cb_names_spaceless(q, cb_walks_names(t, q, ok, on)), LBool.cb_and_intro(Command.cmd_spaceless(w), Command.cmd_all_spaceless(more), cb_typed_spaceless(w, word), after))
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_render(line)), line, cb_words_render_app(q, w, more, hs)) : {Cmd.walk(_, t, Cmd.Top{}) == Cmd.walk(more, t, cb_miss(t, q, w)) : Cmd.St}
  cb_walk_miss(t, q, w, more, ok, on, word, miss)

# a walk at a declared path q answers through the row of the selection
# at q
def kr_st_of(m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, s: {Command.cmd_some(m) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(cb_st.of(m, q), t, line, p, sel, k) : Cmd.Out}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(cb_st.of(None{}, q), t, line, p, sel, k) : Cmd.Out}, s)
    case Some{e}:
      {==}

# the walk over a declared path q (or the root) answers through the row
# of the selection at q
def kr_walked(q: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == Cmd.key.at(Cmd.walk(q, t, Cmd.Top{}), t, line, p, sel, k) : Cmd.Out}:
  match q:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Cmd.St, Cmd.walk(x <> rest, t, Cmd.Top{}), cb_st(t, x <> rest), cb_walk_root(x <> rest, t, ok, on)) : {Cmd.key.row(Cmd.row(sel, t, x <> rest), k, t, line, p) == Cmd.key.at(_, t, line, p, sel, k) : Cmd.Out}
      kr_st_of(Command.cmd_lookup(t, x <> rest), x <> rest, t, line, p, sel, k, LList.cb_walks_decl(rest, x, t, Nil{}, on))

# the line q p: Tab or Enter answers through the row of the selection at q
def kr_key(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key(t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), sel, k) : Cmd.Out}:
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])))), (q, p), cb_cut_last(t, q, p, ok, on, word)) : {Cmd.key.row(Cmd.row(sel, t, q), k, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p) == Cmd.key.cut(_, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), sel, k) : Cmd.Out}
  kr_walked(q, t, Command.cmd_render(List.append(&2, List<&2, Nat>, q, [p])), p, sel, k, ok, on)

# a place that holds the child e of q gives the row e
def kr_hit_kid(e: Cmd.Ent, +q: List<&2, List<&2, Nat>>, c: {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == True{} : Bool}) -> {Some{e} == Cmd.row.kid(Cmd.kid(q, Cmd.Ent.path(e)), e) : Maybe<&2, Cmd.Ent>}:
  match e:
    case Cmd.Ent{+pp, a, r, f, g}:
      %Equal.sym(Bool, Cmd.kid(q, pp), Command.cmd_is_kid(q, pp), cb_kid(q, pp)) : {Some{Cmd.Ent{pp, a, r, f, g}} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      %Equal.sym(Bool, Command.cmd_is_kid(q, pp), True{}, c) : {Some{Cmd.Ent{pp, a, r, f, g}} == Cmd.row.kid(_, Cmd.Ent{pp, a, r, f, g}) : Maybe<&2, Cmd.Ent>}
      {==}

def kr_hit(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +i: Nat, +e: Cmd.Ent, at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}, c: {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == True{} : Bool}) -> {Some{e} == Cmd.row(Cmd.Row{i}, t, q) : Maybe<&2, Cmd.Ent>}:
  %Equal.sym(Maybe<&2, Cmd.Ent>, List.get(&2, Cmd.Ent, t, i), Some{e}, at) : {Some{e} == Cmd.row.of(_, q) : Maybe<&2, Cmd.Ent>}
  kr_hit_kid(e, q, c)

# ---- lists of strings ----

# the items of a list of strings, then rest
def cfr_ss_items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, cfr_ss_items(t, rest))

def cfr_ss_put_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), cfr_ss_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), cfr_ss_items(t, rest)), cfr_ss_put_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, cfr_ss_items(t, rest))) : Nat & String}
      {==}

# a list of strings is its count, then its items
def cfr_ss_put(+xs: List<&2, String>, -rest: String) -> {Wr.put_list(~String, ~Wr.put_str, xs, rest) == Wr.put_nat(List.length(&2, String, xs), cfr_ss_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), cfr_ss_items(xs, rest)), cfr_ss_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, String, xs), cfr_ss_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def cfr_ss_go_rt(+t: List<&2, String>, +x: String, +rest: String, +hf: {Command.cmd_strs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, cfr_ss_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, cfr_ss_items(u, rest)))), Wr.Got{x, Wr.put_str(y, cfr_ss_items(u, rest))}, Wire.wire_str_round_trip(x, Wr.put_str(y, cfr_ss_items(u, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), Command.cmd_strs_all(y <> u), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(y, cfr_ss_items(u, rest)))), Wr.Got{y <> u, rest}, cfr_ss_go_rt(u, y, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(x)), Command.cmd_strs_all(y <> u), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

# a list of strings that fits reads back
def cfr_strs_rt(+xs: List<&2, String>, +rest: String, h: {Command.cmd_strs_fit(xs) == True{} : Bool}) -> {FCmd.get_strs(FCmd.put_strs(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, x <> t, r), Wr.put_nat(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r)), cfr_ss_put(x <> t, r)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r))), Wr.Got{List.length(&2, String, x <> t), cfr_ss_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, String, x <> t), cfr_ss_items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, String, x <> t)), Command.cmd_strs_all(x <> t), hh))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      cfr_ss_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, x <> t)), Command.cmd_strs_all(x <> t), hh))
