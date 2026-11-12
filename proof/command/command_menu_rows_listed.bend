# eukhe: the proof of LAW command_menu_rows_listed
#
# PROOF of LAW command_menu_rows_listed: the line's words are pre's words
# and p (nm_menu_pre), so its menu is the menu at the walk of pre's words;
# a menu of children of q comes only from a walk at q (KB.kb_inv), whose
# places are the model's items of q from 0 for p in lowercase (ml_xs).
# Those items, from 1 + n, are the items from n each one up (ml_shift),
# so place i is listed exactly when the entry at place i passes the test
# (ml_in: by induction on the table, place 0 the head's test, place 1 + k
# place k of the rest), and they rise from n (ml_rise: each listed place
# is the current n, every later one is past it).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA
import ./base/named.bend as LANamed
import ./base/keys.bend as KB

# the model's starts is cmd_prefix
def cb_starts(x: List<&2, Nat>, n: List<&2, Nat>) -> {Cmd.starts(x, n) == Command.cmd_prefix(x, n) : Bool}:
  match x n:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      {==}
    case Con{a, as} Nil{}:
      {==}
    case Con{+a, +as} Con{+y, +ys}:
      %cb_starts(as, ys) : {Bool.and(Nat.is_eq(a, y), Cmd.starts(as, ys)) == Bool.and(Nat.is_eq(a, y), _) : Bool}
      {==}

# the model's has_start is cmd_prefix_in
def cb_has_start(xs: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.has_start(xs, x) == Command.cmd_prefix_in(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      %cb_has_start(rest, x) : {Bool.or(Cmd.starts(x, y), Cmd.has_start(rest, x)) == Bool.or(Command.cmd_prefix(x, y), _) : Bool}
      %cb_starts(x, y) : {Bool.or(Cmd.starts(x, y), Cmd.has_start(rest, x)) == Bool.or(_, Cmd.has_start(rest, x)) : Bool}
      {==}

# the model's test of an entry is the law's
def cb_row_cond(+q: List<&2, List<&2, Nat>>, +p: List<&2, List<&2, Nat>>, +a: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, Command.cmd_last(p)), Command.cmd_prefix_in(x, a))) : Bool}:
  %cb_has_start(a, x) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, Command.cmd_last(p)), _)) : Bool}
  %LA.cb_last(p) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(Command.cmd_prefix(x, _), Cmd.has_start(a, x))) : Bool}
  %cb_starts(x, Cmd.last(p)) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(Command.cmd_is_kid(q, p), Bool.or(_, Cmd.has_start(a, x))) : Bool}
  %LA.cb_kid(q, p) : {Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) == Bool.and(_, Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x))) : Bool}
  {==}

# ---- the places ----

# each place one up
def ml_succs(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, rest}:
      (1n+x) <> ml_succs(rest)

def ml_items_at(b: Bool, -n: Nat, -ys: List<&2, Nat>) -> {Cmd.items.at(b, 1n+n, ml_succs(ys)) == ml_succs(Cmd.items.at(b, n, ys)) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the items from 1 + n are the items from n, each one up
def ml_shift(t: List<&2, Cmd.Ent>, +n: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.items(t, 1n+n, q, x) == ml_succs(Cmd.items(t, n, q, x)) : List<&2, Nat>}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      +C = Bool.and(Cmd.kid(q, Cmd.Ent.path(e)), Cmd.opens_with(x, e))
      +Y = Cmd.items(rest, 1n+n, q, x)
      %Equal.sym(List<&2, Nat>, Cmd.items(rest, 1n+(1n+n), q, x), ml_succs(Y), ml_shift(rest, 1n+n, q, x)) : {Cmd.items.at(C, 1n+n, _) == ml_succs(Cmd.items.at(C, n, Y)) : List<&2, Nat>}
      ml_items_at(C, n, Y)

# no place one up is 0
def ml_in_zero(ys: List<&2, Nat>) -> {Command.cmd_nat_in(0n, ml_succs(ys)) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, r}:
      ml_in_zero(r)

# 1 + k is a place one up exactly when k is a place
def ml_in_succ(+k: Nat, ys: List<&2, Nat>) -> {Command.cmd_nat_in(1n+k, ml_succs(ys)) == Command.cmd_nat_in(k, ys) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, r}:
      %ml_in_succ(k, r) : {Bool.or(Nat.is_eq(y, k), Command.cmd_nat_in(1n+k, ml_succs(r))) == Bool.or(Nat.is_eq(y, k), _) : Bool}
      {==}

def ml_zero(b: Bool, ys: List<&2, Nat>) -> {Command.cmd_nat_in(0n, Cmd.items.at(b, 0n, ml_succs(ys))) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ml_in_zero(ys)

def ml_succ(b: Bool, +k: Nat, ys: List<&2, Nat>) -> {Command.cmd_nat_in(1n+k, Cmd.items.at(b, 0n, ml_succs(ys))) == Command.cmd_nat_in(k, ys) : Bool}:
  match b:
    case True{}:
      ml_in_succ(k, ys)
    case False{}:
      ml_in_succ(k, ys)

# at place 0 the head's test
def ml_head(c: Cmd.Ent, +rest: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Command.cmd_nat_in(0n, Cmd.items(c <> rest, 0n, q, x)) == Command.cmd_listed(c <> rest, 0n, q, x) : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      +C = Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x)))
      +Y = Cmd.items(rest, 0n, q, x)
      %Equal.sym(List<&2, Nat>, Cmd.items(rest, 1n, q, x), ml_succs(Y), ml_shift(rest, 0n, q, x)) : {Command.cmd_nat_in(0n, Cmd.items.at(C, 0n, _)) == Command.cmd_listed(Cmd.Ent{p, a, r, f, g} <> rest, 0n, q, x) : Bool}
      Equal.trans(Bool, Command.cmd_nat_in(0n, Cmd.items.at(C, 0n, ml_succs(Y))), C, Command.cmd_listed.of(Some{Cmd.Ent{p, a, r, f, g}}, q, x), ml_zero(C, Y), cb_row_cond(q, p, a, x))

# at place 1 + k place k of the rest
def ml_tail(c: Cmd.Ent, +rest: List<&2, Cmd.Ent>, +k: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, ih: {Command.cmd_nat_in(k, Cmd.items(rest, 0n, q, x)) == Command.cmd_listed(rest, k, q, x) : Bool}) -> {Command.cmd_nat_in(1n+k, Cmd.items(c <> rest, 0n, q, x)) == Command.cmd_listed(c <> rest, 1n+k, q, x) : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      +C = Bool.and(Cmd.kid(q, p), Bool.or(Cmd.starts(x, Cmd.last(p)), Cmd.has_start(a, x)))
      +Y = Cmd.items(rest, 0n, q, x)
      %Equal.sym(List<&2, Nat>, Cmd.items(rest, 1n, q, x), ml_succs(Y), ml_shift(rest, 0n, q, x)) : {Command.cmd_nat_in(1n+k, Cmd.items.at(C, 0n, _)) == Command.cmd_listed(rest, k, q, x) : Bool}
      Equal.trans(Bool, Command.cmd_nat_in(1n+k, Cmd.items.at(C, 0n, ml_succs(Y))), Command.cmd_nat_in(k, Y), Command.cmd_listed(rest, k, q, x), ml_succ(C, k, Y), ih)

# place i is listed exactly when the entry at place i passes the test
def ml_in(t: List<&2, Cmd.Ent>, +i: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Command.cmd_nat_in(i, Cmd.items(t, 0n, q, x)) == Command.cmd_listed(t, i, q, x) : Bool}:
  match t:
    case Nil{}:
      match i:
        case 0n:
          {==}
        case 1n+k:
          {==}
    case Con{c, +rest}:
      match i:
        case 0n:
          ml_head(c, rest, q, x)
        case 1n+k:
          ml_tail(c, rest, k, q, x, ml_in(rest, k, q, x))

def ml_rise_at(b: Bool, +lo: Nat, +n: Nat, -ys: List<&2, Nat>, h: {Nat.is_le(lo, n) == True{} : Bool}, ih1: {Command.cmd_rising(ys, 1n+n) == True{} : Bool}, ih2: {Command.cmd_rising(ys, lo) == True{} : Bool}) -> {Command.cmd_rising(Cmd.items.at(b, n, ys), lo) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_le(lo, n), True{}, h) : {Bool.and(_, Command.cmd_rising(ys, 1n+n)) == True{} : Bool}
      ih1
    case False{}:
      ih2

# the items from n rise from any lo up to n
def ml_rise(t: List<&2, Cmd.Ent>, +n: Nat, +lo: Nat, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +h: {Nat.is_le(lo, n) == True{} : Bool}) -> {Command.cmd_rising(Cmd.items(t, n, q, x), lo) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +rest}:
      ml_rise_at(Bool.and(Cmd.kid(q, Cmd.Ent.path(e)), Cmd.opens_with(x, e)), lo, n, Cmd.items(rest, 1n+n, q, x), h, ml_rise(rest, 1n+n, 1n+n, q, x, LNat.compactor.pc.le_refl(1n+n)), ml_rise(rest, 1n+n, lo, q, x, LNat.wn_le_step(lo, n, h)))

# ---- the menu ----

# the places of a children menu
def ml_kxs(m: Cmd.Menu) -> List<&2, Nat>:
  match m:
    case Cmd.Names{}:
      Nil{}
    case Cmd.Kids{q, xs}:
      xs
    case Cmd.Shut{}:
      Nil{}

# a walk state whose menu is the children q, xs: xs are q's items
def ml_xs(+s: Cmd.St, +t: List<&2, Cmd.Ent>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, -xs: List<&2, Nat>, +h: {Cmd.menu.at(s, t, p) == Cmd.Kids{q, xs} : Cmd.Menu}) -> {xs == Cmd.items(t, 0n, q, Cmd.lows(p)) : List<&2, Nat>}:
  +W = {Cmd.Walk{q, KB.kb_ent(s, KB.kb_dflt())} : Cmd.St}
  +hl = Equal.trans(Bool, Command.cmd_lists_kids(Cmd.menu.at(s, t, p), q), Command.cmd_lists_kids(Cmd.Kids{q, xs}, q), True{}, Equal.cong(Cmd.Menu, Bool, m => Command.cmd_lists_kids(m, q), Cmd.menu.at(s, t, p), Cmd.Kids{q, xs}, h), LNat.cb_path_refl(q))
  +hw = Equal.trans(Cmd.Menu, Cmd.menu.at(W, t, p), Cmd.menu.at(s, t, p), Cmd.Kids{q, xs}, Equal.cong(Cmd.St, Cmd.Menu, z => Cmd.menu.at(z, t, p), W, s, Equal.sym(Cmd.St, s, W, KB.kb_inv(s, t, p, q, hl))), h)
  Equal.sym(List<&2, Nat>, Cmd.items(t, 0n, q, Cmd.lows(p)), xs, Equal.cong(Cmd.Menu, List<&2, Nat>, m => ml_kxs(m), Cmd.menu.at(W, t, p), Cmd.Kids{q, xs}, hw))

def Command.command_menu_rows_listed(t, pre, p, q, xs, i, word, kids):
  +S = Cmd.walk(Cmd.words(pre), t, Cmd.Top{})
  +L = List.append(&2, Nat, pre, 32n <> p)
  +I = Cmd.items(t, 0n, q, Cmd.lows(p))
  +hk = Equal.trans(Cmd.Menu, Cmd.menu.at(S, t, p), Cmd.menu(t, L), Cmd.Kids{q, xs}, Equal.sym(Cmd.Menu, Cmd.menu(t, L), Cmd.menu.at(S, t, p), LANamed.nm_menu_pre(t, pre, p, word)), kids)
  %Equal.sym(List<&2, Nat>, xs, I, ml_xs(S, t, p, q, xs, hk)) : {(Command.cmd_nat_in(i, _), Command.cmd_rising(_, 0n)) == (Command.cmd_listed(t, i, q, Command.cmd_lower(p)), True{}) : Bool & Bool}
  %LA.cb_lows(p) : {(Command.cmd_nat_in(i, I), Command.cmd_rising(I, 0n)) == (Command.cmd_listed(t, i, q, _), True{}) : Bool & Bool}
  %ml_in(t, i, q, Cmd.lows(p)) : {(Command.cmd_nat_in(i, I), Command.cmd_rising(I, 0n)) == (_, True{}) : Bool & Bool}
  %ml_rise(t, 0n, 0n, q, Cmd.lows(p), {==}) : {(Command.cmd_nat_in(i, I), Command.cmd_rising(I, 0n)) == (Command.cmd_nat_in(i, I), _) : Bool & Bool}
  {==}
