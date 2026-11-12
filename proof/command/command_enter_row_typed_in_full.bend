# eukhe: the proof of LAW command_enter_row_typed_in_full
#
# PROOF of LAW command_enter_row_typed_in_full: the entry e that p names
# below q is a child of q (its path is q and its last name: ef_kid) and p
# names it (its last name is p in lowercase, or an alias is: ef_names). The
# line keyed below q answers Enter through the row of the selection at q
# (KB.kb_key), which is e (LA.kr_hit); Enter on a row the word names
# answers key.typed on e's default-or-no-child flag. With no row Enter
# answers key.enter on the line's resolution (KB.kb_enter), and the line
# walks into e (KB.kb_walk), so it finishes on that same flag; key.typed
# and key.enter agree on it (ef_fin_at).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../../laws/command/named.bend as CommandNamed
import ../base/bool.bend as LBool
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ./base.bend as LA
import ./base/named.bend as LANamed
import ./base/keys.bend as KB

# ---- the named entry is a child ----

def ef_init_go(zs: List<&2, List<&2, Nat>>, +z: List<&2, Nat>, -y: List<&2, Nat>) -> {Command.cmd_init.go(List.append(&2, List<&2, Nat>, zs, [y]), z) == z <> zs : List<&2, List<&2, Nat>>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+u, us}:
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, l => z <> l, Command.cmd_init.go(List.append(&2, List<&2, Nat>, us, [y]), u), u <> us, ef_init_go(us, u, y))

# q and one more name is a child of q
def ef_kid_snoc(q: List<&2, List<&2, Nat>>, -y: List<&2, Nat>) -> {Command.cmd_is_kid(q, List.append(&2, List<&2, Nat>, q, [y])) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{+z, +zs}:
      %Equal.sym(List<&2, List<&2, Nat>>, Command.cmd_init.go(List.append(&2, List<&2, Nat>, zs, [y]), z), z <> zs, ef_init_go(zs, z, y)) : {Command.cmd_path_eq(_, z <> zs) == True{} : Bool}
      LNat.cb_path_refl(z <> zs)

# the entry a word names below q is a child of q
def ef_kid(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +e: Cmd.Ent, hit: {CommandNamed.cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == True{} : Bool}:
  +y = Command.cmd_last(Command.cmd_ent_path(e))
  %Equal.sym(List<&2, List<&2, Nat>>, Command.cmd_ent_path(e), List.append(&2, List<&2, Nat>, q, [y]), LANamed.nm_path(t, q, p, e, hit)) : {Command.cmd_is_kid(q, _) == True{} : Bool}
  ef_kid_snoc(q, y)

# ---- the word names the entry ----

# an entry of path q ++ [x] has the last name x
def ef_names_path(c: Cmd.Ent, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hp: {Command.cmd_ent_path(c) == List.append(&2, List<&2, Nat>, q, [x]) : List<&2, List<&2, Nat>>}) -> {CommandNamed.cmd_names(x, c) == True{} : Bool}:
  match c:
    case Cmd.Ent{+pp, +a, r, f, g}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      %Equal.sym(List<&2, List<&2, Nat>>, pp, qx, hp) : {Bool.or(Command.cmd_eq(x, Command.cmd_last(_)), Command.cmd_in(x, a)) == True{} : Bool}
      %Equal.sym(List<&2, Nat>, Command.cmd_last(qx), x, LANamed.nm_last_app(q, x)) : {Bool.or(Command.cmd_eq(x, _), Command.cmd_in(x, a)) == True{} : Bool}
      %Equal.sym(Bool, Command.cmd_eq(x, x), True{}, LNat.cb_eq_refl(x)) : {Bool.or(_, Command.cmd_in(x, a)) == True{} : Bool}
      {==}

# m is none, or an entry x names
def ef_namesm(+x: List<&2, Nat>, m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{c}:
      CommandNamed.cmd_names(x, c)

# an entry the alias hits is named by it
def ef_hit_names(+q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, c: Cmd.Ent, h: {CommandNamed.cmd_alias_hit(q, x, c) == True{} : Bool}) -> {CommandNamed.cmd_names(x, c) == True{} : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      LBool.ppr.or_r(Command.cmd_eq(x, Command.cmd_last(p)), Command.cmd_in(x, a), LLogicBool.cb_and_r(Command.cmd_is_kid(q, p), Command.cmd_in(x, a), h))

def ef_namesm_at(b: Bool, +c: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hb: {CommandNamed.cmd_alias_hit(q, x, c) == b : Bool}, ih: {ef_namesm(x, m) == True{} : Bool}) -> {ef_namesm(x, Command.cmd_first.at(b, c, m)) == True{} : Bool}:
  match b:
    case True{}:
      ef_hit_names(q, x, c, hb)
    case False{}:
      ih

# the first child of q with the alias x is named by x
def ef_alias_namesm(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {ef_namesm(x, CommandNamed.cmd_alias_ent(t, q, x)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+c, rest}:
      ef_namesm_at(CommandNamed.cmd_alias_hit(q, x, c), c, CommandNamed.cmd_alias_ent(rest, q, x), q, x, {==}, ef_alias_namesm(rest, q, x))

def ef_names.at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +e: Cmd.Ent, hm: {Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])) == m : Maybe<&2, Cmd.Ent>}, h: {CommandNamed.cmd_named.at(m, t, q, x) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {CommandNamed.cmd_names(x, e) == True{} : Bool}:
  match m:
    case None{}:
      %h : {ef_namesm(x, _) == True{} : Bool}
      ef_alias_namesm(t, q, x)
    case Some{+c}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      +fit = Equal.trans(Bool, LA.cb_fits(Some{c}, qx), LA.cb_fits(Command.cmd_lookup(t, qx), qx), True{}, Equal.cong(Maybe<&2, Cmd.Ent>, Bool, z => LA.cb_fits(z, qx), Some{c}, Command.cmd_lookup(t, qx), Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, qx), Some{c}, hm)), LA.cb_lookup_fits(t, qx))
      %LANamed.nm_some_inj(c, e, h) : {CommandNamed.cmd_names(x, _) == True{} : Bool}
      ef_names_path(c, q, x, LLogicNat.cb_path_eq(Command.cmd_ent_path(c), qx, fit))

# the word p names the entry it walks into
def ef_names(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +e: Cmd.Ent, hit: {CommandNamed.cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.names(Cmd.lows(p), e) == True{} : Bool}:
  +x = Command.cmd_lower(p)
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  Equal.trans(Bool, Cmd.names(Cmd.lows(p), e), CommandNamed.cmd_names(x, e), True{}, KB.kb_names(e, p), ef_names.at(Command.cmd_lookup(t, qx), t, q, x, e, {==}, hit))

# ---- Enter ----

# Enter on a row typed in full and Enter with no row agree on the flag
def ef_fin_at(d: Bool, -P: List<&2, List<&2, Nat>>, +L: List<&2, Nat>) -> {Cmd.key.typed(d, Cmd.join(P), L) == Cmd.key.enter(Cmd.finish.at(d, P), L) : Cmd.Out}:
  match d:
    case True{}:
      {==}
    case False{}:
      {==}

def CommandNamed.command_enter_row_typed_in_full(t, pre, p, q, i, e, word, below, at, hit):
  +L = List.append(&2, Nat, pre, p)
  +w = word
  +b = below
  +h = hit
  +P = Cmd.Ent.path(e)
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.Row{i}, Cmd.Enter{}), Cmd.key.row(Cmd.row(Cmd.Row{i}, t, q), Cmd.Enter{}, t, L, p), KB.kb_key(t, pre, p, q, Cmd.Row{i}, Cmd.Enter{}, LA.cb_typed_spaceless(p, w), b)) : {_ == Cmd.key(t, L, Cmd.NoRow{}, Cmd.Enter{}) : Cmd.Out}
  %LA.kr_hit(t, q, i, e, at, ef_kid(t, q, p, e, h)) : {Cmd.key.row(_, Cmd.Enter{}, t, L, p) == Cmd.key(t, L, Cmd.NoRow{}, Cmd.Enter{}) : Cmd.Out}
  %Equal.sym(Cmd.Out, Cmd.key(t, L, Cmd.NoRow{}, Cmd.Enter{}), Cmd.key.enter(Cmd.resolve(t, L), L), KB.kb_enter(t, L)) : {Cmd.key.row(Some{e}, Cmd.Enter{}, t, L, p) == _ : Cmd.Out}
  %Equal.sym(Cmd.St, Cmd.walk(Cmd.words(L), t, Cmd.Top{}), Cmd.Walk{P, e}, KB.kb_walk(t, pre, p, q, e, w, b, h)) : {Cmd.key.row(Some{e}, Cmd.Enter{}, t, L, p) == Cmd.key.enter(Cmd.finish(_, t), L) : Cmd.Out}
  %Equal.sym(Bool, Cmd.names(Cmd.lows(p), e), True{}, ef_names(t, q, p, e, h)) : {Cmd.key.row_enter(_, Cmd.done(t, e), Cmd.kids.any(t, P), Cmd.Ent.arg(e), Cmd.join(P), L) == Cmd.key.enter(Cmd.finish(Cmd.Walk{P, e}, t), L) : Cmd.Out}
  ef_fin_at(Cmd.done(t, e), P, L)
