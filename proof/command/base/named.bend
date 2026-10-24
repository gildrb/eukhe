# eukhe: lemmas the proofs of laws/command/named.bend share
#
# The model's search is the spec's cmd_named (nm_search: by_alias is
# cmd_alias_ent); a step on a word that names the entry e lands on e's
# path with e (nm_step); a named entry's path is the walked path and its
# last name (nm_path); the words of a loose line then text that cuts
# (nm_words_line), and the walk over them (nm_walk_line). For keys: the
# words of pre, a space and a last word (nm_words_last), the menu and the
# key of such a line through the walk of pre's words (nm_menu_pre,
# nm_key_pre), the key at a walk state as cmd_key_at (nm_key_row), and a
# line that is not blank never walks back to the root (nm_off_pre).
# Lemma names: nm_.

import Base
import ../../../bend/command.bend as Cmd
import ../../../laws/command/paths.bend as Command
import ../../../laws/command/named.bend as CommandNamed
import ../../base/bool.bend as LBool
import ../../base/list.bend as LList
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/logic/nat.bend as LLogicNat
import ../../base/nat.bend as LNat
import ../base.bend as LA
import ./space.bend as LACommandSpace
import ../command_enter_without_row.bend as PCommandEnterWithoutRow
import ../command_tab_completes_row.bend as PCommandTabCompletesRow
import ../command_enter_on_row.bend as PCommandEnterOnRow

# ---- the search ----

# the model's by_alias is cmd_alias_ent
def nm_alias(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.by_alias(t, q, x) == CommandNamed.cmd_alias_ent(t, q, x) : Maybe<&2, Cmd.Ent>}:
  match t:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case Cmd.Ent{+p, +a, +r, +f, +g}:
          +E = {Cmd.Ent{p, a, r, f, g} : Cmd.Ent}
          %nm_alias(rest, q, x) : {Cmd.pick(Bool.and(Cmd.kid(q, p), Cmd.has(a, x)), E, Cmd.by_alias(rest, q, x)) == Command.cmd_first.at(Bool.and(Command.cmd_is_kid(q, p), Command.cmd_in(x, a)), E, _) : Maybe<&2, Cmd.Ent>}
          %LA.cb_alias_cond(q, p, a, x) : {Cmd.pick(Bool.and(Cmd.kid(q, p), Cmd.has(a, x)), E, Cmd.by_alias(rest, q, x)) == Command.cmd_first.at(_, E, Cmd.by_alias(rest, q, x)) : Maybe<&2, Cmd.Ent>}
          LA.cb_pick(Bool.and(Cmd.kid(q, p), Cmd.has(a, x)), E, Cmd.by_alias(rest, q, x))

def nm_named_at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {Cmd.search.alias(m, t, q, x) == CommandNamed.cmd_named.at(m, t, q, x) : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      nm_alias(t, q, x)
    case Some{e}:
      {==}

# the model's search of a typed word is cmd_named
def nm_search(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>) -> {Cmd.search(t, q, Cmd.lows(w)) == CommandNamed.cmd_named(t, q, w) : Maybe<&2, Cmd.Ent>}:
  %LA.cb_lows(w) : {Cmd.search(t, q, Cmd.lows(w)) == CommandNamed.cmd_named.at(Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [_])), t, q, _) : Maybe<&2, Cmd.Ent>}
  %LA.cb_by_path(t, List.append(&2, List<&2, Nat>, q, [Cmd.lows(w)])) : {Cmd.search(t, q, Cmd.lows(w)) == CommandNamed.cmd_named.at(_, t, q, Cmd.lows(w)) : Maybe<&2, Cmd.Ent>}
  nm_named_at(Cmd.by_path(t, List.append(&2, List<&2, Nat>, q, [Cmd.lows(w)])), t, q, Cmd.lows(w))

# ---- one step ----

def nm_step_of(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, hs: {Command.cmd_some(m) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.step(LA.cb_st.of(m, q), t, w) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({Cmd.step(LA.cb_st.of(None{}, q), t, w) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}, hs)
    case Some{+e0}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Walk{q, e0}, t, w), Cmd.step.word(Cmd.Walk{q, e0}, t, w), LA.cb_step_word(w, Cmd.Walk{q, e0}, t, hw)) : {_ == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, q, Cmd.lows(w)), CommandNamed.cmd_named(t, q, w), nm_search(t, q, w)) : {Cmd.step.walk(_, q, Cmd.Ent.free(e0), w) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, CommandNamed.cmd_named(t, q, w), Some{e}, hit) : {Cmd.step.walk(_, q, Cmd.Ent.free(e0), w) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      {==}

# from the state of q (the root, or q declared), a typed word that names
# the entry e lands on e's path with e
def nm_step(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, at: {LA.cb_at(t, q) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.step(LA.cb_st(t, q), t, w) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}:
  match q:
    case Nil{}:
      %Equal.sym(Cmd.St, Cmd.step(Cmd.Top{}, t, w), Cmd.step.word(Cmd.Top{}, t, w), LA.cb_step_word(w, Cmd.Top{}, t, hw)) : {_ == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Cmd.search(t, Nil{}, Cmd.lows(w)), CommandNamed.cmd_named(t, Nil{}, w), nm_search(t, Nil{}, w)) : {Cmd.step.top(_) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Maybe<&2, Cmd.Ent>, CommandNamed.cmd_named(t, Nil{}, w), Some{e}, hit) : {Cmd.step.top(_) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      {==}
    case Con{+y, +ys}:
      nm_step_of(Command.cmd_lookup(t, y <> ys), t, y <> ys, w, e, at, hw, hit)

# ---- the path of a named entry ----

def nm_get(m: Maybe<&2, Cmd.Ent>, d: Cmd.Ent) -> Cmd.Ent:
  match m:
    case None{}:
      d
    case Some{e}:
      e

def nm_some_inj(-a: Cmd.Ent, -b: Cmd.Ent, h: {Some{a} == Some{b} : Maybe<&2, Cmd.Ent>}) -> {a == b : Cmd.Ent}:
  Equal.cong(Maybe<&2, Cmd.Ent>, Cmd.Ent, m => nm_get(m, a), Some{a}, Some{b}, h)

# the last name of q ++ [x] is x
def nm_last_go(zs: List<&2, List<&2, Nat>>, -z: List<&2, Nat>, -x: List<&2, Nat>) -> {Command.cmd_last.go(List.append(&2, List<&2, Nat>, zs, [x]), z) == x : List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case Con{u, us}:
      nm_last_go(us, u, x)

def nm_last_app(q: List<&2, List<&2, Nat>>, -x: List<&2, Nat>) -> {Command.cmd_last(List.append(&2, List<&2, Nat>, q, [x])) == x : List<&2, Nat>}:
  match q:
    case Nil{}:
      {==}
    case Con{z, zs}:
      nm_last_go(zs, z, x)

# a path p equal to q ++ [x] is q ++ [its last name]
def nm_snoc(+p: List<&2, List<&2, Nat>>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, h: {p == List.append(&2, List<&2, Nat>, q, [x]) : List<&2, List<&2, Nat>>}) -> {p == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(p)]) : List<&2, List<&2, Nat>>}:
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  %Equal.sym(List<&2, List<&2, Nat>>, p, qx, h) : {_ == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(_)]) : List<&2, List<&2, Nat>>}
  %Equal.sym(List<&2, Nat>, Command.cmd_last(qx), x, nm_last_app(q, x)) : {qx == List.append(&2, List<&2, Nat>, q, [_]) : List<&2, List<&2, Nat>>}
  {==}

# z <> zs is its init and its last name
def nm_init_last(zs: List<&2, List<&2, Nat>>, +z: List<&2, Nat>) -> {z <> zs == List.append(&2, List<&2, Nat>, Command.cmd_init.go(zs, z), [Command.cmd_last.go(zs, z)]) : List<&2, List<&2, Nat>>}:
  match zs:
    case Nil{}:
      {==}
    case Con{+u, us}:
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, l => z <> l, u <> us, List.append(&2, List<&2, Nat>, Command.cmd_init.go(us, u), [Command.cmd_last.go(us, u)]), nm_init_last(us, u))

# a child p of q is q and its last name
def nm_kid_snoc(+q: List<&2, List<&2, Nat>>, p: List<&2, List<&2, Nat>>, h: {Command.cmd_is_kid(q, p) == True{} : Bool}) -> {p == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(p)]) : List<&2, List<&2, Nat>>}:
  match p:
    case Nil{}:
      LLogicLogic.cb_absurd({Nil{} == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(Nil{})]) : List<&2, List<&2, Nat>>}, h)
    case Con{+z, +zs}:
      +i = Command.cmd_init.go(zs, z)
      %LLogicNat.cb_path_eq(i, q, h) : {z <> zs == List.append(&2, List<&2, Nat>, _, [Command.cmd_last.go(zs, z)]) : List<&2, List<&2, Nat>>}
      nm_init_last(zs, z)

# None is not Some
def nm_none_some(-e: Cmd.Ent, h: {None{} == Some{e} : Maybe<&2, Cmd.Ent>}) -> {False{} == True{} : Bool}:
  Equal.cong(Maybe<&2, Cmd.Ent>, Bool, m => Command.cmd_some(m), None{}, Some{e}, h)

# an entry the alias hits is a child
def nm_hit_kid(+q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, c: Cmd.Ent, h: {CommandNamed.cmd_alias_hit(q, x, c) == True{} : Bool}) -> {Command.cmd_is_kid(q, Command.cmd_ent_path(c)) == True{} : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      LLogicBool.cb_and_l(Command.cmd_is_kid(q, p), Command.cmd_in(x, a), h)

# m is none, or an entry that is a child of q
def nm_kidm(q: List<&2, List<&2, Nat>>, m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      Command.cmd_is_kid(q, Command.cmd_ent_path(e))

def nm_kidm_at(b: Bool, +c: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hb: {CommandNamed.cmd_alias_hit(q, x, c) == b : Bool}, ih: {nm_kidm(q, m) == True{} : Bool}) -> {nm_kidm(q, Command.cmd_first.at(b, c, m)) == True{} : Bool}:
  match b:
    case True{}:
      nm_hit_kid(q, x, c, hb)
    case False{}:
      ih

# the first child with an alias is a child
def nm_alias_kidm(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {nm_kidm(q, CommandNamed.cmd_alias_ent(t, q, x)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+c, rest}:
      nm_kidm_at(CommandNamed.cmd_alias_hit(q, x, c), c, CommandNamed.cmd_alias_ent(rest, q, x), q, x, {==}, nm_alias_kidm(rest, q, x))

def nm_alias_kid(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, -e: Cmd.Ent, h: {CommandNamed.cmd_alias_ent(t, q, x) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_is_kid(q, Command.cmd_ent_path(e)) == True{} : Bool}:
  %h : {nm_kidm(q, _) == True{} : Bool}
  nm_alias_kidm(t, q, x)

def nm_path.at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +e: Cmd.Ent, hm: {Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])) == m : Maybe<&2, Cmd.Ent>}, h: {CommandNamed.cmd_named.at(m, t, q, x) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_ent_path(e) == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(Command.cmd_ent_path(e))]) : List<&2, List<&2, Nat>>}:
  match m:
    case None{}:
      nm_kid_snoc(q, Command.cmd_ent_path(e), nm_alias_kid(t, q, x, e, h))
    case Some{+c}:
      +qx = List.append(&2, List<&2, Nat>, q, [x])
      +fit = Equal.trans(Bool, LA.cb_fits(Some{c}, qx), LA.cb_fits(Command.cmd_lookup(t, qx), qx), True{}, Equal.cong(Maybe<&2, Cmd.Ent>, Bool, z => LA.cb_fits(z, qx), Some{c}, Command.cmd_lookup(t, qx), Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, qx), Some{c}, hm)), LA.cb_lookup_fits(t, qx))
      %nm_some_inj(c, e, h) : {Command.cmd_ent_path(_) == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(Command.cmd_ent_path(_))]) : List<&2, List<&2, Nat>>}
      nm_snoc(Command.cmd_ent_path(c), q, x, LLogicNat.cb_path_eq(Command.cmd_ent_path(c), qx, fit))

# a named entry's path is q and its last name
def nm_path(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +e: Cmd.Ent, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_ent_path(e) == List.append(&2, List<&2, Nat>, q, [Command.cmd_last(Command.cmd_ent_path(e))]) : List<&2, List<&2, Nat>>}:
  +x = Command.cmd_lower(w)
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  nm_path.at(Command.cmd_lookup(t, qx), t, q, x, e, {==}, hit)

# the canonical last name of a named entry is a name
def nm_canon_name(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +e: Cmd.Ent, -e1: Cmd.Ent, ok: {Command.cmd_wf(t) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}, first: {Command.cmd_lookup(t, Command.cmd_ent_path(e)) == Some{e1} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_name_ok(Command.cmd_last(Command.cmd_ent_path(e))) == True{} : Bool}:
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +d = Equal.cong(Maybe<&2, Cmd.Ent>, Bool, m => Command.cmd_some(m), Command.cmd_lookup(t, pe), Some{e1}, first)
  +np = LA.cb_decl_names(t, pe, ok, d)
  +nq = Equal.trans(Bool, Command.cmd_names_ok(qy), Command.cmd_names_ok(pe), True{}, Equal.cong(List<&2, List<&2, Nat>>, Bool, z => Command.cmd_names_ok(z), qy, pe, Equal.sym(List<&2, List<&2, Nat>>, pe, qy, nm_path(t, q, w, e, hit))), np)
  LA.cb_names_last(q, y, nq)

# ... and names the first entry of that path below q
def nm_canon_hit(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +e: Cmd.Ent, +e1: Cmd.Ent, +ok: {Command.cmd_wf(t) == True{} : Bool}, +hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}, +first: {Command.cmd_lookup(t, Command.cmd_ent_path(e)) == Some{e1} : Maybe<&2, Cmd.Ent>}) -> {CommandNamed.cmd_named(t, q, Command.cmd_last(Command.cmd_ent_path(e))) == Some{e1} : Maybe<&2, Cmd.Ent>}:
  +pe = Command.cmd_ent_path(e)
  +y = Command.cmd_last(pe)
  +qy = List.append(&2, List<&2, Nat>, q, [y])
  +lk = Equal.trans(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, qy), Command.cmd_lookup(t, pe), Some{e1}, Equal.cong(List<&2, List<&2, Nat>>, Maybe<&2, Cmd.Ent>, z => Command.cmd_lookup(t, z), qy, pe, Equal.sym(List<&2, List<&2, Nat>>, pe, qy, nm_path(t, q, w, e, hit))), first)
  %Equal.sym(List<&2, Nat>, Command.cmd_lower(y), y, LA.cb_name_low(y, nm_canon_name(t, q, w, e, e1, ok, hit, first))) : {CommandNamed.cmd_named.at(Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [_])), t, q, _) == Some{e1} : Maybe<&2, Cmd.Ent>}
  %Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, qy), Some{e1}, lk) : {CommandNamed.cmd_named.at(_, t, q, y) == Some{e1} : Maybe<&2, Cmd.Ent>}
  {==}

# ---- the walk of a line ----

# the words after the first of a text that cuts
def nm_tail(s: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match s:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      Cmd.words(r)

def nm_words_at(b: Bool, -c: Nat, -ws: List<&2, List<&2, Nat>>, h: {b == True{} : Bool}) -> {Cmd.words.at(b, c, ws) == Nil{} <> ws : List<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.cb_absurd({Cmd.words.at(False{}, c, ws) == Nil{} <> ws : List<&2, List<&2, Nat>>}, h)

# a text that cuts: an empty word, then its tail
def nm_cuts(s: List<&2, Nat>, h: {CommandNamed.cmd_cuts(s) == True{} : Bool}) -> {Cmd.words(s) == Nil{} <> nm_tail(s) : List<&2, List<&2, Nat>>}:
  match s:
    case Nil{}:
      {==}
    case Con{+c, r}:
      nm_words_at(Nat.is_eq(c, 32n), c, Cmd.words(r), h)

# the names of a walked q, then a typed w, are spaceless
def nm_spaceless(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}) -> {Command.cmd_all_spaceless(List.append(&2, List<&2, Nat>, q, [w])) == True{} : Bool}:
  LA.cb_all_spaceless_app(q, [w], LA.cb_names_spaceless(q, LA.cb_walks_names(t, q, ok, on)), LBool.cb_and_intro(Command.cmd_spaceless(w), True{}, LA.cb_typed_spaceless(w, hw), {==}))

# the loose words of q and w, then words y: the walk lands after w on
# e's path with e, then takes y
def nm_walk_words(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, +gs: List<&2, Nat>, +y: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.walk(List.append(&2, List<&2, Nat>, LACommandSpace.sp_ls(List.append(&2, List<&2, Nat>, q, [w]), gs), y), t, Cmd.Top{}) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}:
  +A = LACommandSpace.sp_lsi(q, gs)
  +Aw = List.append(&2, List<&2, Nat>, A, [w])
  %Equal.sym(List<&2, List<&2, Nat>>, LACommandSpace.sp_ls(List.append(&2, List<&2, Nat>, q, [w]), gs), Aw, LACommandSpace.sp_ls_last(q, w, gs)) : {Cmd.walk(List.append(&2, List<&2, Nat>, _, y), t, Cmd.Top{}) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, Aw, y), t, Cmd.Top{}), Cmd.walk(y, t, Cmd.walk(Aw, t, Cmd.Top{})), LA.cb_walk_app(Aw, y, t, Cmd.Top{})) : {_ == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(Aw, t, Cmd.Top{}), Cmd.walk([w], t, Cmd.walk(A, t, Cmd.Top{})), LA.cb_walk_app(A, [w], t, Cmd.Top{})) : {Cmd.walk(y, t, _) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(A, t, Cmd.Top{}), Cmd.walk(q, t, Cmd.Top{}), LACommandSpace.sp_walk_loose(q, gs, t, ok, on)) : {Cmd.walk(y, t, Cmd.walk([w], t, _)) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(q, t, Cmd.Top{}), LA.cb_st(t, q), LA.cb_walk_root(q, t, ok, on)) : {Cmd.walk(y, t, Cmd.walk([w], t, _)) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.step(LA.cb_st(t, q), t, w), Cmd.Walk{Cmd.Ent.path(e), e}, nm_step(t, q, w, e, LA.cb_walks_at(t, q, on), hw, hit)) : {Cmd.walk(y, t, _) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  {==}

# the walk of the loose line of q and w, then a text that cuts
def nm_walk_line(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, +gs: List<&2, Nat>, +s: List<&2, Nat>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, +hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}, gap: {CommandNamed.cmd_cuts(s) == True{} : Bool}) -> {Cmd.walk(Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), s)), t, Cmd.Top{}) == Cmd.walk(nm_tail(s), t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}:
  +y = nm_tail(s)
  +qw = List.append(&2, List<&2, Nat>, q, [w])
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_loose(qw, gs), s)), List.append(&2, List<&2, Nat>, LACommandSpace.sp_ls(qw, gs), y), LACommandSpace.sp_words_loose_last(q, w, gs, s, y, nm_spaceless(t, q, w, ok, on, hw), nm_cuts(s, gap))) : {Cmd.walk(_, t, Cmd.Top{}) == Cmd.walk(y, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.St}
  nm_walk_words(t, q, w, e, gs, y, ok, on, hw, hit)

# ---- the cut of a line ----

def nm_cut_go(as: List<&2, List<&2, Nat>>, ws: List<&2, List<&2, Nat>>, +a0: List<&2, Nat>, -d: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, h: {Cmd.cut(ws) == (d, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}, ne: {LACommandSpace.sp_ne(ws) == True{} : Bool}) -> {Cmd.cut.go(List.append(&2, List<&2, Nat>, as, ws), a0) == (a0 <> List.append(&2, List<&2, Nat>, as, d), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match as:
    case Nil{}:
      match ws:
        case Nil{}:
          LLogicLogic.cb_absurd({Cmd.cut.go(Nil{}, a0) == (a0 <> d, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}, ne)
        case Con{v, rest}:
          %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(rest, v), (d, p), h) : {Cmd.cut.cons(a0, _) == (a0 <> d, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}
          {==}
    case Con{+u, us}:
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut.go(List.append(&2, List<&2, Nat>, us, ws), u), (u <> List.append(&2, List<&2, Nat>, us, d), p), nm_cut_go(us, ws, u, d, p, h, ne)) : {Cmd.cut.cons(a0, _) == (a0 <> u <> List.append(&2, List<&2, Nat>, us, d), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}
      {==}

# the cut of a ++ ws (ws not none): a, then the cut of ws
def nm_cut_app(a: List<&2, List<&2, Nat>>, ws: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, h: {Cmd.cut(ws) == (d, p) : List<&2, List<&2, Nat>> & List<&2, Nat>}, ne: {LACommandSpace.sp_ne(ws) == True{} : Bool}) -> {Cmd.cut(List.append(&2, List<&2, Nat>, a, ws)) == (List.append(&2, List<&2, Nat>, a, d), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  match a:
    case Nil{}:
      h
    case Con{+a0, as}:
      nm_cut_go(as, ws, a0, d, p, h, ne)

# ---- menus ----

# the menu at the walk from S over the cut words d, before the last p
def nm_menu_after(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, S: Cmd.St) -> Cmd.Menu:
  match c:
    case (d, p):
      Cmd.menu.at(Cmd.walk(d, t, S), t, p)

def nm_menu_go(B: List<&2, List<&2, Nat>>, -w: List<&2, Nat>, -c: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, +t: List<&2, Cmd.Ent>) -> {Cmd.menu.go(List.append(&2, List<&2, Nat>, B, w <> c), p, t) == Cmd.menu.at(Cmd.walk(List.append(&2, List<&2, Nat>, B, w <> c), t, Cmd.Top{}), t, p) : Cmd.Menu}:
  match B:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

def nm_menu_at(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, +gs: List<&2, Nat>, +s: List<&2, Nat>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, +hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}, hc: {Cmd.cut(Cmd.words(s)) == c : List<&2, List<&2, Nat>> & List<&2, Nat>}) -> {Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == nm_menu_after(c, t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.Menu}:
  match c:
    case (+d, +p):
      +W = Cmd.words(s)
      +qw = List.append(&2, List<&2, Nat>, q, [w])
      +A = LACommandSpace.sp_lsi(q, gs)
      +Aw = List.append(&2, List<&2, Nat>, A, [w])
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, Command.cmd_loose(qw, gs), 32n <> s)), List.append(&2, List<&2, Nat>, LACommandSpace.sp_ls(qw, gs), W), LACommandSpace.sp_words_loose_last(q, w, gs, 32n <> s, W, nm_spaceless(t, q, w, ok, on, hw), {==})) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>>, LACommandSpace.sp_ls(qw, gs), Aw, LACommandSpace.sp_ls_last(q, w, gs)) : {Cmd.menu.cut(Cmd.cut(List.append(&2, List<&2, Nat>, _, W)), t) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, Aw, W)), (List.append(&2, List<&2, Nat>, Aw, d), p), nm_cut_app(Aw, W, d, p, hc, LACommandSpace.sp_words_ne(s))) : {Cmd.menu.cut(_, t) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, Aw, d), List.append(&2, List<&2, Nat>, A, w <> d), LList.cb_app_assoc(List<&2, Nat>, A, [w], d)) : {Cmd.menu.go(_, p, t) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(Cmd.Menu, Cmd.menu.go(List.append(&2, List<&2, Nat>, A, w <> d), p, t), Cmd.menu.at(Cmd.walk(List.append(&2, List<&2, Nat>, A, w <> d), t, Cmd.Top{}), t, p), nm_menu_go(A, w, d, p, t)) : {_ == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, A, w <> d), t, Cmd.Top{}), Cmd.walk(w <> d, t, Cmd.walk(A, t, Cmd.Top{})), LA.cb_walk_app(A, w <> d, t, Cmd.Top{})) : {Cmd.menu.at(_, t, p) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.walk(A, t, Cmd.Top{}), Cmd.walk(q, t, Cmd.Top{}), LACommandSpace.sp_walk_loose(q, gs, t, ok, on)) : {Cmd.menu.at(Cmd.walk(w <> d, t, _), t, p) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.walk(q, t, Cmd.Top{}), LA.cb_st(t, q), LA.cb_walk_root(q, t, ok, on)) : {Cmd.menu.at(Cmd.walk(w <> d, t, _), t, p) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      %Equal.sym(Cmd.St, Cmd.step(LA.cb_st(t, q), t, w), Cmd.Walk{Cmd.Ent.path(e), e}, nm_step(t, q, w, e, LA.cb_walks_at(t, q, on), hw, hit)) : {Cmd.menu.at(Cmd.walk(d, t, _), t, p) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{Cmd.Ent.path(e), e}), t, p) : Cmd.Menu}
      {==}

# the menu of the loose line of q and w, a space, then any text
def nm_menu_line(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, +gs: List<&2, Nat>, +s: List<&2, Nat>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, +hw: {Command.cmd_typed(w) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.menu(t, List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [w]), gs), 32n <> s)) == nm_menu_after(Cmd.cut(Cmd.words(s)), t, Cmd.Walk{Cmd.Ent.path(e), e}) : Cmd.Menu}:
  nm_menu_at(Cmd.cut(Cmd.words(s)), t, q, w, e, gs, s, ok, on, hw, hit, {==})

# ---- keys ----

def nm_ww_at(b: Bool, +c: Nat, -r: List<&2, Nat>, hb: {Bool.and(Bool.not(b), Command.cmd_spaceless(r)) == True{} : Bool}, ih: {Cmd.words(r) == [r] : List<&2, List<&2, Nat>>}) -> {Cmd.words.at(b, c, Cmd.words(r)) == [c <> r] : List<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      LLogicLogic.cb_absurd({Cmd.words.at(True{}, c, Cmd.words(r)) == [c <> r] : List<&2, List<&2, Nat>>}, hb)
    case False{}:
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(r), [r], ih) : {Cmd.put_word(c, _) == [c <> r] : List<&2, List<&2, Nat>>}
      {==}

# a spaceless word is one word
def nm_words_word(p: List<&2, Nat>, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(p) == [p] : List<&2, List<&2, Nat>>}:
  match p:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      +h2 = h
      nm_ww_at(Nat.is_eq(c, 32n), c, r, h2, nm_words_word(r, LLogicBool.cb_and_r(Bool.not(Nat.is_eq(c, 32n)), Command.cmd_spaceless(r), h2)))

def nm_at_app(b: Bool, -c: Nat, ws: List<&2, List<&2, Nat>>, -y: List<&2, List<&2, Nat>>, ne: {LACommandSpace.sp_ne(ws) == True{} : Bool}) -> {Cmd.words.at(b, c, List.append(&2, List<&2, Nat>, ws, y)) == List.append(&2, List<&2, Nat>, Cmd.words.at(b, c, ws), y) : List<&2, List<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match ws:
        case Nil{}:
          LLogicLogic.cb_absurd({Cmd.words.at(False{}, c, List.append(&2, List<&2, Nat>, Nil{}, y)) == List.append(&2, List<&2, Nat>, Cmd.words.at(False{}, c, Nil{}), y) : List<&2, List<&2, Nat>>}, ne)
        case Con{w, rest}:
          {==}

# the words of pre, then a text s whose words are an empty word and y
def nm_words_app(pre: List<&2, Nat>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, pre, s)) == List.append(&2, List<&2, Nat>, Cmd.words(pre), y) : List<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      hs
    case Con{+c, +r}:
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, r, s)), List.append(&2, List<&2, Nat>, Cmd.words(r), y), nm_words_app(r, s, y, hs)) : {Cmd.words.at(Nat.is_eq(c, 32n), c, _) == List.append(&2, List<&2, Nat>, Cmd.words.at(Nat.is_eq(c, 32n), c, Cmd.words(r)), y) : List<&2, List<&2, Nat>>}
      nm_at_app(Nat.is_eq(c, 32n), c, Cmd.words(r), y, LACommandSpace.sp_words_ne(r))

# the words of pre, a space and a spaceless p: pre's words, then p
def nm_words_last(pre: List<&2, Nat>, +p: List<&2, Nat>, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(List.append(&2, Nat, pre, 32n <> p)) == List.append(&2, List<&2, Nat>, Cmd.words(pre), [p]) : List<&2, List<&2, Nat>>}:
  nm_words_app(pre, 32n <> p, [p], Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => Nil{} <> z, Cmd.words(p), [p], nm_words_word(p, h)))

def nm_menu_go1(d: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, +t: List<&2, Cmd.Ent>, ne: {LACommandSpace.sp_ne(d) == True{} : Bool}) -> {Cmd.menu.go(d, p, t) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Top{}), t, p) : Cmd.Menu}:
  match d:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.menu.go(Nil{}, p, t) == Cmd.menu.at(Cmd.walk(Nil{}, t, Cmd.Top{}), t, p) : Cmd.Menu}, ne)
    case Con{w, r}:
      {==}

# the menu of pre, a space and p: the menu at the walk of pre's words
def nm_menu_pre(+t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.menu(t, List.append(&2, Nat, pre, 32n <> p)) == Cmd.menu.at(Cmd.walk(Cmd.words(pre), t, Cmd.Top{}), t, p) : Cmd.Menu}:
  +ws = Cmd.words(pre)
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, pre, 32n <> p)), List.append(&2, List<&2, Nat>, ws, [p]), nm_words_last(pre, p, h)) : {Cmd.menu.cut(Cmd.cut(_), t) == Cmd.menu.at(Cmd.walk(ws, t, Cmd.Top{}), t, p) : Cmd.Menu}
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, ws, [p])), (ws, p), LA.cb_cut(ws, p)) : {Cmd.menu.cut(_, t) == Cmd.menu.at(Cmd.walk(ws, t, Cmd.Top{}), t, p) : Cmd.Menu}
  nm_menu_go1(ws, p, t, LACommandSpace.sp_words_ne(pre))

# the key of pre, a space and p: the key at the walk of pre's words
def nm_key_pre(+t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, h: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.key(t, List.append(&2, Nat, pre, 32n <> p), sel, k) == Cmd.key.at(Cmd.walk(Cmd.words(pre), t, Cmd.Top{}), t, List.append(&2, Nat, pre, 32n <> p), p, sel, k) : Cmd.Out}:
  +ws = Cmd.words(pre)
  +L = List.append(&2, Nat, pre, 32n <> p)
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(L), List.append(&2, List<&2, Nat>, ws, [p]), nm_words_last(pre, p, h)) : {Cmd.key.cut(Cmd.cut(_), t, L, sel, k) == Cmd.key.at(Cmd.walk(ws, t, Cmd.Top{}), t, L, p, sel, k) : Cmd.Out}
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, ws, [p])), (ws, p), LA.cb_cut(ws, p)) : {Cmd.key.cut(_, t, L, sel, k) == Cmd.key.at(Cmd.walk(ws, t, Cmd.Top{}), t, L, p, sel, k) : Cmd.Out}
  {==}

# no row: the model's key.bare is cmd_key_bare
def nm_bare(k: Cmd.Press, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.key.bare(k, t, line) == CommandNamed.cmd_key_bare(t, line, k) : Cmd.Out}:
  match k:
    case Cmd.Tab{}:
      {==}
    case Cmd.Enter{}:
      PCommandEnterWithoutRow.kewr_enter(Cmd.resolve(t, line), line)

def nm_kid(b: Bool, c: Cmd.Ent, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>, k: Cmd.Press) -> {Cmd.key.row(Cmd.row.kid(b, c), k, t, line, p) == CommandNamed.cmd_key_kid(b, c, t, line, p, k) : Cmd.Out}:
  match b:
    case True{}:
      match k:
        case Cmd.Tab{}:
          PCommandTabCompletesRow.tcr_pick(c, t, line, p)
        case Cmd.Enter{}:
          PCommandEnterOnRow.eor_pick(c, t, line, p)
    case False{}:
      nm_bare(k, t, line)

def nm_row_of(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +line: List<&2, Nat>, +p: List<&2, Nat>, k: Cmd.Press) -> {Cmd.key.row(Cmd.row.of(m, q), k, t, line, p) == CommandNamed.cmd_key_row(m, t, q, line, p, k) : Cmd.Out}:
  match m:
    case None{}:
      nm_bare(k, t, line)
    case Some{c}:
      match c:
        case Cmd.Ent{+pp, +a, +r, +f, +g}:
          +E = {Cmd.Ent{pp, a, r, f, g} : Cmd.Ent}
          %LA.cb_kid(q, pp) : {Cmd.key.row(Cmd.row.kid(Cmd.kid(q, pp), E), k, t, line, p) == CommandNamed.cmd_key_kid(_, E, t, line, p, k) : Cmd.Out}
          nm_kid(Cmd.kid(q, pp), E, t, line, p, k)

# the row of the selection at q is cmd_key_at
def nm_key_row(sel: Cmd.Sel, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +line: List<&2, Nat>, +p: List<&2, Nat>, k: Cmd.Press) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}:
  match sel:
    case Cmd.NoRow{}:
      nm_bare(k, t, line)
    case Cmd.Row{+i}:
      nm_row_of(List.get(&2, Cmd.Ent, t, i), t, q, line, p, k)

# the path of a children menu, and which menus list children
def nm_kq(m: Cmd.Menu) -> List<&2, List<&2, Nat>>:
  match m:
    case Cmd.Names{}:
      Nil{}
    case Cmd.Kids{q, xs}:
      q
    case Cmd.Shut{}:
      Nil{}

def nm_is_kids(m: Cmd.Menu) -> Bool:
  match m:
    case Cmd.Names{}:
      False{}
    case Cmd.Kids{q, xs}:
      True{}
    case Cmd.Shut{}:
      False{}

# a shut menu is no children menu
def nm_shut_kids(-q: List<&2, List<&2, Nat>>, -xs: List<&2, Nat>, h: {Cmd.Shut{} == Cmd.Kids{q, xs} : Cmd.Menu}) -> {False{} == True{} : Bool}:
  Equal.cong(Cmd.Menu, Bool, m => nm_is_kids(m), Cmd.Shut{}, Cmd.Kids{q, xs}, h)

# a walk state whose menu lists the children of q: the key acts on q
def nm_key_kids(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +q: List<&2, List<&2, Nat>>, -xs: List<&2, Nat>, h: {Cmd.menu.at(s, t, p) == Cmd.Kids{q, xs} : Cmd.Menu}) -> {Cmd.key.at(s, t, line, p, sel, k) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Top{}, t, line, p, sel, k) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}, nm_shut_kids(q, xs, h))
    case Cmd.Walk{+q0, e}:
      +eq = Equal.cong(Cmd.Menu, List<&2, List<&2, Nat>>, m => nm_kq(m), Cmd.Kids{q0, Cmd.items(t, 0n, q0, Cmd.lows(p))}, Cmd.Kids{q, xs}, h)
      %Equal.sym(List<&2, List<&2, Nat>>, q0, q, eq) : {Cmd.key.row(Cmd.row(sel, t, _), k, t, line, p) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}
      nm_key_row(sel, t, q, line, p, k)
    case Cmd.Rest{q0, ws}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Rest{q0, ws}, t, line, p, sel, k) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}, nm_shut_kids(q, xs, h))
    case Cmd.Lost{q0, x}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Lost{q0, x}, t, line, p, sel, k) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}, nm_shut_kids(q, xs, h))
    case Cmd.Stray{}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Stray{}, t, line, p, sel, k) == CommandNamed.cmd_key_at(t, q, line, p, sel, k) : Cmd.Out}, nm_shut_kids(q, xs, h))

# the root state
def nm_top(s: Cmd.St) -> Bool:
  match s:
    case Cmd.Top{}:
      True{}
    case Cmd.Walk{q, e}:
      False{}
    case Cmd.Rest{q, ws}:
      False{}
    case Cmd.Lost{q, x}:
      False{}
    case Cmd.Stray{}:
      False{}

# a walk state off the root whose menu is shut: a row acts as no row
def nm_key_shut(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>, +i: Nat, k: Cmd.Press, h: {Cmd.menu.at(s, t, p) == Cmd.Shut{} : Cmd.Menu}, nt: {nm_top(s) == False{} : Bool}) -> {Cmd.key.at(s, t, line, p, Cmd.Row{i}, k) == Cmd.key.at(s, t, line, p, Cmd.NoRow{}, k) : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Top{}, t, line, p, Cmd.Row{i}, k) == Cmd.key.at(Cmd.Top{}, t, line, p, Cmd.NoRow{}, k) : Cmd.Out}, Equal.sym(Bool, True{}, False{}, nt))
    case Cmd.Walk{+q0, e}:
      LLogicLogic.cb_absurd({Cmd.key.at(Cmd.Walk{q0, e}, t, line, p, Cmd.Row{i}, k) == Cmd.key.at(Cmd.Walk{q0, e}, t, line, p, Cmd.NoRow{}, k) : Cmd.Out}, Equal.sym(Bool, True{}, False{}, Equal.cong(Cmd.Menu, Bool, m => nm_is_kids(m), Cmd.Kids{q0, Cmd.items(t, 0n, q0, Cmd.lows(p))}, Cmd.Shut{}, h)))
    case Cmd.Rest{q0, ws}:
      {==}
    case Cmd.Lost{q0, x}:
      {==}
    case Cmd.Stray{}:
      {==}

# a found entry's step lands off the root
def nm_top_top(m: Maybe<&2, Cmd.Ent>) -> {nm_top(Cmd.step.top(m)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

def nm_walk_off(m: Maybe<&2, Cmd.Ent>, -q: List<&2, List<&2, Nat>>, f: Bool, -w: List<&2, Nat>) -> {nm_top(Cmd.step.walk(m, q, f, w)) == False{} : Bool}:
  match m:
    case None{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}
    case Some{e}:
      {==}

# a step off the root stays off it
def nm_step_off(s: Cmd.St, +t: List<&2, Cmd.Ent>, w: List<&2, Nat>, h: {nm_top(s) == False{} : Bool}) -> {nm_top(Cmd.step(s, t, w)) == False{} : Bool}:
  match s:
    case Cmd.Top{}:
      LLogicLogic.cb_absurd({nm_top(Cmd.step(Cmd.Top{}, t, w)) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case Cmd.Walk{+q, e}:
      match w:
        case Nil{}:
          {==}
        case Con{+c, +r}:
          nm_walk_off(Cmd.search(t, q, Cmd.lows(c <> r)), q, Cmd.Ent.free(e), c <> r)
    case Cmd.Rest{q, ws}:
      match w:
        case Nil{}:
          {==}
        case Con{c, r}:
          {==}
    case Cmd.Lost{q, x}:
      match w:
        case Nil{}:
          {==}
        case Con{c, r}:
          {==}
    case Cmd.Stray{}:
      match w:
        case Nil{}:
          {==}
        case Con{c, r}:
          {==}

# a walk off the root stays off it
def nm_stays(ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +s: Cmd.St, h: {nm_top(s) == False{} : Bool}) -> {nm_top(Cmd.walk(ws, t, s)) == False{} : Bool}:
  match ws:
    case Nil{}:
      h
    case Con{+w, rest}:
      nm_stays(rest, t, Cmd.step(s, t, w), nm_step_off(s, t, w, h))

def nm_off_put(+c: Nat, ws: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, ne: {LACommandSpace.sp_ne(ws) == True{} : Bool}) -> {nm_top(Cmd.walk(Cmd.put_word(c, ws), t, Cmd.Top{})) == False{} : Bool}:
  match ws:
    case Nil{}:
      LLogicLogic.cb_absurd({nm_top(Cmd.walk(Cmd.put_word(c, Nil{}), t, Cmd.Top{})) == False{} : Bool}, ne)
    case Con{+w, rest}:
      nm_stays(rest, t, Cmd.step.top(Cmd.search(t, Nil{}, Cmd.lows(c <> w))), nm_top_top(Cmd.search(t, Nil{}, Cmd.lows(c <> w))))

def nm_off_at(b: Bool, +c: Nat, +r: List<&2, Nat>, +t: List<&2, Cmd.Ent>, hb: {Bool.and(b, CommandNamed.cmd_blank(r)) == False{} : Bool}, ih: {CommandNamed.cmd_blank(r) == False{} : Bool} -> {nm_top(Cmd.walk(Cmd.words(r), t, Cmd.Top{})) == False{} : Bool}) -> {nm_top(Cmd.walk(Cmd.words.at(b, c, Cmd.words(r)), t, Cmd.Top{})) == False{} : Bool}:
  match b:
    case True{}:
      ih(hb)
    case False{}:
      nm_off_put(c, Cmd.words(r), t, LACommandSpace.sp_words_ne(r))

# a line that is not blank walks off the root
def nm_off_pre(+t: List<&2, Cmd.Ent>, pre: List<&2, Nat>, h: {CommandNamed.cmd_blank(pre) == False{} : Bool}) -> {nm_top(Cmd.walk(Cmd.words(pre), t, Cmd.Top{})) == False{} : Bool}:
  match pre:
    case Nil{}:
      LLogicLogic.cb_absurd({nm_top(Cmd.walk(Cmd.words(Nil{}), t, Cmd.Top{})) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, h))
    case Con{+c, +r}:
      nm_off_at(Nat.is_eq(c, 32n), c, r, t, h, x => nm_off_pre(t, r, x))

# ---- tables that declare a path twice ----

def nm_decl_at(b: Bool, -c: Cmd.Ent, -m: Maybe<&2, Cmd.Ent>, h: {Command.cmd_some(m) == True{} : Bool}) -> {Command.cmd_some(Command.cmd_first.at(b, c, m)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      h

# a path declared in rest is declared below one more entry
def nm_decl_cons(+c: Cmd.Ent, rest: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, h: {Command.cmd_declared(rest, p) == True{} : Bool}) -> {Command.cmd_declared(c <> rest, p) == True{} : Bool}:
  nm_decl_at(Command.cmd_path_eq(Command.cmd_ent_path(c), p), c, Command.cmd_lookup(rest, p), h)

# an entry's own path is declared
def nm_decl_self(+c: Cmd.Ent, rest: List<&2, Cmd.Ent>) -> {Command.cmd_declared(c <> rest, Command.cmd_ent_path(c)) == True{} : Bool}:
  +pc = Command.cmd_ent_path(c)
  %Equal.sym(Bool, Command.cmd_path_eq(pc, pc), True{}, LNat.cb_path_refl(pc)) : {Command.cmd_some(Command.cmd_first.at(_, c, Command.cmd_lookup(rest, pc))) == True{} : Bool}
  {==}

# m is none, or an entry whose path t declares
def nm_decm(t: List<&2, Cmd.Ent>, m: Maybe<&2, Cmd.Ent>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{e}:
      Command.cmd_declared(t, Command.cmd_ent_path(e))

def nm_decm_cons(+c: Cmd.Ent, rest: List<&2, Cmd.Ent>, m: Maybe<&2, Cmd.Ent>, h: {nm_decm(rest, m) == True{} : Bool}) -> {nm_decm(c <> rest, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      nm_decl_cons(c, rest, Command.cmd_ent_path(e), h)

def nm_decm_at(b: Bool, +c: Cmd.Ent, rest: List<&2, Cmd.Ent>, -m: Maybe<&2, Cmd.Ent>, ih: {nm_decm(c <> rest, m) == True{} : Bool}) -> {nm_decm(c <> rest, Command.cmd_first.at(b, c, m)) == True{} : Bool}:
  match b:
    case True{}:
      nm_decl_self(c, rest)
    case False{}:
      ih

# the first child with an alias is an entry of the table
def nm_alias_decm(t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>) -> {nm_decm(t, CommandNamed.cmd_alias_ent(t, q, x)) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+c, +rest}:
      nm_decm_at(CommandNamed.cmd_alias_hit(q, x, c), c, rest, CommandNamed.cmd_alias_ent(rest, q, x), nm_decm_cons(c, rest, CommandNamed.cmd_alias_ent(rest, q, x), nm_alias_decm(rest, q, x)))

# the entry lookup finds for p has the path p, so its path is declared
def nm_lookup_decm(+t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, m: Maybe<&2, Cmd.Ent>, +hm: {Command.cmd_lookup(t, p) == m : Maybe<&2, Cmd.Ent>}) -> {nm_decm(t, m) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      +fit = Equal.trans(Bool, LA.cb_fits(Some{c}, p), LA.cb_fits(Command.cmd_lookup(t, p), p), True{}, Equal.cong(Maybe<&2, Cmd.Ent>, Bool, z => LA.cb_fits(z, p), Some{c}, Command.cmd_lookup(t, p), Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, p), Some{c}, hm)), LA.cb_lookup_fits(t, p))
      %Equal.sym(List<&2, List<&2, Nat>>, Command.cmd_ent_path(c), p, LLogicNat.cb_path_eq(Command.cmd_ent_path(c), p, fit)) : {Command.cmd_some(Command.cmd_lookup(t, _)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, p), Some{c}, hm) : {Command.cmd_some(_) == True{} : Bool}
      {==}

def nm_named_decm.at(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, hm: {Command.cmd_lookup(t, List.append(&2, List<&2, Nat>, q, [x])) == m : Maybe<&2, Cmd.Ent>}) -> {nm_decm(t, CommandNamed.cmd_named.at(m, t, q, x)) == True{} : Bool}:
  match m:
    case None{}:
      nm_alias_decm(t, q, x)
    case Some{+c}:
      nm_lookup_decm(t, List.append(&2, List<&2, Nat>, q, [x]), Some{c}, hm)

# a named entry's path is declared
def nm_named_decl(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, -e: Cmd.Ent, hit: {CommandNamed.cmd_named(t, q, w) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_declared(t, Command.cmd_ent_path(e)) == True{} : Bool}:
  +x = Command.cmd_lower(w)
  +qx = List.append(&2, List<&2, Nat>, q, [x])
  %hit : {nm_decm(t, _) == True{} : Bool}
  nm_named_decm.at(Command.cmd_lookup(t, qx), t, q, x, {==})

# the first entry of a named entry's path has that path
def nm_first_path(+t: List<&2, Cmd.Ent>, +e: Cmd.Ent, +e1: Cmd.Ent, first: {Command.cmd_lookup(t, Command.cmd_ent_path(e)) == Some{e1} : Maybe<&2, Cmd.Ent>}) -> {Cmd.Ent.path(e1) == Cmd.Ent.path(e) : List<&2, List<&2, Nat>>}:
  +pe = Command.cmd_ent_path(e)
  +fit = Equal.trans(Bool, LA.cb_fits(Some{e1}, pe), LA.cb_fits(Command.cmd_lookup(t, pe), pe), True{}, Equal.cong(Maybe<&2, Cmd.Ent>, Bool, z => LA.cb_fits(z, pe), Some{e1}, Command.cmd_lookup(t, pe), Equal.sym(Maybe<&2, Cmd.Ent>, Command.cmd_lookup(t, pe), Some{e1}, first)), LA.cb_lookup_fits(t, pe))
  Equal.trans(List<&2, List<&2, Nat>>, Cmd.Ent.path(e1), pe, Cmd.Ent.path(e), LA.cb_found(e1, pe, fit), Equal.sym(List<&2, List<&2, Nat>>, Cmd.Ent.path(e), pe, LA.cb_ent_path(e)))

# a declared path has a first entry
def nm_first.of(m: Maybe<&2, Cmd.Ent>, h: {Command.cmd_some(m) == True{} : Bool}) -> Cmd.Ent:
  match m:
    case None{}:
      LLogicLogic.cb_absurd(Cmd.Ent, h)
    case Some{e}:
      e

def nm_first.eq(m: Maybe<&2, Cmd.Ent>, h: {Command.cmd_some(m) == True{} : Bool}) -> {m == Some{nm_first.of(m, h)} : Maybe<&2, Cmd.Ent>}:
  match m:
    case None{}:
      LLogicLogic.cb_absurd({None{} == Some{nm_first.of(None{}, h)} : Maybe<&2, Cmd.Ent>}, h)
    case Some{e}:
      {==}

# ---- flags ----

def nm_flag_eq(a: Bool, b: Bool, h: {CommandNamed.cmd_flag_eq(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      LLogicLogic.cb_absurd({True{} == False{} : Bool}, h)
    case False{} True{}:
      LLogicLogic.cb_absurd({False{} == True{} : Bool}, h)
    case False{} False{}:
      {==}

def nm_alike_run(a: Cmd.Ent, b: Cmd.Ent, h: {CommandNamed.cmd_alike(a, b) == True{} : Bool}) -> {Cmd.Ent.run(a) == Cmd.Ent.run(b) : Bool}:
  match a b:
    case Cmd.Ent{p, x, +r, f, g} Cmd.Ent{p2, x2, +r2, f2, g2}:
      nm_flag_eq(r, r2, LLogicBool.cb_and_l(CommandNamed.cmd_flag_eq(r, r2), CommandNamed.cmd_flag_eq(f, f2), h))

def nm_alike_free(a: Cmd.Ent, b: Cmd.Ent, h: {CommandNamed.cmd_alike(a, b) == True{} : Bool}) -> {Cmd.Ent.free(a) == Cmd.Ent.free(b) : Bool}:
  match a b:
    case Cmd.Ent{p, x, +r, +f, g} Cmd.Ent{p2, x2, +r2, +f2, g2}:
      nm_flag_eq(f, f2, LLogicBool.cb_and_r(CommandNamed.cmd_flag_eq(r, r2), CommandNamed.cmd_flag_eq(f, f2), h))

# two entries of one path that run bare and take text alike finish any
# walk alike
def nm_finish_alike(ys: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +e: Cmd.Ent, +e1: Cmd.Ent, +hr: {Cmd.Ent.run(e1) == Cmd.Ent.run(e) : Bool}, +hf: {Cmd.Ent.free(e1) == Cmd.Ent.free(e) : Bool}, +hp: {Cmd.Ent.path(e1) == Cmd.Ent.path(e) : List<&2, List<&2, Nat>>}) -> {Cmd.finish(Cmd.walk(ys, t, Cmd.Walk{p, e}), t) == Cmd.finish(Cmd.walk(ys, t, Cmd.Walk{p, e1}), t) : Cmd.Res}:
  match ys:
    case Nil{}:
      %hr : {Cmd.finish.at(Bool.or(_, Bool.not(Cmd.kids.any(t, Cmd.Ent.path(e)))), p) == Cmd.finish.at(Bool.or(Cmd.Ent.run(e1), Bool.not(Cmd.kids.any(t, Cmd.Ent.path(e1)))), p) : Cmd.Res}
      %hp : {Cmd.finish.at(Bool.or(Cmd.Ent.run(e1), Bool.not(Cmd.kids.any(t, _))), p) == Cmd.finish.at(Bool.or(Cmd.Ent.run(e1), Bool.not(Cmd.kids.any(t, Cmd.Ent.path(e1)))), p) : Cmd.Res}
      {==}
    case Con{w, rest}:
      match w:
        case Nil{}:
          nm_finish_alike(rest, t, p, e, e1, hr, hf, hp)
        case Con{+c, +r}:
          %hf : {Cmd.finish(Cmd.walk(rest, t, Cmd.step.walk(Cmd.search(t, p, Cmd.lows(c <> r)), p, _, c <> r)), t) == Cmd.finish(Cmd.walk(rest, t, Cmd.step.walk(Cmd.search(t, p, Cmd.lows(c <> r)), p, Cmd.Ent.free(e1), c <> r)), t) : Cmd.Res}
          {==}

# after a miss the menu is shut, whatever follows
def nm_miss_shut(f: Bool, rest: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, x: List<&2, Nat>) -> {Cmd.menu.at(Cmd.walk(rest, t, Cmd.step.miss(f, p, w)), t, x) == Cmd.Shut{} : Cmd.Menu}:
  match f:
    case True{}:
      %Equal.sym(Cmd.St, Cmd.walk(rest, t, Cmd.Rest{p, [w]}), Cmd.Rest{p, List.append(&2, List<&2, Nat>, [w], rest)}, LA.cb_walk_rest(rest, t, p, [w])) : {Cmd.menu.at(_, t, x) == Cmd.Shut{} : Cmd.Menu}
      {==}
    case False{}:
      %Equal.sym(Cmd.St, Cmd.walk(rest, t, Cmd.Lost{p, w}), Cmd.Lost{p, w}, LA.cb_walk_lost(rest, t, p, w)) : {Cmd.menu.at(_, t, x) == Cmd.Shut{} : Cmd.Menu}
      {==}

def nm_menu_sw(m: Maybe<&2, Cmd.Ent>, f1: Bool, f2: Bool, rest: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +w: List<&2, Nat>, +x: List<&2, Nat>) -> {Cmd.menu.at(Cmd.walk(rest, t, Cmd.step.walk(m, p, f1, w)), t, x) == Cmd.menu.at(Cmd.walk(rest, t, Cmd.step.walk(m, p, f2, w)), t, x) : Cmd.Menu}:
  match m:
    case None{}:
      +rr = rest
      Equal.trans(Cmd.Menu, Cmd.menu.at(Cmd.walk(rr, t, Cmd.step.miss(f1, p, w)), t, x), Cmd.Shut{}, Cmd.menu.at(Cmd.walk(rr, t, Cmd.step.miss(f2, p, w)), t, x), nm_miss_shut(f1, rr, t, p, w, x), Equal.sym(Cmd.Menu, Cmd.menu.at(Cmd.walk(rr, t, Cmd.step.miss(f2, p, w)), t, x), Cmd.Shut{}, nm_miss_shut(f2, rr, t, p, w, x)))
    case Some{e}:
      {==}

# the menu of a walk from a path does not depend on the path's entry
def nm_menu_walk_any(d: List<&2, List<&2, Nat>>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +x: List<&2, Nat>, +e: Cmd.Ent, +e1: Cmd.Ent) -> {Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{p, e}), t, x) == Cmd.menu.at(Cmd.walk(d, t, Cmd.Walk{p, e1}), t, x) : Cmd.Menu}:
  match d:
    case Nil{}:
      {==}
    case Con{w, rest}:
      match w:
        case Nil{}:
          nm_menu_walk_any(rest, t, p, x, e, e1)
        case Con{+c, +r}:
          nm_menu_sw(Cmd.search(t, p, Cmd.lows(c <> r)), Cmd.Ent.free(e), Cmd.Ent.free(e1), rest, t, p, c <> r, x)

def nm_menu_after_any(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, +e: Cmd.Ent, +e1: Cmd.Ent) -> {nm_menu_after(c, t, Cmd.Walk{p, e}) == nm_menu_after(c, t, Cmd.Walk{p, e1}) : Cmd.Menu}:
  match c:
    case (d, x):
      nm_menu_walk_any(d, t, p, x, e, e1)

# a finished walk at an entry's own path
def nm_finish_at(b: Bool, -p: List<&2, List<&2, Nat>>) -> {Cmd.finish.at(b, p) == Command.cmd_ended.at(b, p) : Cmd.Res}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nm_finish_ent(+t: List<&2, Cmd.Ent>, e: Cmd.Ent) -> {Cmd.finish(Cmd.Walk{Cmd.Ent.path(e), e}, t) == CommandNamed.cmd_ent_ended(t, e) : Cmd.Res}:
  match e:
    case Cmd.Ent{+p, a, +r, f, g}:
      %LA.cb_kids_any(t, p) : {Cmd.finish.at(Bool.or(r, Bool.not(Cmd.kids.any(t, p))), p) == Command.cmd_ended.at(Bool.or(r, Bool.not(_)), p) : Cmd.Res}
      nm_finish_at(Bool.or(r, Bool.not(Cmd.kids.any(t, p))), p)
