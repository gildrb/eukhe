# eukhe: lemmas the key proofs of area command share
#
# A line pre ++ p keyed below q (CommandNamed.cmd_below) answers Tab and
# Enter through the row of the selection at q (kb_key): when pre is blank
# its words are empty words and then p, and the walk over the empty words
# stays at the root (kb_blank_words, kb_walk_empties); else pre ends in a
# space, the line is pre's front, a space and p (kb_front_app), and a walk
# state whose menu lists q's children is a walk at q (kb_inv). A typed p
# that names the child e of q walks into e (kb_walk). With no row, Enter
# answers key.enter on the line's resolution (kb_enter). The end of a line
# (kb_es_*), and a table's entries in a well-formed table (kb_wf_get).
# Lemma names: kb_.

import Base
import ../../../bend/command.bend as Cmd
import ../../../laws/command/paths.bend as Command
import ../../../laws/command/named.bend as CommandNamed
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/logic/nat.bend as LLogicNat
import ../../base/command.bend as LCommand
import ../base.bend as LA
import ./named.bend as LANamed

# ---- a walk state below q ----

# the entry of a walk state (d elsewhere)
def kb_ent(s: Cmd.St, d: Cmd.Ent) -> Cmd.Ent:
  match s:
    case Cmd.Top{}:
      d
    case Cmd.Walk{q, e}:
      e
    case Cmd.Rest{q, ws}:
      d
    case Cmd.Lost{q, w}:
      d
    case Cmd.Stray{}:
      d

def kb_dflt() -> Cmd.Ent:
  Cmd.Ent{Nil{}, Nil{}, False{}, False{}, False{}}

# a walk state whose menu lists children of q is a walk at q
def kb_inv(s: Cmd.St, +t: List<&2, Cmd.Ent>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, h: {Command.cmd_lists_kids(Cmd.menu.at(s, t, p), q) == True{} : Bool}) -> {s == Cmd.Walk{q, kb_ent(s, kb_dflt())} : Cmd.St}:
  match s:
    case Cmd.Top{}:
      LLogicLogic.cb_absurd({Cmd.Top{} == Cmd.Walk{q, kb_ent(Cmd.Top{}, kb_dflt())} : Cmd.St}, h)
    case Cmd.Walk{+q0, +e}:
      Equal.cong(List<&2, List<&2, Nat>>, Cmd.St, z => Cmd.Walk{z, e}, q0, q, LLogicNat.cb_path_eq(q0, q, h))
    case Cmd.Rest{q0, ws}:
      LLogicLogic.cb_absurd({Cmd.Rest{q0, ws} == Cmd.Walk{q, kb_ent(Cmd.Rest{q0, ws}, kb_dflt())} : Cmd.St}, h)
    case Cmd.Lost{q0, w}:
      LLogicLogic.cb_absurd({Cmd.Lost{q0, w} == Cmd.Walk{q, kb_ent(Cmd.Lost{q0, w}, kb_dflt())} : Cmd.St}, h)
    case Cmd.Stray{}:
      LLogicLogic.cb_absurd({Cmd.Stray{} == Cmd.Walk{q, kb_ent(Cmd.Stray{}, kb_dflt())} : Cmd.St}, h)

# ... so its key answers through the row of the selection at q
def kb_at(+s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, +p: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +q: List<&2, List<&2, Nat>>, h: {Command.cmd_lists_kids(Cmd.menu.at(s, t, p), q) == True{} : Bool}) -> {Cmd.key.at(s, t, line, p, sel, k) == Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) : Cmd.Out}:
  %Equal.sym(Cmd.St, s, Cmd.Walk{q, kb_ent(s, kb_dflt())}, kb_inv(s, t, p, q, h)) : {Cmd.key.at(_, t, line, p, sel, k) == Cmd.key.row(Cmd.row(sel, t, q), k, t, line, p) : Cmd.Out}
  {==}

# ... and a typed word p that names the child e of q steps onto e
def kb_step(+s: Cmd.St, +t: List<&2, Cmd.Ent>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, -e: Cmd.Ent, h: {Command.cmd_lists_kids(Cmd.menu.at(s, t, p), q) == True{} : Bool}, hw: {Command.cmd_typed(p) == True{} : Bool}, hit: {CommandNamed.cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.step(s, t, p) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}:
  %Equal.sym(Cmd.St, s, Cmd.Walk{q, kb_ent(s, kb_dflt())}, kb_inv(s, t, p, q, h)) : {Cmd.step(_, t, p) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
  LANamed.nm_step_of(Some{kb_ent(s, kb_dflt())}, t, q, p, e, {==}, hw, hit)

# ---- the words of a line keyed below q ----

# an empty word for each char of pre
def kb_empties(pre: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match pre:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      Nil{} <> kb_empties(r)

def kb_bw_at(b: Bool, -c: Nat, -ws: List<&2, List<&2, Nat>>, -y: List<&2, List<&2, Nat>>, hb: {b == True{} : Bool}, ih: {ws == y : List<&2, List<&2, Nat>>}) -> {Cmd.words.at(b, c, ws) == Nil{} <> y : List<&2, List<&2, Nat>>}:
  %Equal.sym(Bool, b, True{}, hb) : {Cmd.words.at(_, c, ws) == Nil{} <> y : List<&2, List<&2, Nat>>}
  Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => Nil{} <> z, ws, y, ih)

# a blank pre, then a spaceless p: an empty word per space, then p
def kb_blank_words(pre: List<&2, Nat>, +p: List<&2, Nat>, hb: {CommandNamed.cmd_blank(pre) == True{} : Bool}, hp: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(List.append(&2, Nat, pre, p)) == List.append(&2, List<&2, Nat>, kb_empties(pre), [p]) : List<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      LANamed.nm_words_word(p, hp)
    case Con{+c, +r}:
      +h2 = hb
      kb_bw_at(Nat.is_eq(c, 32n), c, Cmd.words(List.append(&2, Nat, r, p)), List.append(&2, List<&2, Nat>, kb_empties(r), [p]), LLogicBool.cb_and_l(Nat.is_eq(c, 32n), CommandNamed.cmd_blank(r), h2), kb_blank_words(r, p, LLogicBool.cb_and_r(Nat.is_eq(c, 32n), CommandNamed.cmd_blank(r), h2), hp))

# empty words leave the walk at the root
def kb_walk_empties(pre: List<&2, Nat>, +t: List<&2, Cmd.Ent>) -> {Cmd.walk(kb_empties(pre), t, Cmd.Top{}) == Cmd.Top{} : Cmd.St}:
  match pre:
    case Nil{}:
      {==}
    case Con{c, r}:
      kb_walk_empties(r, t)

# pre without its last char
def kb_front.go(r: List<&2, Nat>, c: Nat) -> List<&2, Nat>:
  match r:
    case Nil{}:
      Nil{}
    case Con{d, m}:
      c <> kb_front.go(m, d)

def kb_front(pre: List<&2, Nat>) -> List<&2, Nat>:
  match pre:
    case Nil{}:
      Nil{}
    case Con{c, r}:
      kb_front.go(r, c)

def kb_front_go(r: List<&2, Nat>, +c: Nat, -p: List<&2, Nat>, es: {CommandNamed.cmd_ends_space.go(r, c) == True{} : Bool}) -> {c <> List.append(&2, Nat, r, p) == List.append(&2, Nat, kb_front.go(r, c), 32n <> p) : List<&2, Nat>}:
  match r:
    case Nil{}:
      %Equal.sym(Nat, c, 32n, LLogicNat.cb_nat_eq(c, 32n, es)) : {_ <> p == 32n <> p : List<&2, Nat>}
      {==}
    case Con{+d, m}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, l => c <> l, d <> List.append(&2, Nat, m, p), List.append(&2, Nat, kb_front.go(m, d), 32n <> p), kb_front_go(m, d, p, es))

# a pre that ends in a space, then p: pre's front, a space and p
def kb_front_app(pre: List<&2, Nat>, -p: List<&2, Nat>, es: {CommandNamed.cmd_ends_space(pre) == True{} : Bool}) -> {List.append(&2, Nat, pre, p) == List.append(&2, Nat, kb_front(pre), 32n <> p) : List<&2, Nat>}:
  match pre:
    case Nil{}:
      LLogicLogic.cb_absurd({List.append(&2, Nat, Nil{}, p) == List.append(&2, Nat, kb_front(Nil{}), 32n <> p) : List<&2, Nat>}, es)
    case Con{+c, r}:
      kb_front_go(r, c, p, es)

# ---- the key of a line keyed below q ----

def kb_key.at(b: Bool, +t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, +sel: Cmd.Sel, +k: Cmd.Press, hb: {CommandNamed.cmd_blank(pre) == b : Bool}, +word: {Command.cmd_spaceless(p) == True{} : Bool}, +below: {CommandNamed.cmd_below.at(b, t, pre, p, q) == True{} : Bool}) -> {Cmd.key(t, List.append(&2, Nat, pre, p), sel, k) == Cmd.key.row(Cmd.row(sel, t, q), k, t, List.append(&2, Nat, pre, p), p) : Cmd.Out}:
  match b:
    case True{}:
      +L = List.append(&2, Nat, pre, p)
      +E = kb_empties(pre)
      %Equal.sym(List<&2, List<&2, Nat>>, q, Nil{}, LLogicNat.cb_path_eq(q, Nil{}, below)) : {Cmd.key(t, L, sel, k) == Cmd.key.row(Cmd.row(sel, t, _), k, t, L, p) : Cmd.Out}
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(L), List.append(&2, List<&2, Nat>, E, [p]), kb_blank_words(pre, p, hb, word)) : {Cmd.key.cut(Cmd.cut(_), t, L, sel, k) == Cmd.key.row(Cmd.row(sel, t, Nil{}), k, t, L, p) : Cmd.Out}
      %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(List.append(&2, List<&2, Nat>, E, [p])), (E, p), LA.cb_cut(E, p)) : {Cmd.key.cut(_, t, L, sel, k) == Cmd.key.row(Cmd.row(sel, t, Nil{}), k, t, L, p) : Cmd.Out}
      %Equal.sym(Cmd.St, Cmd.walk(E, t, Cmd.Top{}), Cmd.Top{}, kb_walk_empties(pre, t)) : {Cmd.key.at(_, t, L, p, sel, k) == Cmd.key.row(Cmd.row(sel, t, Nil{}), k, t, L, p) : Cmd.Out}
      {==}
    case False{}:
      +F = kb_front(pre)
      +es = LLogicBool.cb_and_l(CommandNamed.cmd_ends_space(pre), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), below)
      +lk = LLogicBool.cb_and_r(CommandNamed.cmd_ends_space(pre), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), below)
      +L = List.append(&2, Nat, F, 32n <> p)
      +S = Cmd.walk(Cmd.words(F), t, Cmd.Top{})
      +fa = kb_front_app(pre, p, es)
      +lk2 = Equal.trans(Bool, Command.cmd_lists_kids(Cmd.menu(t, L), q), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), True{}, Equal.cong(List<&2, Nat>, Bool, z => Command.cmd_lists_kids(Cmd.menu(t, z), q), L, List.append(&2, Nat, pre, p), Equal.sym(List<&2, Nat>, List.append(&2, Nat, pre, p), L, fa)), lk)
      +h = Equal.trans(Bool, Command.cmd_lists_kids(Cmd.menu.at(S, t, p), q), Command.cmd_lists_kids(Cmd.menu(t, L), q), True{}, Equal.cong(Cmd.Menu, Bool, m => Command.cmd_lists_kids(m, q), Cmd.menu.at(S, t, p), Cmd.menu(t, L), Equal.sym(Cmd.Menu, Cmd.menu(t, L), Cmd.menu.at(S, t, p), LANamed.nm_menu_pre(t, F, p, word))), lk2)
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, pre, p), L, fa) : {Cmd.key(t, _, sel, k) == Cmd.key.row(Cmd.row(sel, t, q), k, t, _, p) : Cmd.Out}
      %Equal.sym(Cmd.Out, Cmd.key(t, L, sel, k), Cmd.key.at(S, t, L, p, sel, k), LANamed.nm_key_pre(t, F, p, sel, k, word)) : {_ == Cmd.key.row(Cmd.row(sel, t, q), k, t, L, p) : Cmd.Out}
      kb_at(S, t, L, p, sel, k, q, h)

# the keys of the line pre ++ p keyed below q answer through the row of
# the selection at q
def kb_key(+t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, sel: Cmd.Sel, k: Cmd.Press, +word: {Command.cmd_spaceless(p) == True{} : Bool}, below: {CommandNamed.cmd_below(t, pre, p, q) == True{} : Bool}) -> {Cmd.key(t, List.append(&2, Nat, pre, p), sel, k) == Cmd.key.row(Cmd.row(sel, t, q), k, t, List.append(&2, Nat, pre, p), p) : Cmd.Out}:
  kb_key.at(CommandNamed.cmd_blank(pre), t, pre, p, q, sel, k, {==}, word, below)

# ---- the walk of a line keyed below q, into a named child ----

def kb_walk.at(b: Bool, +t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, -e: Cmd.Ent, hb: {CommandNamed.cmd_blank(pre) == b : Bool}, +word: {Command.cmd_typed(p) == True{} : Bool}, +below: {CommandNamed.cmd_below.at(b, t, pre, p, q) == True{} : Bool}, +hit: {CommandNamed.cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.walk(Cmd.words(List.append(&2, Nat, pre, p)), t, Cmd.Top{}) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}:
  match b:
    case True{}:
      +sp = LA.cb_typed_spaceless(p, word)
      +E = kb_empties(pre)
      +qn = LLogicNat.cb_path_eq(q, Nil{}, below)
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(List.append(&2, Nat, pre, p)), List.append(&2, List<&2, Nat>, E, [p]), kb_blank_words(pre, p, hb, sp)) : {Cmd.walk(_, t, Cmd.Top{}) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, E, [p]), t, Cmd.Top{}), Cmd.walk([p], t, Cmd.walk(E, t, Cmd.Top{})), LA.cb_walk_app(E, [p], t, Cmd.Top{})) : {_ == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Cmd.St, Cmd.walk(E, t, Cmd.Top{}), Cmd.Top{}, kb_walk_empties(pre, t)) : {Cmd.walk([p], t, _) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %qn : {Cmd.step(LA.cb_st(t, _), t, p) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      LANamed.nm_step(t, q, p, e, Equal.trans(Bool, LA.cb_at(t, q), LA.cb_at(t, Nil{}), True{}, Equal.cong(List<&2, List<&2, Nat>>, Bool, z => LA.cb_at(t, z), q, Nil{}, qn), {==}), word, hit)
    case False{}:
      +sp = LA.cb_typed_spaceless(p, word)
      +F = kb_front(pre)
      +es = LLogicBool.cb_and_l(CommandNamed.cmd_ends_space(pre), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), below)
      +lk = LLogicBool.cb_and_r(CommandNamed.cmd_ends_space(pre), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), below)
      +L = List.append(&2, Nat, F, 32n <> p)
      +ws = Cmd.words(F)
      +S = Cmd.walk(ws, t, Cmd.Top{})
      +fa = kb_front_app(pre, p, es)
      +lk2 = Equal.trans(Bool, Command.cmd_lists_kids(Cmd.menu(t, L), q), Command.cmd_lists_kids(Cmd.menu(t, List.append(&2, Nat, pre, p)), q), True{}, Equal.cong(List<&2, Nat>, Bool, z => Command.cmd_lists_kids(Cmd.menu(t, z), q), L, List.append(&2, Nat, pre, p), Equal.sym(List<&2, Nat>, List.append(&2, Nat, pre, p), L, fa)), lk)
      +h = Equal.trans(Bool, Command.cmd_lists_kids(Cmd.menu.at(S, t, p), q), Command.cmd_lists_kids(Cmd.menu(t, L), q), True{}, Equal.cong(Cmd.Menu, Bool, m => Command.cmd_lists_kids(m, q), Cmd.menu.at(S, t, p), Cmd.menu(t, L), Equal.sym(Cmd.Menu, Cmd.menu(t, L), Cmd.menu.at(S, t, p), LANamed.nm_menu_pre(t, F, p, sp))), lk2)
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, pre, p), L, fa) : {Cmd.walk(Cmd.words(_), t, Cmd.Top{}) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(L), List.append(&2, List<&2, Nat>, ws, [p]), LANamed.nm_words_last(F, p, sp)) : {Cmd.walk(_, t, Cmd.Top{}) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, ws, [p]), t, Cmd.Top{}), Cmd.walk([p], t, S), LA.cb_walk_app(ws, [p], t, Cmd.Top{})) : {_ == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}
      kb_step(S, t, p, q, e, h, word, hit)

# the line pre ++ p keyed below q, p typed and naming the child e of q,
# walks into e
def kb_walk(+t: List<&2, Cmd.Ent>, +pre: List<&2, Nat>, +p: List<&2, Nat>, +q: List<&2, List<&2, Nat>>, -e: Cmd.Ent, +word: {Command.cmd_typed(p) == True{} : Bool}, below: {CommandNamed.cmd_below(t, pre, p, q) == True{} : Bool}, +hit: {CommandNamed.cmd_named(t, q, p) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Cmd.walk(Cmd.words(List.append(&2, Nat, pre, p)), t, Cmd.Top{}) == Cmd.Walk{Cmd.Ent.path(e), e} : Cmd.St}:
  kb_walk.at(CommandNamed.cmd_blank(pre), t, pre, p, q, e, {==}, word, below, hit)

# ---- Enter with no row ----

def kb_enter_at(s: Cmd.St, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>, p: List<&2, Nat>) -> {Cmd.key.at(s, t, line, p, Cmd.NoRow{}, Cmd.Enter{}) == Cmd.key.enter(Cmd.resolve(t, line), line) : Cmd.Out}:
  match s:
    case Cmd.Top{}:
      {==}
    case Cmd.Walk{q, e}:
      {==}
    case Cmd.Rest{q, ws}:
      {==}
    case Cmd.Lost{q, w}:
      {==}
    case Cmd.Stray{}:
      {==}

def kb_enter_cut(c: List<&2, List<&2, Nat>> & List<&2, Nat>, +t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.key.cut(c, t, line, Cmd.NoRow{}, Cmd.Enter{}) == Cmd.key.enter(Cmd.resolve(t, line), line) : Cmd.Out}:
  match c:
    case (d, p):
      kb_enter_at(Cmd.walk(d, t, Cmd.Top{}), t, line, p)

# with no row, Enter answers key.enter on the line's resolution, at
# every walk state
def kb_enter(+t: List<&2, Cmd.Ent>, +line: List<&2, Nat>) -> {Cmd.key(t, line, Cmd.NoRow{}, Cmd.Enter{}) == Cmd.key.enter(Cmd.resolve(t, line), line) : Cmd.Out}:
  kb_enter_cut(Cmd.cut(Cmd.words(line)), t, line)

# ---- names ----

# the model's names is cmd_names
def kb_names(e: Cmd.Ent, +p: List<&2, Nat>) -> {Cmd.names(Cmd.lows(p), e) == CommandNamed.cmd_names(Command.cmd_lower(p), e) : Bool}:
  match e:
    case Cmd.Ent{+pp, +a, r, f, g}:
      %LA.cb_lows(p) : {Cmd.names(Cmd.lows(p), Cmd.Ent{pp, a, r, f, g}) == Bool.or(Command.cmd_eq(_, Command.cmd_last(pp)), Command.cmd_in(_, a)) : Bool}
      %LA.cb_last(pp) : {Cmd.names(Cmd.lows(p), Cmd.Ent{pp, a, r, f, g}) == Bool.or(Command.cmd_eq(Cmd.lows(p), _), Command.cmd_in(Cmd.lows(p), a)) : Bool}
      %LCommand.cb_same(Cmd.lows(p), Cmd.last(pp)) : {Cmd.names(Cmd.lows(p), Cmd.Ent{pp, a, r, f, g}) == Bool.or(_, Command.cmd_in(Cmd.lows(p), a)) : Bool}
      %LA.cb_has(a, Cmd.lows(p)) : {Cmd.names(Cmd.lows(p), Cmd.Ent{pp, a, r, f, g}) == Bool.or(Cmd.same(Cmd.lows(p), Cmd.last(pp)), _) : Bool}
      {==}

# ---- the end of a line ----

def kb_go_snoc(r: List<&2, Nat>, c: Nat) -> {CommandNamed.cmd_ends_space.go(List.append(&2, Nat, r, [32n]), c) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{d, m}:
      kb_go_snoc(m, d)

# a line and then a space ends in a space
def kb_es_snoc(l: List<&2, Nat>) -> {CommandNamed.cmd_ends_space(List.append(&2, Nat, l, [32n])) == True{} : Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{c, r}:
      kb_go_snoc(r, c)

# a word with no space does not end in one
def kb_go_word(r: List<&2, Nat>, +c: Nat, h: {Command.cmd_spaceless(c <> r) == True{} : Bool}) -> {CommandNamed.cmd_ends_space.go(r, c) == False{} : Bool}:
  match r:
    case Nil{}:
      LA.cb_not_true(Nat.is_eq(c, 32n), LLogicBool.cb_and_l(Bool.not(Nat.is_eq(c, 32n)), True{}, h))
    case Con{+d, +m}:
      kb_go_word(m, d, LLogicBool.cb_and_r(Bool.not(Nat.is_eq(c, 32n)), Command.cmd_spaceless(d <> m), h))

# the end of a ++ (d <> m) is the end of d <> m
def kb_go_app(a: List<&2, Nat>, c: Nat, -d: Nat, -m: List<&2, Nat>) -> {CommandNamed.cmd_ends_space.go(List.append(&2, Nat, a, d <> m), c) == CommandNamed.cmd_ends_space.go(m, d) : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, r}:
      kb_go_app(r, x, d, m)

def kb_es_render.go(rest: List<&2, List<&2, Nat>>, +xr: List<&2, Nat>, +c: Nat, h: {Command.cmd_names_ok((c <> xr) <> rest) == True{} : Bool}) -> {CommandNamed.cmd_ends_space.go(List.append(&2, Nat, xr, Command.cmd_sep(rest)), c) == False{} : Bool}:
  match rest:
    case Nil{}:
      +hx = LLogicBool.cb_and_l(Command.cmd_typed(c <> xr), Command.cmd_eq(Command.cmd_lower(c <> xr), c <> xr), LLogicBool.cb_and_l(Command.cmd_name_ok(c <> xr), True{}, h))
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, xr, Nil{}), xr, LA.cb_app_nil(Nat, xr)) : {CommandNamed.cmd_ends_space.go(_, c) == False{} : Bool}
      kb_go_word(xr, c, hx)
    case Con{y, +more}:
      match y:
        case Nil{}:
          LLogicLogic.cb_absurd({CommandNamed.cmd_ends_space.go(List.append(&2, Nat, xr, Command.cmd_sep(Nil{} <> more)), c) == False{} : Bool}, LLogicBool.cb_and_r(Command.cmd_name_ok(c <> xr), Command.cmd_names_ok(Nil{} <> more), h))
        case Con{+c2, +yr}:
          +hr = LLogicBool.cb_and_r(Command.cmd_name_ok(c <> xr), Command.cmd_names_ok((c2 <> yr) <> more), h)
          +X = List.append(&2, Nat, c2 <> yr, Command.cmd_sep(more))
          %Equal.sym(Bool, CommandNamed.cmd_ends_space.go(List.append(&2, Nat, xr, 32n <> X), c), CommandNamed.cmd_ends_space.go(X, 32n), kb_go_app(xr, c, 32n, X)) : {_ == False{} : Bool}
          kb_es_render.go(more, yr, c2, hr)

def kb_es_word(x: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, h: {Command.cmd_names_ok(x <> rest) == True{} : Bool}) -> {CommandNamed.cmd_ends_space(Command.cmd_render(x <> rest)) == False{} : Bool}:
  match x:
    case Nil{}:
      LLogicLogic.cb_absurd({CommandNamed.cmd_ends_space(Command.cmd_render(Nil{} <> rest)) == False{} : Bool}, h)
    case Con{+c, +xr}:
      kb_es_render.go(rest, xr, c, h)

# the line of a child's path, all its names names, does not end in a
# space
def kb_es_kid(+q: List<&2, List<&2, Nat>>, pp: List<&2, List<&2, Nat>>, h: {Command.cmd_names_ok(pp) == True{} : Bool}, ck: {Command.cmd_is_kid(q, pp) == True{} : Bool}) -> {CommandNamed.cmd_ends_space(Command.cmd_render(pp)) == False{} : Bool}:
  match pp:
    case Nil{}:
      LLogicLogic.cb_absurd({CommandNamed.cmd_ends_space(Command.cmd_render(Nil{})) == False{} : Bool}, ck)
    case Con{x, rest}:
      kb_es_word(x, rest, h)

def kb_wf_head(c: Cmd.Ent, -rest: List<&2, Cmd.Ent>, -e: Cmd.Ent, ok: {Command.cmd_wf(c <> rest) == True{} : Bool}, at: {Some{c} == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_names_ok(Command.cmd_ent_path(e)) == True{} : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      %LANamed.nm_some_inj(Cmd.Ent{p, a, r, f, g}, e, at) : {Command.cmd_names_ok(Command.cmd_ent_path(_)) == True{} : Bool}
      LLogicBool.cb_and_l(Command.cmd_names_ok(p), Command.cmd_names_ok(a), LLogicBool.cb_and_l(Bool.and(Command.cmd_names_ok(p), Command.cmd_names_ok(a)), Command.cmd_wf(rest), ok))

def kb_wf_tail(c: Cmd.Ent, -rest: List<&2, Cmd.Ent>, ok: {Command.cmd_wf(c <> rest) == True{} : Bool}) -> {Command.cmd_wf(rest) == True{} : Bool}:
  match c:
    case Cmd.Ent{+p, +a, r, f, g}:
      LLogicBool.cb_and_r(Bool.and(Command.cmd_names_ok(p), Command.cmd_names_ok(a)), Command.cmd_wf(rest), ok)

# in a well-formed table every name of an entry's path is a name
def kb_wf_get(t: List<&2, Cmd.Ent>, i: Nat, -e: Cmd.Ent, ok: {Command.cmd_wf(t) == True{} : Bool}, at: {List.get(&2, Cmd.Ent, t, i) == Some{e} : Maybe<&2, Cmd.Ent>}) -> {Command.cmd_names_ok(Command.cmd_ent_path(e)) == True{} : Bool}:
  match t i:
    case Nil{} 0n:
      LLogicLogic.cb_absurd({Command.cmd_names_ok(Command.cmd_ent_path(e)) == True{} : Bool}, LANamed.nm_none_some(e, at))
    case Nil{} 1n+k:
      LLogicLogic.cb_absurd({Command.cmd_names_ok(Command.cmd_ent_path(e)) == True{} : Bool}, LANamed.nm_none_some(e, at))
    case Con{c, rest} 0n:
      kb_wf_head(c, rest, e, ok, at)
    case Con{+c, rest} 1n+k:
      kb_wf_get(rest, k, e, kb_wf_tail(c, rest, ok), at)

# Tab's answer on a row whose line does not end in a space: closed by a
# space it is that line and a space, ending in one exactly when b
def kb_shape(b: Bool, +R: List<&2, Nat>, -K: Bool, h: {CommandNamed.cmd_ends_space(R) == False{} : Bool}) -> {CommandNamed.cmd_out_shape(Cmd.Out{Cmd.spaced(b, R), K, False{}}) == (List.append(&2, Nat, R, [32n]), (b, (K, False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}:
  match b:
    case True{}:
      +RS = List.append(&2, Nat, R, [32n])
      %Equal.sym(Bool, CommandNamed.cmd_ends_space(RS), True{}, kb_es_snoc(R)) : {(CommandNamed.cmd_closed.at(_, RS), (_, (K, False{}))) == (RS, (True{}, (K, False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}
      {==}
    case False{}:
      %Equal.sym(Bool, CommandNamed.cmd_ends_space(R), False{}, h) : {(CommandNamed.cmd_closed.at(_, R), (_, (K, False{}))) == (List.append(&2, Nat, R, [32n]), (False{}, (K, False{}))) : List<&2, Nat> & (Bool & (Bool & Bool))}
      {==}
