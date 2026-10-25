# eukhe: lemmas the spacing proofs of area command share
#
# The words of a line typed with extra spaces (cmd_loose, or a rendered
# path and then more text): a run of n spaces gives n empty words
# (sp_blanks), and every other word is the typed one (sp_ls, sp_lsi).
# The walk skips an empty word at the root and at a declared path
# (step.empty), so the walk over the loose words lands where the walk
# over the single-spaced ones lands. Lemma names: sp_.

import Base
import ../../../bend/command.bend as Cmd
import ../../../laws/command/paths.bend as Command
import ../../base/bool.bend as LBool
import ../../base/list.bend as LList
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../base.bend as LA

# Words
# -----

# n empty words
def sp_blanks(n: Nat) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Nil{} <> sp_blanks(m)

# the words of cmd_loose(ws, gs) (ws not empty), and of
# cmd_loose.sep(ws, gs) after its leading empty word: each word of ws,
# after the empty words of its run of extra spaces
def sp_ls(ws: List<&2, List<&2, Nat>>, gs: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      match gs:
        case Nil{}:
          w <> sp_ls(rest, Nil{})
        case Con{g, more}:
          List.append(&2, List<&2, Nat>, sp_blanks(g), w <> sp_ls(rest, more))

# the words of cmd_loose(q ++ [p], gs) before the last word p
def sp_lsi(q: List<&2, List<&2, Nat>>, gs: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match q:
    case Nil{}:
      match gs:
        case Nil{}:
          Nil{}
        case Con{g, more}:
          sp_blanks(g)
    case Con{w, rest}:
      match gs:
        case Nil{}:
          w <> sp_lsi(rest, Nil{})
        case Con{g, more}:
          List.append(&2, List<&2, Nat>, sp_blanks(g), w <> sp_lsi(rest, more))

def sp_ls_last(q: List<&2, List<&2, Nat>>, -p: List<&2, Nat>, gs: List<&2, Nat>) -> {sp_ls(List.append(&2, List<&2, Nat>, q, [p]), gs) == List.append(&2, List<&2, Nat>, sp_lsi(q, gs), [p]) : List<&2, List<&2, Nat>>}:
  match q:
    case Nil{}:
      match gs:
        case Nil{}:
          {==}
        case Con{g, more}:
          {==}
    case Con{+w, rest}:
      match gs:
        case Nil{}:
          %sp_ls_last(rest, p, Nil{}) : {w <> sp_ls(List.append(&2, List<&2, Nat>, rest, [p]), Nil{}) == w <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Con{+g, more}:
          %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, sp_blanks(g), w <> sp_lsi(rest, more)), [p]), List.append(&2, List<&2, Nat>, sp_blanks(g), List.append(&2, List<&2, Nat>, w <> sp_lsi(rest, more), [p])), LList.cb_app_assoc(List<&2, Nat>, sp_blanks(g), w <> sp_lsi(rest, more), [p])) : {List.append(&2, List<&2, Nat>, sp_blanks(g), w <> sp_ls(List.append(&2, List<&2, Nat>, rest, [p]), more)) == _ : List<&2, List<&2, Nat>>}
          %sp_ls_last(rest, p, more) : {List.append(&2, List<&2, Nat>, sp_blanks(g), w <> sp_ls(List.append(&2, List<&2, Nat>, rest, [p]), more)) == List.append(&2, List<&2, Nat>, sp_blanks(g), w <> _) : List<&2, List<&2, Nat>>}
          {==}

# a run of spaces: its empty words
def sp_words_spaces(n: Nat, -s: List<&2, Nat>) -> {Cmd.words(List.append(&2, Nat, Command.cmd_spaces(n), s)) == List.append(&2, List<&2, Nat>, sp_blanks(n), Cmd.words(s)) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %sp_words_spaces(m, s) : {Nil{} <> Cmd.words(List.append(&2, Nat, Command.cmd_spaces(m), s)) == Nil{} <> _ : List<&2, List<&2, Nat>>}
      {==}

# a spaceless word w, then text l whose words (with s after) start with
# an empty word: w takes that word's place
def sp_words_word(+w: List<&2, Nat>, -l: List<&2, Nat>, -s: List<&2, Nat>, -r: List<&2, List<&2, Nat>>, hw: {Command.cmd_spaceless(w) == True{} : Bool}, ih: {Cmd.words(List.append(&2, Nat, l, s)) == Nil{} <> r : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, List.append(&2, Nat, w, l), s)) == w <> r : List<&2, List<&2, Nat>>}:
  -lhs = Cmd.words(List.append(&2, Nat, List.append(&2, Nat, w, l), s))
  %LA.cb_app_nil(Nat, w) : {lhs == _ <> r : List<&2, List<&2, Nat>>}
  %LA.cb_put_con(w, Nil{}, r) : {lhs == _ : List<&2, List<&2, Nat>>}
  %ih : {lhs == LA.cb_put(w, _) : List<&2, List<&2, Nat>>}
  %LA.cb_words_app(w, List.append(&2, Nat, l, s), hw) : {lhs == _ : List<&2, List<&2, Nat>>}
  %LList.cb_app_assoc(Nat, w, l, s) : {lhs == Cmd.words(_) : List<&2, List<&2, Nat>>}
  {==}

# a run of g spaces, then w as in sp_words_word
def sp_words_gap(+g: Nat, +w: List<&2, Nat>, -l: List<&2, Nat>, -s: List<&2, Nat>, -r: List<&2, List<&2, Nat>>, hw: {Command.cmd_spaceless(w) == True{} : Bool}, ih: {Cmd.words(List.append(&2, Nat, l, s)) == Nil{} <> r : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, List.append(&2, Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, l)), s)) == List.append(&2, List<&2, Nat>, sp_blanks(g), w <> r) : List<&2, List<&2, Nat>>}:
  -lhs = Cmd.words(List.append(&2, Nat, List.append(&2, Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, l)), s))
  %sp_words_word(w, l, s, r, hw, ih) : {lhs == List.append(&2, List<&2, Nat>, sp_blanks(g), _) : List<&2, List<&2, Nat>>}
  %sp_words_spaces(g, List.append(&2, Nat, List.append(&2, Nat, w, l), s)) : {lhs == _ : List<&2, List<&2, Nat>>}
  %LList.cb_app_assoc(Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, l), s) : {lhs == Cmd.words(_) : List<&2, List<&2, Nat>>}
  {==}

# the words of cmd_loose.sep(ws, gs), then text s whose words are an
# empty word and y
def sp_words_lsep(ws: List<&2, List<&2, Nat>>, gs: List<&2, Nat>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(ws) == True{} : Bool}, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_loose.sep(ws, gs), s)) == Nil{} <> List.append(&2, List<&2, Nat>, sp_ls(ws, gs), y) : List<&2, List<&2, Nat>>}:
  match ws:
    case Nil{}:
      match gs:
        case Nil{}:
          hs
        case Con{g, more}:
          hs
    case Con{+w, +rest}:
      match gs:
        case Nil{}:
          %sp_words_word(w, Command.cmd_loose.sep(rest, Nil{}), s, List.append(&2, List<&2, Nat>, sp_ls(rest, Nil{}), y), LLogicBool.cb_and_l(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), sp_words_lsep(rest, Nil{}, s, y, LLogicBool.cb_and_r(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), hs)) : {Nil{} <> Cmd.words(List.append(&2, Nat, List.append(&2, Nat, w, Command.cmd_loose.sep(rest, Nil{})), s)) == Nil{} <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Con{+g, +more}:
          +ls = sp_ls(rest, more)
          %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, sp_blanks(g), w <> ls), y), List.append(&2, List<&2, Nat>, sp_blanks(g), List.append(&2, List<&2, Nat>, w <> ls, y)), LList.cb_app_assoc(List<&2, Nat>, sp_blanks(g), w <> ls, y)) : {Nil{} <> Cmd.words(List.append(&2, Nat, List.append(&2, Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, Command.cmd_loose.sep(rest, more))), s)) == Nil{} <> _ : List<&2, List<&2, Nat>>}
          %sp_words_gap(g, w, Command.cmd_loose.sep(rest, more), s, List.append(&2, List<&2, Nat>, ls, y), LLogicBool.cb_and_l(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), sp_words_lsep(rest, more, s, y, LLogicBool.cb_and_r(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), hs)) : {Nil{} <> Cmd.words(List.append(&2, Nat, List.append(&2, Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, Command.cmd_loose.sep(rest, more))), s)) == Nil{} <> _ : List<&2, List<&2, Nat>>}
          {==}

# the words of a loose line of the words w <> rest, then text s whose
# words are an empty word and y
def sp_words_loose(+w: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, gs: List<&2, Nat>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(w <> rest) == True{} : Bool}, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_loose(w <> rest, gs), s)) == List.append(&2, List<&2, Nat>, sp_ls(w <> rest, gs), y) : List<&2, List<&2, Nat>>}:
  match gs:
    case Nil{}:
      sp_words_word(w, Command.cmd_loose.sep(rest, Nil{}), s, List.append(&2, List<&2, Nat>, sp_ls(rest, Nil{}), y), LLogicBool.cb_and_l(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), sp_words_lsep(rest, Nil{}, s, y, LLogicBool.cb_and_r(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), hs))
    case Con{+g, +more}:
      +ls = sp_ls(rest, more)
      %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, List.append(&2, List<&2, Nat>, sp_blanks(g), w <> ls), y), List.append(&2, List<&2, Nat>, sp_blanks(g), List.append(&2, List<&2, Nat>, w <> ls, y)), LList.cb_app_assoc(List<&2, Nat>, sp_blanks(g), w <> ls, y)) : {Cmd.words(List.append(&2, Nat, List.append(&2, Nat, Command.cmd_spaces(g), List.append(&2, Nat, w, Command.cmd_loose.sep(rest, more))), s)) == _ : List<&2, List<&2, Nat>>}
      sp_words_gap(g, w, Command.cmd_loose.sep(rest, more), s, List.append(&2, List<&2, Nat>, ls, y), LLogicBool.cb_and_l(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), sp_words_lsep(rest, more, s, y, LLogicBool.cb_and_r(Command.cmd_spaceless(w), Command.cmd_all_spaceless(rest), h), hs))

# the same for the words q ++ [p]
def sp_words_loose_last(q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, gs: List<&2, Nat>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, h: {Command.cmd_all_spaceless(List.append(&2, List<&2, Nat>, q, [p])) == True{} : Bool}, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs), s)) == List.append(&2, List<&2, Nat>, sp_ls(List.append(&2, List<&2, Nat>, q, [p]), gs), y) : List<&2, List<&2, Nat>>}:
  match q:
    case Nil{}:
      sp_words_loose(p, Nil{}, gs, s, y, h, hs)
    case Con{+v, +vs}:
      sp_words_loose(v, List.append(&2, List<&2, Nat>, vs, [p]), gs, s, y, h, hs)

# the words of a space before each word of rest, then text s whose words
# are an empty word and y
def sp_words_sep(rest: List<&2, List<&2, Nat>>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(rest) == True{} : Bool}, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_sep(rest), s)) == Nil{} <> List.append(&2, List<&2, Nat>, rest, y) : List<&2, List<&2, Nat>>}:
  match rest:
    case Nil{}:
      hs
    case Con{+v, +r}:
      +hv = LLogicBool.cb_and_l(Command.cmd_spaceless(v), Command.cmd_all_spaceless(r), h)
      +hr = LLogicBool.cb_and_r(Command.cmd_spaceless(v), Command.cmd_all_spaceless(r), h)
      %sp_words_word(v, Command.cmd_sep(r), s, List.append(&2, List<&2, Nat>, r, y), hv, sp_words_sep(r, s, y, hr, hs)) : {Nil{} <> Cmd.words(List.append(&2, Nat, List.append(&2, Nat, v, Command.cmd_sep(r)), s)) == Nil{} <> _ : List<&2, List<&2, Nat>>}
      {==}

# the words of the line of the path x <> rest, then text s whose words
# are an empty word and y
def sp_words_render(+x: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, -s: List<&2, Nat>, -y: List<&2, List<&2, Nat>>, +h: {Command.cmd_all_spaceless(x <> rest) == True{} : Bool}, hs: {Cmd.words(s) == Nil{} <> y : List<&2, List<&2, Nat>>}) -> {Cmd.words(List.append(&2, Nat, Command.cmd_render(x <> rest), s)) == x <> List.append(&2, List<&2, Nat>, rest, y) : List<&2, List<&2, Nat>>}:
  sp_words_word(x, Command.cmd_sep(rest), s, List.append(&2, List<&2, Nat>, rest, y), LLogicBool.cb_and_l(Command.cmd_spaceless(x), Command.cmd_all_spaceless(rest), h), sp_words_sep(rest, s, y, LLogicBool.cb_and_r(Command.cmd_spaceless(x), Command.cmd_all_spaceless(rest), h), hs))

# a line's words are never none
def sp_ne(ws: List<&2, List<&2, Nat>>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case Con{w, rest}:
      True{}

def sp_ne_at(b: Bool, -c: Nat, ws: List<&2, List<&2, Nat>>) -> {sp_ne(Cmd.words.at(b, c, ws)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match ws:
        case Nil{}:
          {==}
        case Con{w, rest}:
          {==}

def sp_words_ne(line: List<&2, Nat>) -> {sp_ne(Cmd.words(line)) == True{} : Bool}:
  match line:
    case Nil{}:
      {==}
    case Con{+c, r}:
      sp_ne_at(Nat.is_eq(c, 32n), c, Cmd.words(r))

# The walk
# --------

def sp_empty_of(m: Maybe<&2, Cmd.Ent>, -p: List<&2, List<&2, Nat>>) -> {Cmd.step.empty(LA.cb_st.of(m, p)) == LA.cb_st.of(m, p) : Cmd.St}:
  match m:
    case None{}:
      {==}
    case Some{e}:
      {==}

# an empty word leaves the walk at the root or at a path where it is
def sp_empty_st(+t: List<&2, Cmd.Ent>, q: List<&2, List<&2, Nat>>) -> {Cmd.step.empty(LA.cb_st(t, q)) == LA.cb_st(t, q) : Cmd.St}:
  match q:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      sp_empty_of(Command.cmd_lookup(t, x <> rest), x <> rest)

def sp_walk_blanks(n: Nat, +t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>) -> {Cmd.walk(sp_blanks(n), t, LA.cb_st(t, q)) == LA.cb_st(t, q) : Cmd.St}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Cmd.St, Cmd.step.empty(LA.cb_st(t, q)), LA.cb_st(t, q), sp_empty_st(t, q)) : {Cmd.walk(sp_blanks(m), t, _) == LA.cb_st(t, q) : Cmd.St}
      sp_walk_blanks(m, t, q)

# the walk lemma of loose words: from the state of acc, the loose words
# of q (before a last word) land on the state of acc ++ q
def sp_walk_lsi(q: List<&2, List<&2, Nat>>, gs: List<&2, Nat>, +t: List<&2, Cmd.Ent>, +acc: List<&2, List<&2, Nat>>, +ok: {Command.cmd_wf(t) == True{} : Bool}, at: {LA.cb_at(t, acc) == True{} : Bool}, +h: {Command.cmd_walks.go(q, t, acc) == True{} : Bool}) -> {Cmd.walk(sp_lsi(q, gs), t, LA.cb_st(t, acc)) == LA.cb_st(t, List.append(&2, List<&2, Nat>, acc, q)) : Cmd.St}:
  match q:
    case Nil{}:
      match gs:
        case Nil{}:
          %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, acc, Nil{}), acc, LA.cb_app_nil(List<&2, Nat>, acc)) : {LA.cb_st(t, acc) == LA.cb_st(t, _) : Cmd.St}
          {==}
        case Con{+g, more}:
          %Equal.sym(List<&2, List<&2, Nat>>, List.append(&2, List<&2, Nat>, acc, Nil{}), acc, LA.cb_app_nil(List<&2, Nat>, acc)) : {Cmd.walk(sp_blanks(g), t, LA.cb_st(t, acc)) == LA.cb_st(t, _) : Cmd.St}
          sp_walk_blanks(g, t, acc)
    case Con{+x, +more}:
      match gs:
        case Nil{}:
          +ax = List.append(&2, List<&2, Nat>, acc, [x])
          +d = LLogicBool.cb_and_l(Command.cmd_declared(t, ax), Command.cmd_walks.go(more, t, ax), h)
          %Equal.sym(Cmd.St, Cmd.step(LA.cb_st(t, acc), t, x), LA.cb_st(t, ax), LA.cb_step(t, acc, x, ok, at, d)) : {Cmd.walk(sp_lsi(more, Nil{}), t, _) == LA.cb_st(t, List.append(&2, List<&2, Nat>, acc, x <> more)) : Cmd.St}
          %LList.cb_app_assoc(List<&2, Nat>, acc, [x], more) : {Cmd.walk(sp_lsi(more, Nil{}), t, LA.cb_st(t, ax)) == LA.cb_st(t, _) : Cmd.St}
          sp_walk_lsi(more, Nil{}, t, ax, ok, LA.cb_at_app(t, acc, x, d), LLogicBool.cb_and_r(Command.cmd_declared(t, ax), Command.cmd_walks.go(more, t, ax), h))
        case Con{+g, +m}:
          +ax = List.append(&2, List<&2, Nat>, acc, [x])
          +d = LLogicBool.cb_and_l(Command.cmd_declared(t, ax), Command.cmd_walks.go(more, t, ax), h)
          +rest = {x <> sp_lsi(more, m) : List<&2, List<&2, Nat>>}
          %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, sp_blanks(g), rest), t, LA.cb_st(t, acc)), Cmd.walk(rest, t, Cmd.walk(sp_blanks(g), t, LA.cb_st(t, acc))), LA.cb_walk_app(sp_blanks(g), rest, t, LA.cb_st(t, acc))) : {_ == LA.cb_st(t, List.append(&2, List<&2, Nat>, acc, x <> more)) : Cmd.St}
          %Equal.sym(Cmd.St, Cmd.walk(sp_blanks(g), t, LA.cb_st(t, acc)), LA.cb_st(t, acc), sp_walk_blanks(g, t, acc)) : {Cmd.walk(rest, t, _) == LA.cb_st(t, List.append(&2, List<&2, Nat>, acc, x <> more)) : Cmd.St}
          %Equal.sym(Cmd.St, Cmd.step(LA.cb_st(t, acc), t, x), LA.cb_st(t, ax), LA.cb_step(t, acc, x, ok, at, d)) : {Cmd.walk(sp_lsi(more, m), t, _) == LA.cb_st(t, List.append(&2, List<&2, Nat>, acc, x <> more)) : Cmd.St}
          %LList.cb_app_assoc(List<&2, Nat>, acc, [x], more) : {Cmd.walk(sp_lsi(more, m), t, LA.cb_st(t, ax)) == LA.cb_st(t, _) : Cmd.St}
          sp_walk_lsi(more, m, t, ax, ok, LA.cb_at_app(t, acc, x, d), LLogicBool.cb_and_r(Command.cmd_declared(t, ax), Command.cmd_walks.go(more, t, ax), h))

# the loose words of a walked path q walk from the root as q does
def sp_walk_loose(+q: List<&2, List<&2, Nat>>, +gs: List<&2, Nat>, +t: List<&2, Cmd.Ent>, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}) -> {Cmd.walk(sp_lsi(q, gs), t, Cmd.Top{}) == Cmd.walk(q, t, Cmd.Top{}) : Cmd.St}:
  Equal.trans(Cmd.St, Cmd.walk(sp_lsi(q, gs), t, Cmd.Top{}), LA.cb_st(t, q), Cmd.walk(q, t, Cmd.Top{}), sp_walk_lsi(q, gs, t, Nil{}, ok, {==}, on), Equal.sym(Cmd.St, Cmd.walk(q, t, Cmd.Top{}), LA.cb_st(t, q), LA.cb_walk_root(q, t, ok, on)))

# after a walked path q, an empty word changes nothing the walk does
def sp_walk_gap(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, -d: List<&2, List<&2, Nat>>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}) -> {Cmd.walk(List.append(&2, List<&2, Nat>, q, Nil{} <> d), t, Cmd.Top{}) == Cmd.walk(List.append(&2, List<&2, Nat>, q, d), t, Cmd.Top{}) : Cmd.St}:
  %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, q, Nil{} <> d), t, Cmd.Top{}), Cmd.walk(Nil{} <> d, t, Cmd.walk(q, t, Cmd.Top{})), LA.cb_walk_app(q, Nil{} <> d, t, Cmd.Top{})) : {_ == Cmd.walk(List.append(&2, List<&2, Nat>, q, d), t, Cmd.Top{}) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(List.append(&2, List<&2, Nat>, q, d), t, Cmd.Top{}), Cmd.walk(d, t, Cmd.walk(q, t, Cmd.Top{})), LA.cb_walk_app(q, d, t, Cmd.Top{})) : {Cmd.walk(Nil{} <> d, t, Cmd.walk(q, t, Cmd.Top{})) == _ : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.walk(q, t, Cmd.Top{}), LA.cb_st(t, q), LA.cb_walk_root(q, t, ok, on)) : {Cmd.walk(Nil{} <> d, t, _) == Cmd.walk(d, t, _) : Cmd.St}
  %Equal.sym(Cmd.St, Cmd.step.empty(LA.cb_st(t, q)), LA.cb_st(t, q), sp_empty_st(t, q)) : {Cmd.walk(d, t, _) == Cmd.walk(d, t, LA.cb_st(t, q)) : Cmd.St}
  {==}

# Keys
# ----

# the words of the loose line of q and a spaceless last word p
def sp_words_lsi(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +gs: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.words(Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)) == List.append(&2, List<&2, Nat>, sp_lsi(q, gs), [p]) : List<&2, List<&2, Nat>>}:
  +l = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)
  +ls = sp_ls(List.append(&2, List<&2, Nat>, q, [p]), gs)
  %sp_ls_last(q, p, gs) : {Cmd.words(l) == _ : List<&2, List<&2, Nat>>}
  %LA.cb_app_nil(List<&2, Nat>, ls) : {Cmd.words(l) == _ : List<&2, List<&2, Nat>>}
  %LA.cb_app_nil(Nat, l) : {Cmd.words(_) == List.append(&2, List<&2, Nat>, ls, Nil{}) : List<&2, List<&2, Nat>>}
  sp_words_loose_last(q, p, gs, Nil{}, Nil{}, LA.cb_all_spaceless_app(q, [p], LA.cb_names_spaceless(q, LA.cb_walks_names(t, q, ok, on)), LBool.cb_and_intro(Command.cmd_spaceless(p), True{}, word, {==})), {==})

# ... and its cut: the loose words before p, and p
def sp_cut(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +gs: List<&2, Nat>, ok: {Command.cmd_wf(t) == True{} : Bool}, on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.cut(Cmd.words(Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs))) == (sp_lsi(q, gs), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}:
  %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)), List.append(&2, List<&2, Nat>, sp_lsi(q, gs), [p]), sp_words_lsi(t, q, p, gs, ok, on, word)) : {Cmd.cut(_) == (sp_lsi(q, gs), p) : List<&2, List<&2, Nat>> & List<&2, Nat>}
  LA.cb_cut(sp_lsi(q, gs), p)

# the loose line of q p: Tab or Enter answers through the row of the
# selection at q, as on the single-spaced line (LA.kr_key)
def sp_key(+t: List<&2, Cmd.Ent>, +q: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +gs: List<&2, Nat>, sel: Cmd.Sel, k: Cmd.Press, +ok: {Command.cmd_wf(t) == True{} : Bool}, +on: {Command.cmd_walks(t, q) == True{} : Bool}, word: {Command.cmd_spaceless(p) == True{} : Bool}) -> {Cmd.key.row(Cmd.row(sel, t, q), k, t, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs), p) == Cmd.key(t, Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs), sel, k) : Cmd.Out}:
  +l = Command.cmd_loose(List.append(&2, List<&2, Nat>, q, [p]), gs)
  %Equal.sym(List<&2, List<&2, Nat>> & List<&2, Nat>, Cmd.cut(Cmd.words(l)), (sp_lsi(q, gs), p), sp_cut(t, q, p, gs, ok, on, word)) : {Cmd.key.row(Cmd.row(sel, t, q), k, t, l, p) == Cmd.key.cut(_, t, l, sel, k) : Cmd.Out}
  %Equal.sym(Cmd.St, Cmd.walk(sp_lsi(q, gs), t, Cmd.Top{}), Cmd.walk(q, t, Cmd.Top{}), sp_walk_loose(q, gs, t, ok, on)) : {Cmd.key.row(Cmd.row(sel, t, q), k, t, l, p) == Cmd.key.at(_, t, l, p, sel, k) : Cmd.Out}
  LA.kr_walked(q, t, l, p, sel, k, ok, on)
