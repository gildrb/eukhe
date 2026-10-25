# eukhe: the proof of LAW command_path_runs_itself
#
# PROOF of LAW command_path_runs_itself: the names of a declared path are
# spaceless names (cmd_wf), so the words of its line are the path
# itself; the walk over them from the root lands on the path with its own
# entry (B.cb_walk_root: every prefix is declared and found by its name,
# never by an alias); finishing there runs it when it has a default or no
# child, else opens its menu, which is cmd_ended (kids.any is
# cmd_has_kid).

import Base
import ../../bend/command.bend as Cmd
import ../../laws/command/paths.bend as Command
import ../base/list.bend as LList
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LA

def pri_at(b: Bool, -p: List<&2, List<&2, Nat>>) -> {Cmd.finish.at(b, p) == Command.cmd_ended.at(b, p) : Cmd.Res}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# finishing on the state of p is cmd_ended of p's entry
def pri_end(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, hf: {LA.cb_fits(m, p) == True{} : Bool}) -> {Cmd.finish(LA.cb_st.of(m, p), t) == Command.cmd_ended.of(m, t, p) : Cmd.Res}:
  match m:
    case None{}:
      {==}
    case Some{Cmd.Ent{+q, +a, +r, +f, +g}}:
      %LLogicNat.cb_path_eq(q, p, hf) : {Cmd.finish.at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p) == Command.cmd_ended.at(Bool.or(r, Bool.not(Command.cmd_has_kid(t, _))), p) : Cmd.Res}
      %LA.cb_kids_any(t, q) : {Cmd.finish.at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p) == Command.cmd_ended.at(Bool.or(r, Bool.not(_)), p) : Cmd.Res}
      pri_at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p)

def Command.command_path_runs_itself(t, p, ok, on):
  match p:
    case Nil{}:
      LLogicLogic.cb_absurd({Cmd.resolve(t, Command.cmd_render(Nil{})) == Command.cmd_ended(t, Nil{}) : Cmd.Res}, on)
    case Con{+x, +rest}:
      +k = ok
      +o = on
      +hd = LList.cb_walks_decl(rest, x, t, Nil{}, o)
      +hs = LA.cb_names_spaceless(x <> rest, LA.cb_decl_names(t, x <> rest, k, hd))
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Command.cmd_render(x <> rest)), x <> rest, LA.cb_words_render(x, rest, hs)) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Command.cmd_ended(t, x <> rest) : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(x <> rest, t, Cmd.Top{}), LA.cb_st(t, x <> rest), LA.cb_walk_root(x <> rest, t, k, o)) : {Cmd.finish(_, t) == Command.cmd_ended(t, x <> rest) : Cmd.Res}
      pri_end(Command.cmd_lookup(t, x <> rest), t, x <> rest, LA.cb_lookup_fits(t, x <> rest))
