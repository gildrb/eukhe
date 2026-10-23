# PROOF of LAW command_path_runs_itself: the names of a declared path are
# spaceless names (cmd_wf), so the words of its line are the path
# itself; the walk over them from the root lands on the path with its own
# entry (B.cb_walk_root: every prefix is declared and found by its name,
# never by an alias); finishing there runs it when it has a default or no
# child, else opens its menu, which is cmd_ended (kids.any is
# cmd_has_kid).

import Base
import ../LAWS.bend as Laws
import ../bend/command.bend as Cmd
import ./base.bend as B

def pri_at(b: Bool, -p: List<&2, List<&2, Nat>>) -> {Cmd.finish.at(b, p) == Laws.cmd_ended.at(b, p) : Cmd.Res}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# finishing on the state of p is cmd_ended of p's entry
def pri_end(m: Maybe<&2, Cmd.Ent>, +t: List<&2, Cmd.Ent>, +p: List<&2, List<&2, Nat>>, hf: {B.cb_fits(m, p) == True{} : Bool}) -> {Cmd.finish(B.cb_st.of(m, p), t) == Laws.cmd_ended.of(m, t, p) : Cmd.Res}:
  match m:
    case None{}:
      {==}
    case Some{Cmd.Ent{+q, +a, +r, +f, +g}}:
      %B.cb_path_eq(q, p, hf) : {Cmd.finish.at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p) == Laws.cmd_ended.at(Bool.or(r, Bool.not(Laws.cmd_has_kid(t, _))), p) : Cmd.Res}
      %B.cb_kids_any(t, q) : {Cmd.finish.at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p) == Laws.cmd_ended.at(Bool.or(r, Bool.not(_)), p) : Cmd.Res}
      pri_at(Bool.or(r, Bool.not(Cmd.kids.any(t, q))), p)

def Laws.command_path_runs_itself(t, p, ok, on):
  match p:
    case Nil{}:
      B.cb_absurd({Cmd.resolve(t, Laws.cmd_render(Nil{})) == Laws.cmd_ended(t, Nil{}) : Cmd.Res}, on)
    case Con{+x, +rest}:
      +k = ok
      +o = on
      +hd = B.cb_walks_decl(rest, x, t, Nil{}, o)
      +hs = B.cb_names_spaceless(x <> rest, B.cb_decl_names(t, x <> rest, k, hd))
      %Equal.sym(List<&2, List<&2, Nat>>, Cmd.words(Laws.cmd_render(x <> rest)), x <> rest, B.cb_words_render(x, rest, hs)) : {Cmd.finish(Cmd.walk(_, t, Cmd.Top{}), t) == Laws.cmd_ended(t, x <> rest) : Cmd.Res}
      %Equal.sym(Cmd.St, Cmd.walk(x <> rest, t, Cmd.Top{}), B.cb_st(t, x <> rest), B.cb_walk_root(x <> rest, t, k, o)) : {Cmd.finish(_, t) == Laws.cmd_ended(t, x <> rest) : Cmd.Res}
      pri_end(Laws.cmd_lookup(t, x <> rest), t, x <> rest, B.cb_lookup_fits(t, x <> rest))
