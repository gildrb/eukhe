# eukhe: the proof of LAW slash_args_goal_budget_eq
#
# PROOF: the text is its own trim (its ends: LA.sab.ld_app), no keyword;
# its first piece is `F=v` (LA.sab.cut_pre, LA.sab.cut_white), whose
# value after the `=` is v; the objective after the White_Space trims to o
# (LA.sab.trim_left, LA.sab.trim_edge).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sbe.edge(+v: String, +c: Char, +w: String, o: String, +oe: {SlashArgs.sa_edge(o) == True{} : Bool}) -> {SlashArgs.sa_last_dark(String.append(v, SCon{c, String.append(w, o)}), '=') == True{} : Bool}:
  match o:
    case SNil{}:
      LStg.stg.absurdF({SlashArgs.sa_last_dark(String.append(v, SCon{c, String.append(w, SNil{})}), '=') == True{} : Bool}, oe)
    case SCon{+o0, +os}:
      +l2 = SlashArgs.sa_last_dark(String.append(w, SCon{o0, os}), c)
      Equal.trans(Bool, SlashArgs.sa_last_dark(String.append(v, SCon{c, String.append(w, SCon{o0, os})}), '='), l2, True{}, LA.sab.ld_app(v, '=', c, String.append(w, SCon{o0, os})), Equal.trans(Bool, l2, SlashArgs.sa_last_dark(os, o0), True{}, LA.sab.ld_app(w, c, o0, os), LStg.stg.and_r(Bool.not(SlashArgs.sa_white(o0)), SlashArgs.sa_last_dark(os, o0), oe)))

def sbe.one(+fe: String, +fes: {SlashArgs.sa_solid(fe) == True{} : Bool}, +v: String, +vs: {SlashArgs.sa_solid(v) == True{} : Bool}, +c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +w: String, +wb: {SlashArgs.sa_blank(w) == True{} : Bool}, +o: String, +oe: {SlashArgs.sa_edge(o) == True{} : Bool}, ee: {SlashArgs.sa_edge(String.append(fe, String.append(v, SCon{c, String.append(w, o)}))) == True{} : Bool}, ek: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, String.append(v, SCon{c, String.append(w, o)})))) == False{} : Bool}, ef: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{v, SCon{c, String.append(w, o)}}), String.append(fe, String.append(v, SCon{c, String.append(w, o)}))) == Sa.goal.budget(Sa.u64(v), v, SCon{c, String.append(w, o)}) : Sa.Goal}) -> {Sa.goal(String.append(fe, String.append(v, SCon{c, String.append(w, o)}))) == SlashArgs.sa_budget(v, o) : Sa.Goal}:
  +y = String.append(w, o)
  +x = String.append(v, SCon{c, y})
  +t = String.append(fe, x)
  +cp = LA.sab.cpre(fe, Sa.Cut{v, SCon{c, y}})
  +cx = Equal.trans(Sa.Cut, Sa.cut(x), LA.sab.cpre(v, Sa.cut(SCon{c, y})), Sa.Cut{v, SCon{c, y}}, LA.sab.cut_pre(v, SCon{c, y}, vs), Equal.trans(Sa.Cut, LA.sab.cpre(v, Sa.cut(SCon{c, y})), LA.sab.cpre(v, Sa.Cut{SNil{}, SCon{c, y}}), Sa.Cut{v, SCon{c, y}}, Equal.cong(Sa.Cut, Sa.Cut, z => LA.sab.cpre(v, z), Sa.cut(SCon{c, y}), Sa.Cut{SNil{}, SCon{c, y}}, LA.sab.cut_white(c, y, cw)), LA.sab.cpre_nil(v, SCon{c, y})))
  +ct = Equal.trans(Sa.Cut, Sa.cut(t), LA.sab.cpre(fe, Sa.cut(x)), cp, LA.sab.cut_pre(fe, x, fes), Equal.cong(Sa.Cut, Sa.Cut, z => LA.sab.cpre(fe, z), Sa.cut(x), Sa.Cut{v, SCon{c, y}}, cx))
  +et = Equal.trans(String, Sa.trim(SCon{c, y}), Sa.trim(o), o, LA.sab.trim_left(SCon{c, w}, LA.sab.blank_cons(c, w, cw, wb), o), LA.sab.trim_edge(o, oe))
  Equal.trans(Sa.Goal, Sa.goal(t), Sa.goal.start(Sa.cut(t), t), SlashArgs.sa_budget(v, o), LA.sab.goal_plain(t, ee, ek), Equal.trans(Sa.Goal, Sa.goal.start(Sa.cut(t), t), Sa.goal.start(cp, t), SlashArgs.sa_budget(v, o), Equal.cong(Sa.Cut, Sa.Goal, z => Sa.goal.start(z, t), Sa.cut(t), cp, ct), Equal.trans(Sa.Goal, Sa.goal.start(cp, t), Sa.goal.budget(Sa.u64(v), v, SCon{c, y}), SlashArgs.sa_budget(v, o), ef, LA.sab.budget.at(Sa.u64(v), v, SCon{c, y}, o, oe, et))))

def sbe.two(+fe: String, +fes: {SlashArgs.sa_solid(fe) == True{} : Bool}, +v: String, +vs: {SlashArgs.sa_solid(v) == True{} : Bool}, ee: {SlashArgs.sa_edge(String.append(fe, v)) == True{} : Bool}, ek: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, v))) == False{} : Bool}, ef: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{v, SNil{}}), String.append(fe, v)) == Sa.goal.budget(Sa.u64(v), v, SNil{}) : Sa.Goal}) -> {Sa.goal(String.append(fe, v)) == SlashArgs.sa_budget_none(Sa.u64(v)) : Sa.Goal}:
  +t = String.append(fe, v)
  +cp = LA.sab.cpre(fe, Sa.Cut{v, SNil{}})
  +ct = Equal.trans(Sa.Cut, Sa.cut(t), LA.sab.cpre(fe, Sa.cut(v)), cp, LA.sab.cut_pre(fe, v, fes), Equal.cong(Sa.Cut, Sa.Cut, z => LA.sab.cpre(fe, z), Sa.cut(v), Sa.Cut{v, SNil{}}, LA.sab.cut_all(v, vs)))
  Equal.trans(Sa.Goal, Sa.goal(t), Sa.goal.start(Sa.cut(t), t), SlashArgs.sa_budget_none(Sa.u64(v)), LA.sab.goal_plain(t, ee, ek), Equal.trans(Sa.Goal, Sa.goal.start(Sa.cut(t), t), Sa.goal.start(cp, t), SlashArgs.sa_budget_none(Sa.u64(v)), Equal.cong(Sa.Cut, Sa.Goal, z => Sa.goal.start(z, t), Sa.cut(t), cp, ct), Equal.trans(Sa.Goal, Sa.goal.start(cp, t), Sa.goal.budget(Sa.u64(v), v, SNil{}), SlashArgs.sa_budget_none(Sa.u64(v)), ef, LA.sab.budget_none(Sa.u64(v), v))))

def SlashArgs.slash_args_goal_budget_eq(k, v, vs, c, cw, w, wb, o, oe):
  match k:
    case True{}:
      (sbe.one("--budget=", {==}, v, vs, c, cw, w, wb, o, oe, sbe.edge(v, c, w, o, oe), {==}, {==}), sbe.two("--budget=", {==}, v, vs, LA.sab.ld_solid(v, '=', vs, {==}), {==}, {==}))
    case False{}:
      (sbe.one("--token-budget=", {==}, v, vs, c, cw, w, wb, o, oe, sbe.edge(v, c, w, o, oe), {==}, {==}), sbe.two("--token-budget=", {==}, v, vs, LA.sab.ld_solid(v, '=', vs, {==}), {==}, {==}))
