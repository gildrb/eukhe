# eukhe: the proof of LAW slash_args_goal_budget_spaced
#
# PROOF: the text is its own trim (its ends: LA.sab.ld_app), no keyword;
# its first piece is the flag (LA.sab.cut_pre, LA.sab.cut_white); after
# the White_Space the value is the next piece (LA.sab.ts_blank,
# LA.sab.ts_dark, LA.sab.cut_pre), and the objective after the one
# White_Space char that ends it trims to o.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sbs.at_v(+v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}) -> {Ga.space(v0) == False{} : Bool}:
  LA.sab.sp_f(v0, LA.sab.not_t(SlashArgs.sa_white(v0), LStg.stg.and_l(Bool.not(SlashArgs.sa_white(v0)), SlashArgs.sa_solid(vs), vd)))

def sbs.edge(+c: Char, +w: String, +v0: Char, +vs: String, +d: Char, +x: String, o: String, +oe: {SlashArgs.sa_edge(o) == True{} : Bool}) -> {SlashArgs.sa_last_dark(String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)})), c) == True{} : Bool}:
  match o:
    case SNil{}:
      LStg.stg.absurdF({SlashArgs.sa_last_dark(String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, SNil{})})), c) == True{} : Bool}, oe)
    case SCon{+o0, +os}:
      +y = String.append(x, SCon{o0, os})
      +l2 = SlashArgs.sa_last_dark(String.append(vs, SCon{d, y}), v0)
      +l3 = SlashArgs.sa_last_dark(y, d)
      Equal.trans(Bool, SlashArgs.sa_last_dark(String.append(w, SCon{v0, String.append(vs, SCon{d, y})}), c), l2, True{}, LA.sab.ld_app(w, c, v0, String.append(vs, SCon{d, y})), Equal.trans(Bool, l2, l3, True{}, LA.sab.ld_app(vs, v0, d, y), Equal.trans(Bool, l3, SlashArgs.sa_last_dark(os, o0), True{}, LA.sab.ld_app(x, d, o0, os), LStg.stg.and_r(Bool.not(SlashArgs.sa_white(o0)), SlashArgs.sa_last_dark(os, o0), oe))))

def sbs.edge3(+c: Char, +w: String, +v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}) -> {SlashArgs.sa_last_dark(String.append(w, SCon{v0, vs}), c) == True{} : Bool}:
  Equal.trans(Bool, SlashArgs.sa_last_dark(String.append(w, SCon{v0, vs}), c), SlashArgs.sa_last_dark(vs, v0), True{}, LA.sab.ld_app(w, c, v0, vs), LA.sab.ld_solid(vs, v0, LStg.stg.and_r(Bool.not(SlashArgs.sa_white(v0)), SlashArgs.sa_solid(vs), vd), LStg.stg.and_l(Bool.not(SlashArgs.sa_white(v0)), SlashArgs.sa_solid(vs), vd)))

# after the flag: White_Space, then v: the value v first
def sbs.ts(+c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +w: String, +wb: {SlashArgs.sa_blank(w) == True{} : Bool}, +v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}, +r: String) -> {Sa.trim_start(SCon{c, String.append(w, String.append(SCon{v0, vs}, r))}) == SCon{v0, String.append(vs, r)} : String}:
  Equal.trans(String, Sa.trim_start(String.append(SCon{c, w}, SCon{v0, String.append(vs, r)})), Sa.trim_start(SCon{v0, String.append(vs, r)}), SCon{v0, String.append(vs, r)}, LA.sab.ts_blank(SCon{c, w}, SCon{v0, String.append(vs, r)}, LA.sab.blank_cons(c, w, cw, wb)), LA.sab.ts_dark(v0, String.append(vs, r), sbs.at_v(v0, vs, vd)))

def sbs.one(+fe: String, +fes: {SlashArgs.sa_solid(fe) == True{} : Bool}, +c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +w: String, +wb: {SlashArgs.sa_blank(w) == True{} : Bool}, +v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}, +d: Char, +dw: {SlashArgs.sa_white(d) == True{} : Bool}, +x: String, +xb: {SlashArgs.sa_blank(x) == True{} : Bool}, +o: String, +oe: {SlashArgs.sa_edge(o) == True{} : Bool}, ee: {SlashArgs.sa_edge(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == True{} : Bool}, ek: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}))) == False{} : Bool}, ef: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{SNil{}, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}}), String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == Sa.goal.spaced(Sa.cut(Sa.trim_start(SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}))) : Sa.Goal}) -> {Sa.goal(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == SlashArgs.sa_budget(SCon{v0, vs}, o) : Sa.Goal}:
  +y = String.append(x, o)
  +vv = {SCon{v0, vs} : String}
  +z = String.append(vv, SCon{d, y})
  +rest = {SCon{c, String.append(w, z)} : String}
  +t = String.append(fe, rest)
  +cp = LA.sab.cpre(fe, Sa.Cut{SNil{}, rest})
  +ct = Equal.trans(Sa.Cut, Sa.cut(t), LA.sab.cpre(fe, Sa.cut(rest)), cp, LA.sab.cut_pre(fe, rest, fes), Equal.cong(Sa.Cut, Sa.Cut, q => LA.sab.cpre(fe, q), Sa.cut(rest), Sa.Cut{SNil{}, rest}, LA.sab.cut_white(c, String.append(w, z), cw)))
  +cz = Equal.trans(Sa.Cut, Sa.cut(z), LA.sab.cpre(vv, Sa.cut(SCon{d, y})), Sa.Cut{vv, SCon{d, y}}, LA.sab.cut_pre(vv, SCon{d, y}, vd), Equal.trans(Sa.Cut, LA.sab.cpre(vv, Sa.cut(SCon{d, y})), LA.sab.cpre(vv, Sa.Cut{SNil{}, SCon{d, y}}), Sa.Cut{vv, SCon{d, y}}, Equal.cong(Sa.Cut, Sa.Cut, q => LA.sab.cpre(vv, q), Sa.cut(SCon{d, y}), Sa.Cut{SNil{}, SCon{d, y}}, LA.sab.cut_white(d, y, dw)), LA.sab.cpre_nil(vv, SCon{d, y})))
  +sp = Equal.trans(Sa.Cut, Sa.cut(Sa.trim_start(rest)), Sa.cut(z), Sa.Cut{vv, SCon{d, y}}, Equal.cong(String, Sa.Cut, q => Sa.cut(q), Sa.trim_start(rest), z, sbs.ts(c, cw, w, wb, v0, vs, vd, SCon{d, y})), cz)
  +et = Equal.trans(String, Sa.trim(y), Sa.trim(o), o, LA.sab.trim_left(x, xb, o), LA.sab.trim_edge(o, oe))
  Equal.trans(Sa.Goal, Sa.goal(t), Sa.goal.start(Sa.cut(t), t), SlashArgs.sa_budget(vv, o), LA.sab.goal_plain(t, ee, ek), Equal.trans(Sa.Goal, Sa.goal.start(Sa.cut(t), t), Sa.goal.start(cp, t), SlashArgs.sa_budget(vv, o), Equal.cong(Sa.Cut, Sa.Goal, q => Sa.goal.start(q, t), Sa.cut(t), cp, ct), Equal.trans(Sa.Goal, Sa.goal.start(cp, t), Sa.goal.spaced(Sa.cut(Sa.trim_start(rest))), SlashArgs.sa_budget(vv, o), ef, Equal.trans(Sa.Goal, Sa.goal.spaced(Sa.cut(Sa.trim_start(rest))), Sa.goal.spaced(Sa.Cut{vv, SCon{d, y}}), SlashArgs.sa_budget(vv, o), Equal.cong(Sa.Cut, Sa.Goal, q => Sa.goal.spaced(q), Sa.cut(Sa.trim_start(rest)), Sa.Cut{vv, SCon{d, y}}, sp), LA.sab.budget.at(Sa.u64(vv), vv, y, o, oe, et)))))

def sbs.three(+fe: String, +fes: {SlashArgs.sa_solid(fe) == True{} : Bool}, +c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +w: String, +wb: {SlashArgs.sa_blank(w) == True{} : Bool}, +v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}, ee: {SlashArgs.sa_edge(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == True{} : Bool}, ek: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})}))) == False{} : Bool}, ef: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{SNil{}, SCon{c, String.append(w, SCon{v0, vs})}}), String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == Sa.goal.spaced(Sa.cut(Sa.trim_start(SCon{c, String.append(w, SCon{v0, vs})}))) : Sa.Goal}) -> {Sa.goal(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal}:
  +vv = {SCon{v0, vs} : String}
  +rest = {SCon{c, String.append(w, vv)} : String}
  +t = String.append(fe, rest)
  +cp = LA.sab.cpre(fe, Sa.Cut{SNil{}, rest})
  +ct = Equal.trans(Sa.Cut, Sa.cut(t), LA.sab.cpre(fe, Sa.cut(rest)), cp, LA.sab.cut_pre(fe, rest, fes), Equal.cong(Sa.Cut, Sa.Cut, q => LA.sab.cpre(fe, q), Sa.cut(rest), Sa.Cut{SNil{}, rest}, LA.sab.cut_white(c, String.append(w, vv), cw)))
  +tv = Equal.trans(String, Sa.trim_start(String.append(SCon{c, w}, vv)), Sa.trim_start(vv), vv, LA.sab.ts_blank(SCon{c, w}, vv, LA.sab.blank_cons(c, w, cw, wb)), LA.sab.ts_dark(v0, vs, sbs.at_v(v0, vs, vd)))
  +sp = Equal.trans(Sa.Cut, Sa.cut(Sa.trim_start(rest)), Sa.cut(vv), Sa.Cut{vv, SNil{}}, Equal.cong(String, Sa.Cut, q => Sa.cut(q), Sa.trim_start(rest), vv, tv), LA.sab.cut_all(vv, vd))
  +u = {Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal}
  Equal.trans(Sa.Goal, Sa.goal(t), Sa.goal.start(Sa.cut(t), t), u, LA.sab.goal_plain(t, ee, ek), Equal.trans(Sa.Goal, Sa.goal.start(Sa.cut(t), t), Sa.goal.start(cp, t), u, Equal.cong(Sa.Cut, Sa.Goal, q => Sa.goal.start(q, t), Sa.cut(t), cp, ct), Equal.trans(Sa.Goal, Sa.goal.start(cp, t), Sa.goal.spaced(Sa.cut(Sa.trim_start(rest))), u, ef, Equal.cong(Sa.Cut, Sa.Goal, q => Sa.goal.spaced(q), Sa.cut(Sa.trim_start(rest)), Sa.Cut{vv, SNil{}}, sp))))

def sbs.all(+fe: String, +fes: {SlashArgs.sa_solid(fe) == True{} : Bool}, +c: Char, +cw: {SlashArgs.sa_white(c) == True{} : Bool}, +w: String, +wb: {SlashArgs.sa_blank(w) == True{} : Bool}, +v0: Char, +vs: String, +vd: {SlashArgs.sa_solid(SCon{v0, vs}) == True{} : Bool}, +d: Char, +dw: {SlashArgs.sa_white(d) == True{} : Bool}, +x: String, +xb: {SlashArgs.sa_blank(x) == True{} : Bool}, +o: String, +oe: {SlashArgs.sa_edge(o) == True{} : Bool}, ee1: {SlashArgs.sa_edge(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == True{} : Bool}, ek1: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}))) == False{} : Bool}, ef1: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{SNil{}, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}}), String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == Sa.goal.spaced(Sa.cut(Sa.trim_start(SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))}))) : Sa.Goal}, ee3: {SlashArgs.sa_edge(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == True{} : Bool}, ek3: {SlashArgs.sa_keyword(String.to_lower(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})}))) == False{} : Bool}, ef3: {Sa.goal.start(LA.sab.cpre(fe, Sa.Cut{SNil{}, SCon{c, String.append(w, SCon{v0, vs})}}), String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == Sa.goal.spaced(Sa.cut(Sa.trim_start(SCon{c, String.append(w, SCon{v0, vs})}))) : Sa.Goal}, e2: {Sa.goal(fe) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal}) -> {Sa.goal(String.append(fe, SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == SlashArgs.sa_budget(SCon{v0, vs}, o) : Sa.Goal} & {Sa.goal(fe) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal} & {Sa.goal(String.append(fe, SCon{c, String.append(w, SCon{v0, vs})})) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal}:
  (sbs.one(fe, fes, c, cw, w, wb, v0, vs, vd, d, dw, x, xb, o, oe, ee1, ek1, ef1), e2, sbs.three(fe, fes, c, cw, w, wb, v0, vs, vd, ee3, ek3, ef3))

def SlashArgs.slash_args_goal_budget_spaced(k, c, cw, w, wb, v0, vs, vd, d, dw, x, xb, o, oe):
  match k:
    case True{}:
      sbs.all("--budget", {==}, c, cw, w, wb, v0, vs, vd, d, dw, x, xb, o, oe, sbs.edge(c, w, v0, vs, d, x, o, oe), {==}, {==}, sbs.edge3(c, w, v0, vs, vd), {==}, {==}, {==})
    case False{}:
      sbs.all("--token-budget", {==}, c, cw, w, wb, v0, vs, vd, d, dw, x, xb, o, oe, sbs.edge(c, w, v0, vs, d, x, o, oe), {==}, {==}, sbs.edge3(c, w, v0, vs, vd), {==}, {==}, {==})
