# eukhe: the trim lemmas of LAW dash_stored_spec
#
# The code trims the start, reverses, trims the start again and reverses
# back; the spec strips the start (sp_lstrip), then the end (sp_rstrip).
# Trimming the start of X reversed onto acc trims the end of X: what is
# left of X once its trailing whitespace is gone comes back reversed
# onto acc, or, when nothing of X is left, acc is trimmed (tm.go). The
# whitespace test is the spec's (space.bend).

import Base
import ../../../bend/dash.bend as Da
import ../../../laws/dash.bend as Dash
import ../../base/string.bend as LString
import ../../base/logic/string.bend as LLogicString
import ./space.bend as LSpace

# The start
# ---------

def tm.if(b: Bool, -c: Char, -t: String, -r: String) -> {Da.trim_start.if(b, c, t, r) == Dash.sp_rstrip.if(Bool.not(b), c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's trimmed start is the spec's
def tm.lstrip(s: String) -> {Da.trim_start(s) == Dash.sp_lstrip(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Da.space(c), Dash.sp_space(c), LSpace.sw.space(c)) : {Da.trim_start.if(_, c, t, Da.trim_start(t)) == Dash.sp_rstrip.if(Bool.not(Dash.sp_space(c)), c, t, Dash.sp_lstrip(t)) : String}
      %Equal.sym(String, Da.trim_start(t), Dash.sp_lstrip(t), tm.lstrip(t)) : {Da.trim_start.if(Dash.sp_space(c), c, t, _) == Dash.sp_rstrip.if(Bool.not(Dash.sp_space(c)), c, t, Dash.sp_lstrip(t)) : String}
      tm.if(Dash.sp_space(c), c, t, Dash.sp_lstrip(t))

# The end
# -------

# what is left of X without its trailing whitespace (r), reversed onto
# acc; acc trimmed when nothing is left
def tm.pick(r: String, acc: String) -> String:
  match r:
    case SNil{}:
      Da.trim_start(acc)
    case SCon{x, y}:
      String.reverse.go(SCon{x, y}, acc)

def tm.nil(b: Bool, +c: Char, +acc: String) -> {Da.trim_start.if(b, c, acc, Da.trim_start(acc)) == tm.pick(Dash.sp_rstrip.if(Bool.not(Bool.and(b, True{})), c, SNil{}, SNil{}), acc) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tm.cons(b: Bool, -c: Char, -x: Char, -y: String, -acc: String) -> {tm.pick(SCon{x, y}, SCon{c, acc}) == tm.pick(Dash.sp_rstrip.if(Bool.not(Bool.and(b, False{})), c, SCon{x, y}, SNil{}), acc) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tm.step(rt: String, +c: Char, +acc: String) -> {tm.pick(rt, SCon{c, acc}) == tm.pick(Dash.sp_rstrip.if(Bool.not(Bool.and(Dash.sp_space(c), String.is_empty(rt))), c, rt, SNil{}), acc) : String}:
  match rt:
    case SNil{}:
      %Equal.sym(Bool, Da.space(c), Dash.sp_space(c), LSpace.sw.space(c)) : {Da.trim_start.if(_, c, acc, Da.trim_start(acc)) == tm.pick(Dash.sp_rstrip.if(Bool.not(Bool.and(Dash.sp_space(c), True{})), c, SNil{}, SNil{}), acc) : String}
      tm.nil(Dash.sp_space(c), c, acc)
    case SCon{x, y}:
      tm.cons(Dash.sp_space(c), c, x, y, acc)

# trimming the start of X reversed onto acc
def tm.go(X: String, +acc: String) -> {Da.trim_start(String.reverse.go(X, acc)) == tm.pick(Dash.sp_rstrip(X), acc) : String}:
  match X:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(String, Da.trim_start(String.reverse.go(t, SCon{c, acc})), tm.pick(Dash.sp_rstrip(t), SCon{c, acc}), tm.pick(Dash.sp_rstrip(SCon{c, t}), acc),
        tm.go(t, SCon{c, acc}), tm.step(Dash.sp_rstrip(t), c, acc))

def tm.app_nil(a: String) -> {LLogicString.wr_app(a, SNil{}) == a : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      Equal.cong(String, String, z => SCon{c, z}, LLogicString.wr_app(t, SNil{}), t, tm.app_nil(t))

def tm.back(r: String) -> {String.reverse.go(tm.pick(r, SNil{}), SNil{}) == r : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{+x, +y}:
      Equal.trans(String, String.reverse.go(String.reverse.go(SCon{x, y}, SNil{}), SNil{}), LLogicString.wr_app(SCon{x, y}, SNil{}), SCon{x, y},
        LString.wr_rev_rev(SCon{x, y}, SNil{}, SNil{}), tm.app_nil(SCon{x, y}))

# the code's trim is the spec's
def tm.trim(+s: String) -> {Da.trim(s) == Dash.sp_rstrip(Dash.sp_lstrip(s)) : String}:
  +L = Da.trim_start(s)
  Equal.trans(String, Da.trim(s), String.reverse.go(tm.pick(Dash.sp_rstrip(L), SNil{}), SNil{}), Dash.sp_rstrip(Dash.sp_lstrip(s)),
    Equal.cong(String, String, z => String.reverse.go(z, SNil{}), Da.trim_start(String.reverse.go(L, SNil{})), tm.pick(Dash.sp_rstrip(L), SNil{}), tm.go(L, SNil{})),
    Equal.trans(String, String.reverse.go(tm.pick(Dash.sp_rstrip(L), SNil{}), SNil{}), Dash.sp_rstrip(L), Dash.sp_rstrip(Dash.sp_lstrip(s)),
      tm.back(Dash.sp_rstrip(L)),
      Equal.cong(String, String, z => Dash.sp_rstrip(z), L, Dash.sp_lstrip(s), tm.lstrip(s))))
