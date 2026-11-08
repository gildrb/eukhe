# eukhe: lemmas of the model_name proofs about M.holds (R7): a row of
# verdicts is one per set (mnh.row_len), appends what follows it
# (mnh.row_app) and splits with its sets (mnh.row_split); a rule or a set
# that holds for a name in a list makes the list hold (mnh.rules_in,
# mnh.set_in), and a list that holds has a member that does (mnh.rules_sp,
# mnh.set_sp).

import Base
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA

# Shape
# -----

# a row is one verdict per set, then what follows it
def mnh.row_len(sets: List<&2, List<&2, M.Rule>>, +g: List<&2, String>, -rest: List<&2, Bool>) -> {List.length(&2, Bool, M.row(sets, g, rest)) == Nat.add(List.length(&2, List<&2, M.Rule>, sets), List.length(&2, Bool, rest)) : Nat}:
  match sets:
    case Nil{}:
      {==}
    case rs <> more:
      Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Bool, M.row(more, g, rest)), Nat.add(List.length(&2, List<&2, M.Rule>, more), List.length(&2, Bool, rest)), mnh.row_len(more, g, rest))

# what follows a row can be appended after it
def mnh.row_app(sets: List<&2, List<&2, M.Rule>>, +g: List<&2, String>, -a: List<&2, Bool>, -b: List<&2, Bool>) -> {List.append(&2, Bool, M.row(sets, g, a), b) == M.row(sets, g, List.append(&2, Bool, a, b)) : List<&2, Bool>}:
  match sets:
    case Nil{}:
      {==}
    case +rs <> more:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => M.set_holds(rs, g) <> z, List.append(&2, Bool, M.row(more, g, a), b), M.row(more, g, List.append(&2, Bool, a, b)), mnh.row_app(more, g, a, b))

# the row of the sets s1 ++ s2 is the row of s1 before the row of s2
def mnh.row_split(s1: List<&2, List<&2, M.Rule>>, -s2: List<&2, List<&2, M.Rule>>, +g: List<&2, String>, -rest: List<&2, Bool>) -> {M.row(List.append(&2, List<&2, M.Rule>, s1, s2), g, rest) == M.row(s1, g, M.row(s2, g, rest)) : List<&2, Bool>}:
  match s1:
    case Nil{}:
      {==}
    case +rs <> more:
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => M.set_holds(rs, g) <> z, M.row(List.append(&2, List<&2, M.Rule>, more, s2), g, rest), M.row(more, g, M.row(s2, g, rest)), mnh.row_split(more, s2, g, rest))

# One set over one group, complete
# --------------------------------

def mnh.rules_in(pre: List<&2, M.Rule>, +r: M.Rule, +post: List<&2, M.Rule>, +s: String, h: {M.rule(r, s) == True{} : Bool}) -> {M.rules(List.append(&2, M.Rule, pre, r <> post), s) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, M.rule(r, s), True{}, h) : {P.pm.or(_, u => M.rules(post, s)) == True{} : Bool}
      {==}
    case +q <> more:
      LA.mnb.or_rl(M.rule(q, s), M.rules(List.append(&2, M.Rule, more, r <> post), s), mnh.rules_in(more, r, post, s, h))

def mnh.set_in(+rs: List<&2, M.Rule>, gp: List<&2, String>, +s: String, +gq: List<&2, String>, h: {M.rules(rs, s) == True{} : Bool}) -> {M.set_holds(rs, List.append(&2, String, gp, s <> gq)) == True{} : Bool}:
  match gp:
    case Nil{}:
      %Equal.sym(Bool, M.rules(rs, s), True{}, h) : {P.pm.or(_, u => M.set_holds(rs, gq)) == True{} : Bool}
      {==}
    case +x <> more:
      LA.mnb.or_rl(M.rules(rs, x), M.set_holds(rs, List.append(&2, String, more, s <> gq)), mnh.set_in(rs, more, s, gq, h))

# One set over one group, sound
# -----------------------------

def mnh.RulesP(rs: List<&2, M.Rule>, s: String, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, M.Rule>, pre => Sigma<&1, &1, M.Rule, r => Sigma<&1, &1, List<&2, M.Rule>, post => {rs == List.append(&2, M.Rule, pre, r <> post) : List<&2, M.Rule>} & {M.rule(r, s) == True{} : Bool}>>>
    case False{}:
      Unit

def mnh.rules_or(+r: M.Rule, +more: List<&2, M.Rule>, -s: String, b1: Bool, e1: {M.rule(r, s) == b1 : Bool}, b2: Bool, v2: mnh.RulesP(more, s, b2)) -> mnh.RulesP(r <> more, s, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      (Nil{}, (r, (more, ({==}, e1))))
    case False{}:
      match b2:
        case True{}:
          (+pre, (+q, (+post, (ea, eb)))) = v2
          (r <> pre, (q, (post, (Equal.cong(List<&2, M.Rule>, List<&2, M.Rule>, z => r <> z, more, List.append(&2, M.Rule, pre, q <> post), ea), eb))))
        case False{}:
          Unit{}

# a set's rules that hold for s: one of them does
def mnh.rules_sp(rs: List<&2, M.Rule>, +s: String) -> mnh.RulesP(rs, s, M.rules(rs, s)):
  match rs:
    case Nil{}:
      Unit{}
    case +r <> +more:
      mnh.rules_or(r, more, s, M.rule(r, s), {==}, M.rules(more, s), mnh.rules_sp(more, s))

def mnh.SetP(rs: List<&2, M.Rule>, g: List<&2, String>, b: Bool) -> Type:
  match b:
    case True{}:
      Sigma<&1, &1, List<&2, String>, gp => Sigma<&1, &1, String, s => Sigma<&1, &1, List<&2, String>, gq => {g == List.append(&2, String, gp, s <> gq) : List<&2, String>} & mnh.RulesP(rs, s, True{})>>>
    case False{}:
      Unit

def mnh.set_or(+s: String, +more: List<&2, String>, -rs: List<&2, M.Rule>, b1: Bool, v1: mnh.RulesP(rs, s, b1), b2: Bool, v2: mnh.SetP(rs, more, b2)) -> mnh.SetP(rs, s <> more, P.pm.or(b1, u => b2)):
  match b1:
    case True{}:
      (Nil{}, (s, (more, ({==}, v1))))
    case False{}:
      match b2:
        case True{}:
          (+gp, (+x, (+gq, (e, v)))) = v2
          (s <> gp, (x, (gq, (LA.mnb.lcons_eq(s, more, List.append(&2, String, gp, x <> gq), e), v))))
        case False{}:
          Unit{}

# a set that holds for a group: one of its rules holds for one of its names
def mnh.set_sp(+rs: List<&2, M.Rule>, g: List<&2, String>) -> mnh.SetP(rs, g, M.set_holds(rs, g)):
  match g:
    case Nil{}:
      Unit{}
    case +s <> +more:
      mnh.set_or(s, more, rs, M.rules(rs, s), mnh.rules_sp(rs, s), M.set_holds(rs, more), mnh.set_sp(rs, more))

def mnh.set_cast(-rs: List<&2, M.Rule>, -g: List<&2, String>, b: Bool, e: {b == True{} : Bool}, v: mnh.SetP(rs, g, b)) -> mnh.SetP(rs, g, True{}):
  %e : mnh.SetP(rs, g, _)
  v

# the first verdict of a list (False for none)
def mnh.head(l: List<&2, Bool>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case x <> t:
      x
