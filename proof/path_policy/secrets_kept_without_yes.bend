# eukhe: the proof of LAW secrets_kept_without_yes

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./secrets_need_yes.bend as PSecretsNeedYes

# the first write of writes without a yes has no yes
def pp.no_yes_head(ans: Pp.Ans, +segs: List<&2, Tl.Seg>, +v: Nat, +rest: List<&2, Pp.Put>, no: {PathPolicy.pp_no_yes(Pp.Put{segs, v, ans} <> rest) == True{} : Bool}) -> {Pp.Ans.yes(ans) == False{} : Bool}:
  match ans:
    case Pp.Yes{}:
      LA.pp.absurdF({True{} == False{} : Bool}, no)
    case Pp.No{}:
      {==}
    case Pp.Gone{}:
      {==}

# and the writes after it have none
def pp.no_yes_rest(ans: Pp.Ans, +segs: List<&2, Tl.Seg>, +v: Nat, +rest: List<&2, Pp.Put>, no: {PathPolicy.pp_no_yes(Pp.Put{segs, v, ans} <> rest) == True{} : Bool}) -> {PathPolicy.pp_no_yes(rest) == True{} : Bool}:
  match ans:
    case Pp.Yes{}:
      LA.pp.absurdF({PathPolicy.pp_no_yes(rest) == True{} : Bool}, no)
    case Pp.No{}:
      no
    case Pp.Gone{}:
      no

# a location no secret entry covers is not the secret location at
def pp.not_same(b: Bool, +se: List<&2, List<&2, Nat>>, +k: List<&2, Nat>, +at: List<&2, Nat>, e: {PathPolicy.pp_same(k, at) == b : Bool}, hk: {PathPolicy.pp_under_any(se, k) == False{} : Bool}, sec: {PathPolicy.pp_under_any(se, at) == True{} : Bool}) -> {PathPolicy.pp_same(k, at) == False{} : Bool}:
  match b:
    case True{}:
      +same = PSecretsNeedYes.pp.ids_sound(k, at, Equal.trans(Bool, Tl.ids.eq(k, at), PathPolicy.pp_same(k, at), True{}, LA.pp.ids_same(k, at), e))
      +moved = Equal.cong(List<&2, Nat>, Bool, x => PathPolicy.pp_under_any(se, x), k, at, same)
      LA.pp.absurdF({PathPolicy.pp_same(k, at) == False{} : Bool}, Equal.trans(Bool, False{}, PathPolicy.pp_under_any(se, at), True{}, Equal.trans(Bool, False{}, PathPolicy.pp_under_any(se, k), PathPolicy.pp_under_any(se, at), Equal.sym(Bool, PathPolicy.pp_under_any(se, k), False{}, hk), moved), sec))
    case False{}:
      e

# one cell of a set at k, by the head test b
def pp.cell_set_pick(b: Bool, +a: List<&2, Nat>, +w: Nat, +rest: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, +at: List<&2, Nat>, e: {Tl.ids.eq(a, k) == b : Bool}, +hk: {PathPolicy.pp_same(k, at) == False{} : Bool}, ih: {PathPolicy.pp_cell(Pp.set(rest, k, v), at) == PathPolicy.pp_cell(rest, at) : Maybe<&2, Nat>}) -> {PathPolicy.pp_cell(Pp.set.pick(b, Pp.Cell{a, w}, k, v, rest, Pp.set(rest, k, v)), at) == PathPolicy.pp_cell(Pp.Cell{a, w} <> rest, at) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +same = PSecretsNeedYes.pp.ids_sound(a, k, e)
      %Equal.sym(List<&2, Nat>, a, k, same) : {PathPolicy.pp_cell_pick(PathPolicy.pp_same(k, at), v, PathPolicy.pp_cell(rest, at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(_, at), w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell_pick(_, v, PathPolicy.pp_cell(rest, at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(k, at), w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell(rest, at) == PathPolicy.pp_cell_pick(_, w, PathPolicy.pp_cell(rest, at)) : Maybe<&2, Nat>}
      {==}
    case False{}:
      %ih : {PathPolicy.pp_cell_pick(PathPolicy.pp_same(a, at), w, PathPolicy.pp_cell(Pp.set(rest, k, v), at)) == PathPolicy.pp_cell_pick(PathPolicy.pp_same(a, at), w, _) : Maybe<&2, Nat>}
      {==}

# a write at a location that is not at keeps the content at at
def pp.cell_set(cs: List<&2, Pp.Cell>, +k: List<&2, Nat>, +v: Nat, +at: List<&2, Nat>, +hk: {PathPolicy.pp_same(k, at) == False{} : Bool}) -> {PathPolicy.pp_cell(Pp.set(cs, k, v), at) == PathPolicy.pp_cell(cs, at) : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      %Equal.sym(Bool, PathPolicy.pp_same(k, at), False{}, hk) : {PathPolicy.pp_cell_pick(_, v, None{}) == None{} : Maybe<&2, Nat>}
      {==}
    case c <> +rest:
      match c:
        case Pp.Cell{+a, +w}:
          pp.cell_set_pick(Tl.ids.eq(a, k), a, w, rest, k, v, at, {==}, hk, pp.cell_set(rest, k, v, at, hk))

# one write without a yes, by the gate's verdict b, keeps the content at a
# secret location
def pp.put_keeps(b: Bool, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, +segs: List<&2, Tl.Seg>, +v: Nat, +ans: Pp.Ans, +at: List<&2, Nat>, e: {Pp.runs(Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.Wr{}, auto, ans) == b : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}, sec: {PathPolicy.pp_under_any(se, at) == True{} : Bool}) -> {PathPolicy.pp_cell(Pp.put.pick(b, cs, Pp.Res.at(Pp.real(ls, segs)), v), at) == PathPolicy.pp_cell(cs, at) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +k = Pp.Res.at(Pp.real(ls, segs))
      +plain = LA.pp.gate_write_auto_never_secret(Pp.class(Pp.Pol{ro, ru, se}, ls, segs), auto, ans, e, no)
      +plain_at = PSecretsNeedYes.pp.res_secret(Pp.Pol{ro, ru, se}, Pp.real(ls, segs), plain)
      +hk = Equal.trans(Bool, PathPolicy.pp_under_any(se, k), Pp.Cls.secret(Pp.class_of(Pp.Pol{ro, ru, se}, k)), False{}, Equal.sym(Bool, Pp.Cls.secret(Pp.class_of(Pp.Pol{ro, ru, se}, k)), PathPolicy.pp_under_any(se, k), LA.pp.class_of_secret(ro, ru, se, k)), plain_at)
      pp.cell_set(cs, k, v, at, pp.not_same(PathPolicy.pp_same(k, at), se, k, at, {==}, hk, sec))
    case False{}:
      {==}

def pp.kept(es: List<&2, Pp.Put>, +ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +cs: List<&2, Pp.Cell>, +at: List<&2, Nat>, +sec: {PathPolicy.pp_under_any(se, at) == True{} : Bool}, +no: {PathPolicy.pp_no_yes(es) == True{} : Bool}) -> {PathPolicy.pp_cell(Pp.run(es, Pp.Pol{ro, ru, se}, ls, auto, cs), at) == PathPolicy.pp_cell(cs, at) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Pp.Put{+segs, +v, +ans}:
          +na = pp.no_yes_head(ans, segs, v, rest, no)
          +nr = pp.no_yes_rest(ans, segs, v, rest, no)
          +next = Pp.step(Pp.Pol{ro, ru, se}, ls, auto, cs, Pp.Put{segs, v, ans})
          Equal.trans(Maybe<&2, Nat>, PathPolicy.pp_cell(Pp.run(rest, Pp.Pol{ro, ru, se}, ls, auto, next), at), PathPolicy.pp_cell(next, at), PathPolicy.pp_cell(cs, at), pp.kept(rest, ro, ru, se, ls, auto, next, at, sec, nr), pp.put_keeps(Pp.runs(Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.Wr{}, auto, ans), ro, ru, se, ls, auto, cs, segs, v, ans, at, {==}, na, sec))

def PathPolicy.secrets_kept_without_yes(es, ro, ru, se, ls, auto, cs, at, sec, no):
  pp.kept(es, ro, ru, se, ls, auto, cs, at, sec, no)
