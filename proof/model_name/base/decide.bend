# eukhe: lemmas of the model_name proofs: the code's decisions are the
# spec's (each rule kind, the last part after `/`, the sets over the
# groups, the dash).

import Base
import ../../../bend/text_pat.bend as Tp
import ../../../bend/phrase.bend as P
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA

# Prefixes
# --------

def mnd.got_go(b: Bool, -pt: String, -st: String, ih: {M.got(M.strip(pt, st)) == ModelName.sp_pre(pt, st) : Bool}) -> {M.got(M.strip.go(b, u => M.strip(pt, st))) == Bool.and(b, ModelName.sp_pre(pt, st)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# a prefix stripped off is a spec prefix
def mnd.got_pre(p: String, +s: String) -> {M.got(M.strip(p, s)) == ModelName.sp_pre(p, s) : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +pt}:
      match c:
        case Chr{+cc}:
          match s:
            case SNil{}:
              {==}
            case SCon{x, +st}:
              match x:
                case Chr{+xc}:
                  mnd.got_go(U32.is_eq(cc, xc), pt, st, mnd.got_pre(pt, st))

def mnd.all_go(b: Bool, -pt: String, -st: String, ih: {M.got_all(M.strip(pt, st)) == ModelName.sp_same(pt, st) : Bool}) -> {M.got_all(M.strip.go(b, u => M.strip(pt, st))) == Bool.and(b, ModelName.sp_same(pt, st)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

# the whole name stripped off is the spec's same text
def mnd.got_same(p: String, +s: String) -> {M.got_all(M.strip(p, s)) == ModelName.sp_same(p, s) : Bool}:
  match p:
    case SNil{}:
      {==}
    case SCon{c, +pt}:
      match c:
        case Chr{+cc}:
          match s:
            case SNil{}:
              {==}
            case SCon{x, +st}:
              match x:
                case Chr{+xc}:
                  mnd.all_go(U32.is_eq(cc, xc), pt, st, mnd.got_same(pt, st))

# R1-R3
# -----

def mnd.part(+p: String, s: String) -> {M.part(p, s) == ModelName.sp_part(p, s) : Bool}:
  match s:
    case SNil{}:
      mnd.got_pre(p, SNil{})
    case SCon{+x, +t}:
      LA.mnb.or2(M.got(M.strip(p, SCon{x, t})), M.part(p, t), ModelName.sp_pre(p, SCon{x, t}), ModelName.sp_part(p, t), mnd.got_pre(p, SCon{x, t}), mnd.part(p, t))

def mnd.parts(ps: List<&2, String>, +s: String) -> {M.parts(ps, s) == ModelName.sp_any_part(ps, s) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +more:
      LA.mnb.or2(M.part(q, s), M.parts(more, s), ModelName.sp_part(q, s), ModelName.sp_any_part(more, s), mnd.part(q, s), mnd.parts(more, s))

def mnd.iss(ps: List<&2, String>, +s: String) -> {M.iss(ps, s) == ModelName.sp_any_same(ps, s) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +more:
      LA.mnb.or2(M.got_all(M.strip(q, s)), M.iss(more, s), ModelName.sp_same(q, s), ModelName.sp_any_same(more, s), mnd.got_same(q, s), mnd.iss(more, s))

def mnd.heads(ps: List<&2, String>, +s: String) -> {M.heads(ps, s) == ModelName.sp_any_pre(ps, s) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +more:
      LA.mnb.or2(M.got(M.strip(q, s)), M.heads(more, s), ModelName.sp_pre(q, s), ModelName.sp_any_pre(more, s), mnd.got_pre(q, s), mnd.heads(more, s))

# R4
# --

def mnd.line(+b: String, s: String) -> {M.line_part(b, s) == ModelName.sp_line(b, s) : Bool}:
  match s:
    case SNil{}:
      mnd.got_pre(b, SNil{})
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +n = Bool.not(U32.is_eq(xc, 10))
          LA.mnb.or2(M.got(M.strip(b, SCon{Chr{xc}, t})), P.pm.and(n, v => M.line_part(b, t)), ModelName.sp_pre(b, SCon{Chr{xc}, t}), Bool.and(n, ModelName.sp_line(b, t)), mnd.got_pre(b, SCon{Chr{xc}, t}), LA.mnb.and2(n, M.line_part(b, t), ModelName.sp_line(b, t), mnd.line(b, t)))

def mnd.then_go(b: Bool, +at: String, +bb: String, -st: String, ih: {M.then.at(M.strip(at, st), bb) == ModelName.sp_then_at(at, bb, st) : Bool}) -> {M.then.at(M.strip.go(b, u => M.strip(at, st)), bb) == Bool.and(b, ModelName.sp_then_at(at, bb, st)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def mnd.then_at(a: String, +b: String, +s: String) -> {M.then.at(M.strip(a, s), b) == ModelName.sp_then_at(a, b, s) : Bool}:
  match a:
    case SNil{}:
      mnd.line(b, s)
    case SCon{c, +at}:
      match c:
        case Chr{+cc}:
          match s:
            case SNil{}:
              {==}
            case SCon{x, +st}:
              match x:
                case Chr{+xc}:
                  mnd.then_go(U32.is_eq(cc, xc), at, b, st, mnd.then_at(at, b, st))

def mnd.then(+a: String, +b: String, s: String) -> {M.then(a, b, s) == ModelName.sp_then(a, b, s) : Bool}:
  match s:
    case SNil{}:
      mnd.then_at(a, b, SNil{})
    case SCon{+x, +t}:
      LA.mnb.or2(M.then.at(M.strip(a, SCon{x, t}), b), M.then(a, b, t), ModelName.sp_then_at(a, b, SCon{x, t}), ModelName.sp_then(a, b, t), mnd.then_at(a, b, SCon{x, t}), mnd.then(a, b, t))

# R5
# --

def mnd.end(w: Bool, +xc: U32) -> {M.num.end(w, Chr{xc}) == ModelName.sp_ends(w, Chr{xc}) : Bool}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def mnd.rest_at(g: Bool, +w: Bool, +xc: U32, +t: String, ih: {M.num.rest(t, w) == ModelName.sp_num3(t, w) : Bool}) -> {M.ite(g, u => M.num.rest(t, w), v => M.num.end(w, Chr{xc})) == Bool.or(Bool.and(g, ModelName.sp_num3(t, w)), Bool.and(Bool.not(g), ModelName.sp_ends(w, Chr{xc}))) : Bool}:
  match g:
    case True{}:
      Equal.trans(Bool, M.num.rest(t, w), ModelName.sp_num3(t, w), Bool.or(ModelName.sp_num3(t, w), False{}), ih, Equal.sym(Bool, Bool.or(ModelName.sp_num3(t, w), False{}), ModelName.sp_num3(t, w), LA.mnb.or_false(ModelName.sp_num3(t, w))))
    case False{}:
      mnd.end(w, xc)

def mnd.rest(s: String, +w: Bool) -> {M.num.rest(s, w) == ModelName.sp_num3(s, w) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnd.rest_at(Tp.is_dig(Chr{xc}), w, xc, t, mnd.rest(t, w))

def mnd.sec_end(ok: Bool, w: Bool, +xc: U32) -> {Bool.and(ok, M.num.end(w, Chr{xc})) == Bool.and(ok, ModelName.sp_ends(w, Chr{xc})) : Bool}:
  match ok:
    case True{}:
      mnd.end(w, xc)
    case False{}:
      {==}

def mnd.sec_at(g: Bool, +ok: Bool, +w: Bool, +xc: U32, +t: String) -> {M.ite(g, u => M.num.rest(t, w), v => Bool.and(ok, M.num.end(w, Chr{xc}))) == Bool.or(Bool.and(g, ModelName.sp_num3(t, w)), Bool.and(Bool.not(g), Bool.and(ok, ModelName.sp_ends(w, Chr{xc})))) : Bool}:
  match g:
    case True{}:
      Equal.trans(Bool, M.num.rest(t, w), ModelName.sp_num3(t, w), Bool.or(ModelName.sp_num3(t, w), False{}), mnd.rest(t, w), Equal.sym(Bool, Bool.or(ModelName.sp_num3(t, w), False{}), ModelName.sp_num3(t, w), LA.mnb.or_false(ModelName.sp_num3(t, w))))
    case False{}:
      mnd.sec_end(ok, w, xc)

def mnd.second(s: String, +ok: Bool, +w: Bool) -> {M.num.second(s, ok, w) == ModelName.sp_num2(s, ok, w) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnd.sec_at(Tp.is_dig(Chr{xc}), ok, w, xc, t)

def mnd.first_at(g: Bool, +xc: U32, +t: String, +n: Nat, +w: Bool) -> {M.ite(g, u => M.num.second(t, Nat.is_le(n, M.digit(Chr{xc})), w), v => False{}) == Bool.and(Bool.and(g, True{}), ModelName.sp_num2(t, Nat.is_le(n, M.digit(Chr{xc})), w)) : Bool}:
  match g:
    case True{}:
      mnd.second(t, Nat.is_le(n, M.digit(Chr{xc})), w)
    case False{}:
      {==}

def mnd.num0(z: Bool, +xc: U32, +t: String, +n: Nat, +w: Bool, ih: {M.num.first(M.drop0(t), n, w) == ModelName.sp_num(t, n, w) : Bool}) -> {M.num.first(M.drop0.at(z, SCon{Chr{xc}, t}, u => M.drop0(t)), n, w) == Bool.or(Bool.and(z, ModelName.sp_num(t, n, w)), Bool.and(Bool.and(Tp.is_dig(Chr{xc}), Bool.not(z)), ModelName.sp_num2(t, Nat.is_le(n, M.digit(Chr{xc})), w))) : Bool}:
  match z:
    case True{}:
      +y = ModelName.sp_num(t, n, w)
      +d = Tp.is_dig(Chr{xc})
      %Equal.sym(Bool, Bool.and(d, False{}), False{}, LA.mnb.and_false(d)) : {M.num.first(M.drop0(t), n, w) == Bool.or(y, Bool.and(_, ModelName.sp_num2(t, Nat.is_le(n, M.digit(Chr{xc})), w))) : Bool}
      Equal.trans(Bool, M.num.first(M.drop0(t), n, w), y, Bool.or(y, False{}), ih, Equal.sym(Bool, Bool.or(y, False{}), y, LA.mnb.or_false(y)))
    case False{}:
      mnd.first_at(Tp.is_dig(Chr{xc}), xc, t, n, w)

# the number after the prefix: the code's (drop the zeros, then read) is
# the spec's
def mnd.num(s: String, +n: Nat, +w: Bool) -> {M.num.first(M.drop0(s), n, w) == ModelName.sp_num(s, n, w) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnd.num0(U32.is_eq(xc, 48), xc, t, n, w, mnd.num(t, n, w))

def mnd.on_go(b: Bool, +pt: String, -st: String, +n: Nat, +w: Bool, ih: {M.num.on(M.strip(pt, st), n, w) == ModelName.sp_num_at(pt, st, n, w) : Bool}) -> {M.num.on(M.strip.go(b, u => M.strip(pt, st)), n, w) == Bool.and(b, ModelName.sp_num_at(pt, st, n, w)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      {==}

def mnd.on(p: String, +s: String, +n: Nat, +w: Bool) -> {M.num.on(M.strip(p, s), n, w) == ModelName.sp_num_at(p, s, n, w) : Bool}:
  match p:
    case SNil{}:
      mnd.num(s, n, w)
    case SCon{c, +pt}:
      match c:
        case Chr{+cc}:
          match s:
            case SNil{}:
              {==}
            case SCon{x, +st}:
              match x:
                case Chr{+xc}:
                  mnd.on_go(U32.is_eq(cc, xc), pt, st, n, w, mnd.on(pt, st, n, w))

def mnd.nums(ps: List<&2, String>, +s: String, +n: Nat, +w: Bool) -> {M.nums(ps, s, n, w) == ModelName.sp_any_num(ps, s, n, w) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +q <> +more:
      LA.mnb.or2(M.num.on(M.strip(q, s), n, w), M.nums(more, s, n, w), ModelName.sp_num_at(q, s, n, w), ModelName.sp_any_num(more, s, n, w), mnd.on(q, s, n, w), mnd.nums(more, s, n, w))

# R6
# --

def mnd.seg_pick(e: Bool, h: Bool, -S: String, -t: String, -at: String, -X: String) -> {ModelName.sp_pick(h, S, M.seg.at(e, t, at)) == ModelName.sp_pick(Bool.or(e, h), ModelName.sp_pick(h, S, ModelName.sp_pick(e, t, X)), at) : String}:
  match e:
    case True{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

# the code's walk: the last part when s holds a `/`, else at
def mnd.seg_go(s: String, at: String) -> {M.seg.go(s, at) == ModelName.sp_pick(ModelName.sp_has_slash(s), ModelName.sp_seg(s), at) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +at2 = M.seg.at(U32.is_eq(xc, 47), t, at)
          %Equal.sym(String, M.seg.go(t, at2), ModelName.sp_pick(ModelName.sp_has_slash(t), ModelName.sp_seg(t), at2), mnd.seg_go(t, at2)) : {_ == ModelName.sp_pick(Bool.or(U32.is_eq(xc, 47), ModelName.sp_has_slash(t)), ModelName.sp_seg(SCon{Chr{xc}, t}), at) : String}
          mnd.seg_pick(U32.is_eq(xc, 47), ModelName.sp_has_slash(t), ModelName.sp_seg(t), t, at, SCon{Chr{xc}, t})

# a text with no `/` is its own last part
def mnd.seg_nos(s: String, h: {ModelName.sp_has_slash(s) == False{} : Bool}) -> {ModelName.sp_seg(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = h
          %Equal.sym(Bool, ModelName.sp_has_slash(t), False{}, LA.mnb.or_fr(U32.is_eq(xc, 47), ModelName.sp_has_slash(t), hh)) : {ModelName.sp_pick(_, ModelName.sp_seg(t), ModelName.sp_pick(U32.is_eq(xc, 47), t, SCon{Chr{xc}, t})) == SCon{Chr{xc}, t} : String}
          %Equal.sym(Bool, U32.is_eq(xc, 47), False{}, LA.mnb.or_fl(U32.is_eq(xc, 47), ModelName.sp_has_slash(t), hh)) : {ModelName.sp_pick(False{}, ModelName.sp_seg(t), ModelName.sp_pick(_, t, SCon{Chr{xc}, t})) == SCon{Chr{xc}, t} : String}
          {==}

def mnd.seg_fin(h: Bool, +s: String, eh: {ModelName.sp_has_slash(s) == h : Bool}) -> {ModelName.sp_pick(h, ModelName.sp_seg(s), s) == ModelName.sp_seg(s) : String}:
  match h:
    case True{}:
      {==}
    case False{}:
      Equal.sym(String, ModelName.sp_seg(s), s, mnd.seg_nos(s, eh))

# the code's last part is the spec's
def mnd.seg(+s: String) -> {M.seg(s) == ModelName.sp_seg(s) : String}:
  Equal.trans(String, M.seg(s), ModelName.sp_pick(ModelName.sp_has_slash(s), ModelName.sp_seg(s), s), ModelName.sp_seg(s), mnd.seg_go(s, s), mnd.seg_fin(ModelName.sp_has_slash(s), s, {==}))

# Rules, sets, groups
# -------------------

def mnd.rule(r: M.Rule, +s: String) -> {M.rule(r, s) == ModelName.sp_rule(r, s) : Bool}:
  match r:
    case M.RContains{ps}:
      mnd.parts(ps, s)
    case M.RIs{ps}:
      mnd.iss(ps, s)
    case M.RStarts{ps}:
      mnd.heads(ps, s)
    case M.RThen{a, b}:
      mnd.then(a, b, s)
    case M.RNumber{ps, n, w}:
      mnd.nums(ps, s, n, w)
    case M.RSegment{+ps}:
      %mnd.seg(s) : {M.heads(ps, M.seg(s)) == ModelName.sp_any_pre(ps, _) : Bool}
      mnd.heads(ps, M.seg(s))

def mnd.rules(rs: List<&2, M.Rule>, +s: String) -> {M.rules(rs, s) == ModelName.sp_any_rule(rs, s) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +more:
      LA.mnb.or2(M.rule(r, s), M.rules(more, s), ModelName.sp_rule(r, s), ModelName.sp_any_rule(more, s), mnd.rule(r, s), mnd.rules(more, s))

def mnd.set(+rs: List<&2, M.Rule>, g: List<&2, String>) -> {M.set_holds(rs, g) == ModelName.sp_set(rs, g) : Bool}:
  match g:
    case Nil{}:
      {==}
    case +s <> +more:
      LA.mnb.or2(M.rules(rs, s), M.set_holds(rs, more), ModelName.sp_any_rule(rs, s), ModelName.sp_set(rs, more), mnd.rules(rs, s), mnd.set(rs, more))

def mnd.row(sets: List<&2, List<&2, M.Rule>>, +g: List<&2, String>, -rest: List<&2, Bool>) -> {M.row(sets, g, rest) == List.append(&2, Bool, ModelName.sp_row(sets, g), rest) : List<&2, Bool>}:
  match sets:
    case Nil{}:
      {==}
    case +rs <> more:
      %Equal.sym(Bool, M.set_holds(rs, g), ModelName.sp_set(rs, g), mnd.set(rs, g)) : {_ <> M.row(more, g, rest) == ModelName.sp_set(rs, g) <> List.append(&2, Bool, ModelName.sp_row(more, g), rest) : List<&2, Bool>}
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => ModelName.sp_set(rs, g) <> z, M.row(more, g, rest), List.append(&2, Bool, ModelName.sp_row(more, g), rest), mnd.row(more, g, rest))

def mnd.holds(+sets: List<&2, List<&2, M.Rule>>, groups: List<&2, List<&2, String>>) -> {M.holds(sets, groups) == ModelName.sp_verdicts(sets, groups) : List<&2, Bool>}:
  match groups:
    case Nil{}:
      {==}
    case +g <> more:
      %Equal.sym(List<&2, Bool>, M.row(sets, g, M.holds(sets, more)), List.append(&2, Bool, ModelName.sp_row(sets, g), M.holds(sets, more)), mnd.row(sets, g, M.holds(sets, more))) : {_ == List.append(&2, Bool, ModelName.sp_row(sets, g), ModelName.sp_verdicts(sets, more)) : List<&2, Bool>}
      Equal.cong(List<&2, Bool>, List<&2, Bool>, z => List.append(&2, Bool, ModelName.sp_row(sets, g), z), M.holds(sets, more), ModelName.sp_verdicts(sets, more), mnd.holds(sets, more))

# R8: dash
# --------

def mnd.dash_at(sx: Bool, pv: Bool, +x: Char, -t: String, -R: String, ih: {M.dash.go(t, sx) == R : String}) -> {M.dash.at(sx, pv, x, r => M.dash.go(t, r)) == String.append(ModelName.sp_piece.at(sx, pv, x), R) : String}:
  match sx:
    case True{}:
      match pv:
        case True{}:
          ih
        case False{}:
          LA.mnb.cons_eq('-', M.dash.go(t, True{}), R, ih)
    case False{}:
      LA.mnb.cons_eq(x, M.dash.go(t, False{}), R, ih)

def mnd.dash_go(s: String, +prev: Maybe<&2, Char>) -> {M.dash.go(s, ModelName.sp_sep_m(prev)) == ModelName.sp_dash.go(s, prev) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mnd.dash_at(ModelName.sp_sep(Chr{xc}), ModelName.sp_sep_m(prev), Chr{xc}, t, ModelName.sp_dash.go(t, Some{Chr{xc}}), mnd.dash_go(t, Some{Chr{xc}}))
