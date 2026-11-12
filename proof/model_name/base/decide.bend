# eukhe: lemmas of the model_name proofs: the code's prefix tests are the
# spec's prefix and whole-name tests (sp_pre, sp_same), and the code's
# last part after `/` is the spec's (sp_seg).

import Base
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
