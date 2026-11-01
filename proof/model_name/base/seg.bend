# eukhe: lemmas of the model_name proofs: R6, the last part after `/`
# against its split (name = a ++ part, a empty or ending with `/`, the
# part without `/`).

import Base
import ../../../bend/model_name.bend as M
import ../../../laws/model_name.bend as ModelName
import ../base.bend as LA
import ./decide.bend as LD

# a start that ends with `/` puts a `/` before anything after it
def mns.start_has(t: String, x: Char, -u: String, ha: {ModelName.sp_seg_start(SCon{x, t}) == True{} : Bool}) -> {ModelName.sp_has_slash(SCon{x, String.append(t, u)}) == True{} : Bool}:
  match t:
    case SNil{}:
      match x:
        case Chr{+xc}:
          %Equal.sym(Bool, U32.is_eq(xc, 47), True{}, ha) : {Bool.or(_, ModelName.sp_has_slash(u)) == True{} : Bool}
          {==}
    case SCon{+y, +w}:
      match x:
        case Chr{+xc}:
          LA.mnb.or_rt(U32.is_eq(xc, 47), ModelName.sp_has_slash(SCon{y, String.append(w, u)}), mns.start_has(w, y, u, ha))

# after a start that is empty or ends with `/`, a part with no `/` is the
# last part
def mns.seg_app(a: String, +u: String, ha: {ModelName.sp_seg_start(a) == True{} : Bool}, hu: {ModelName.sp_has_slash(u) == False{} : Bool}) -> {ModelName.sp_seg(String.append(a, u)) == u : String}:
  match a:
    case SNil{}:
      LD.mnd.seg_nos(u, hu)
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          match t:
            case SNil{}:
              %Equal.sym(Bool, ModelName.sp_has_slash(u), False{}, hu) : {ModelName.sp_pick(_, ModelName.sp_seg(u), ModelName.sp_pick(U32.is_eq(xc, 47), u, SCon{Chr{xc}, u})) == u : String}
              %Equal.sym(Bool, U32.is_eq(xc, 47), True{}, ha) : {ModelName.sp_pick(False{}, ModelName.sp_seg(u), ModelName.sp_pick(_, u, SCon{Chr{xc}, u})) == u : String}
              {==}
            case SCon{+y, +w}:
              +hh = ha
              %Equal.sym(Bool, ModelName.sp_has_slash(SCon{y, String.append(w, u)}), True{}, mns.start_has(w, y, u, hh)) : {ModelName.sp_pick(_, ModelName.sp_seg(SCon{y, String.append(w, u)}), ModelName.sp_pick(U32.is_eq(xc, 47), SCon{y, String.append(w, u)}, SCon{Chr{xc}, SCon{y, String.append(w, u)}})) == u : String}
              mns.seg_app(SCon{y, w}, u, hh, hu)

# the code's last part after a start that ends with `/`
def mns.code_app(+a: String, +u: String, ha: {ModelName.sp_seg_start(a) == True{} : Bool}, hu: {ModelName.sp_has_slash(u) == False{} : Bool}) -> {M.seg(String.append(a, u)) == u : String}:
  Equal.trans(String, M.seg(String.append(a, u)), ModelName.sp_seg(String.append(a, u)), u, LD.mnd.seg(String.append(a, u)), mns.seg_app(a, u, ha, hu))

# every text is a start, then its last part
def mns.SegQ(s: String, g: String) -> Type:
  Sigma<&1, &1, String, a => {s == String.append(a, g) : String} & ({ModelName.sp_seg_start(a) == True{} : Bool} & {ModelName.sp_has_slash(g) == False{} : Bool})>

def mns.cons_start(+x: Char, a: String, -t: String, -g: String, es: {t == String.append(a, g) : String}, st: {ModelName.sp_seg_start(a) == True{} : Bool}, nh: {ModelName.sp_has_slash(g) == False{} : Bool}, eh: {ModelName.sp_has_slash(t) == True{} : Bool}) -> {ModelName.sp_seg_start(SCon{x, a}) == True{} : Bool}:
  match a:
    case SNil{}:
      +e1 = Equal.cong(String, Bool, z => ModelName.sp_has_slash(z), t, g, es)
      LA.mnb.clash({ModelName.sp_seg_start(SCon{x, SNil{}}) == True{} : Bool}, ModelName.sp_has_slash(t), eh, Equal.trans(Bool, ModelName.sp_has_slash(t), ModelName.sp_has_slash(g), False{}, e1, nh))
    case SCon{y, w}:
      st

def mns.has_ff(a: Bool, b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      LA.mnb.absurd({Bool.or(True{}, b) == False{} : Bool}, ea)
    case False{}:
      eb

def mns.split_has(+xc: U32, +t: String, eh: {ModelName.sp_has_slash(t) == True{} : Bool}, +a: String, +es: {t == String.append(a, ModelName.sp_seg(t)) : String}, st: {ModelName.sp_seg_start(a) == True{} : Bool}, +nh: {ModelName.sp_has_slash(ModelName.sp_seg(t)) == False{} : Bool}) -> mns.SegQ(SCon{Chr{xc}, t}, ModelName.sp_seg(t)):
  (SCon{Chr{xc}, a}, (LA.mnb.cons_eq(Chr{xc}, t, String.append(a, ModelName.sp_seg(t)), es), (mns.cons_start(Chr{xc}, a, t, ModelName.sp_seg(t), es, st, nh, eh), nh)))

def mns.split_at(+xc: U32, +t: String, h: Bool, eh: {ModelName.sp_has_slash(t) == h : Bool}, e: Bool, ee: {U32.is_eq(xc, 47) == e : Bool}, ih: mns.SegQ(t, ModelName.sp_seg(t))) -> mns.SegQ(SCon{Chr{xc}, t}, ModelName.sp_pick(h, ModelName.sp_seg(t), ModelName.sp_pick(e, t, SCon{Chr{xc}, t}))):
  match h:
    case True{}:
      (+a, (es, (st, nh))) = ih
      mns.split_has(xc, t, eh, a, es, st, nh)
    case False{}:
      match e:
        case True{}:
          (SCon{Chr{xc}, SNil{}}, ({==}, (ee, eh)))
        case False{}:
          (SNil{}, ({==}, ({==}, mns.has_ff(U32.is_eq(xc, 47), ModelName.sp_has_slash(t), ee, eh))))

# every text is a start that is empty or ends with `/`, then its last part
def mns.split(s: String) -> mns.SegQ(s, ModelName.sp_seg(s)):
  match s:
    case SNil{}:
      (SNil{}, ({==}, ({==}, {==})))
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          mns.split_at(xc, t, ModelName.sp_has_slash(t), {==}, U32.is_eq(xc, 47), {==}, mns.split(t))
