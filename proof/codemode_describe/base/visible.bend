# eukhe: lemmas of the proof of LAW codemode_describe_section_exact: the
# tools shown (Dsc.visible: a set of the placed names and one walk over the
# tools) are the spec's (shown_spec): a set built from names holds exactly
# those names (cdv.of, from cdv.add for one name added to a forest), and
# the walk finds the name of each tool (cdv.vis)

import Base
import ../../../bend/codemode_describe.bend as Dsc
import ../../../laws/codemode_describe.bend as CodemodeDescribe
import ../../base/staging.bend as LStg
import ../../base/nat.bend as LNatB

# ---- logic ----

def cdv.T(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# anything follows from True == False
def cdv.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : cdv.T(_, G)
  Unit{}

def cdv.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# ---- chars and strings ----

# a Cmp that is_eq is EQ
def cdv.cmp_eq(o: Cmp, h: {Cmp.is_eq(o) == True{} : Bool}) -> {o == EQ{} : Cmp}:
  match o:
    case LT{}:
      cdv.absurd({LT{} == EQ{} : Cmp}, Equal.sym(Bool, False{}, True{}, h))
    case EQ{}:
      {==}
    case GT{}:
      cdv.absurd({GT{} == EQ{} : Cmp}, Equal.sym(Bool, False{}, True{}, h))

# two strings' order past a first difference keeps it
def cdv.go_lt(a: String, b: String) -> {String.order.go(a, b, LT{}) == LT{} : Cmp}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{h, t}:
          {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          match b:
            case SNil{}:
              {==}
            case SCon{h2, t2}:
              match h2:
                case Chr{y}:
                  {==}

def cdv.go_gt(a: String, b: String) -> {String.order.go(a, b, GT{}) == GT{} : Cmp}:
  match a:
    case SNil{}:
      match b:
        case SNil{}:
          {==}
        case SCon{h, t}:
          {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          match b:
            case SNil{}:
              {==}
            case SCon{h2, t2}:
              match h2:
                case Chr{y}:
                  {==}

def cdv.go_ne(+a: String, +b: String, o: Cmp, h: {Cmp.is_eq(o) == False{} : Bool}) -> {Cmp.is_eq(String.order.go(a, b, o)) == False{} : Bool}:
  match o:
    case LT{}:
      %Equal.sym(Cmp, String.order.go(a, b, LT{}), LT{}, cdv.go_lt(a, b)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}
    case EQ{}:
      cdv.absurd({Cmp.is_eq(String.order.go(a, b, EQ{})) == False{} : Bool}, h)
    case GT{}:
      %Equal.sym(Cmp, String.order.go(a, b, GT{}), GT{}, cdv.go_gt(a, b)) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

# a string starting with c compares with one starting with c as the rests
def cdv.same_c(c: Char, +r: String, +q: String) -> {String.eq(SCon{c, r}, SCon{c, q}) == String.eq(r, q) : Bool}:
  match c:
    case Chr{+x}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, cdv.cmp_eq(U32.cmp(x, x), LStg.stg.char_refl(Chr{x}))) : {Cmp.is_eq(String.order.go(r, q, _)) == String.eq(r, q) : Bool}
      {==}

# equal first chars: the strings compare as their rests
def cdv.same(+c: Char, +d: Char, +r: String, +q: String, e: {Char.is_eq(c, d) == True{} : Bool}) -> {String.eq(SCon{c, r}, SCon{d, q}) == String.eq(r, q) : Bool}:
  %LStg.stg.char_sound(c, d, e) : {String.eq(SCon{c, r}, SCon{_, q}) == String.eq(r, q) : Bool}
  cdv.same_c(c, r, q)

# different first chars: the strings differ
def cdv.diff(c: Char, d: Char, +r: String, +q: String, e: {Char.is_eq(c, d) == False{} : Bool}) -> {String.eq(SCon{c, r}, SCon{d, q}) == False{} : Bool}:
  match c:
    case Chr{x}:
      match d:
        case Chr{y}:
          cdv.go_ne(r, q, U32.cmp(x, y), e)

# a string that goes on is not the empty one
def cdv.con_nil(e: Char, q: String) -> {String.eq(SCon{e, q}, SNil{}) == False{} : Bool}:
  match e:
    case Chr{x}:
      {==}

def cdv.nil_con(e: Char, q: String) -> {String.eq(SNil{}, SCon{e, q}) == False{} : Bool}:
  match e:
    case Chr{x}:
      {==}

def cdv.sym_at(b: Bool, +c: Char, +d: Char, eb: {Char.is_eq(d, c) == b : Bool}, e: {Char.is_eq(c, d) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      %e : {True{} == _ : Bool}
      %Equal.sym(Char, d, c, LStg.stg.char_sound(d, c, eb)) : {True{} == Char.is_eq(c, _) : Bool}
      Equal.sym(Bool, Char.is_eq(c, c), True{}, LStg.stg.char_refl(c))
    case False{}:
      {==}

# Char.is_eq is symmetric where it fails
def cdv.sym_f(+c: Char, +d: Char, e: {Char.is_eq(c, d) == False{} : Bool}) -> {Char.is_eq(d, c) == False{} : Bool}:
  cdv.sym_at(Char.is_eq(d, c), c, d, {==}, e)

# a node's char is c and c2: c is c2
def cdv.both(+d: Char, +c: Char, -c2: Char, e1: {Char.is_eq(d, c) == True{} : Bool}, e2: {Char.is_eq(d, c2) == True{} : Bool}) -> {Char.is_eq(c, c2) == True{} : Bool}:
  %LStg.stg.char_sound(d, c, e1) : {Char.is_eq(_, c2) == True{} : Bool}
  e2

# a node's char is c and not c2: c is not c2
def cdv.one(+d: Char, +c: Char, -c2: Char, e1: {Char.is_eq(d, c) == True{} : Bool}, e2: {Char.is_eq(d, c2) == False{} : Bool}) -> {Char.is_eq(c, c2) == False{} : Bool}:
  %LStg.stg.char_sound(d, c, e1) : {Char.is_eq(_, c2) == False{} : Bool}
  e2

# a node's char is c2 and not c: c is not c2
def cdv.other(+d: Char, +c: Char, +c2: Char, e1: {Char.is_eq(d, c) == False{} : Bool}, e2: {Char.is_eq(d, c2) == True{} : Bool}) -> {Char.is_eq(c, c2) == False{} : Bool}:
  %LStg.stg.char_sound(d, c2, e2) : {Char.is_eq(c, _) == False{} : Bool}
  cdv.sym_f(d, c, e1)

# ---- the chain of one name ----

def cdv.chain_nil(b: Bool, +c: Char, +c2: Char, r2: String, eb: {Char.is_eq(c, c2) == b : Bool}) -> {Dsc.tr.has(Dsc.TNode{c, True{}, Dsc.TEnd{}, Dsc.TEnd{}}, b, c2, r2) == String.eq(SCon{c, SNil{}}, SCon{c2, r2}) : Bool}:
  match b:
    case True{}:
      match r2:
        case SNil{}:
          %Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, SNil{}}), String.eq(SNil{}, SNil{}), cdv.same(c, c2, SNil{}, SNil{}, eb)) : {True{} == _ : Bool}
          {==}
        case SCon{+e, +q}:
          %Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, SCon{e, q}}), String.eq(SNil{}, SCon{e, q}), cdv.same(c, c2, SNil{}, SCon{e, q}, eb)) : {False{} == _ : Bool}
          Equal.sym(Bool, String.eq(SNil{}, SCon{e, q}), False{}, cdv.nil_con(e, q))
    case False{}:
      Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, r2}), False{}, cdv.diff(c, c2, SNil{}, r2, eb))

def cdv.chain_con_nil(b: Bool, +c: Char, +c2: Char, +e: Char, +q: String, eb: {Char.is_eq(c, c2) == b : Bool}) -> {Dsc.tr.has(Dsc.TNode{c, False{}, Dsc.tr.chain(q, e), Dsc.TEnd{}}, b, c2, SNil{}) == String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), String.eq(SCon{e, q}, SNil{}), cdv.same(c, c2, SCon{e, q}, SNil{}, eb)) : {False{} == _ : Bool}
      Equal.sym(Bool, String.eq(SCon{e, q}, SNil{}), False{}, cdv.con_nil(e, q))
    case False{}:
      Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), False{}, cdv.diff(c, c2, SCon{e, q}, SNil{}, eb))

def cdv.chain_con_con(b: Bool, +c: Char, +c2: Char, +e: Char, +q: String, +e2: Char, +q2: String, eb: {Char.is_eq(c, c2) == b : Bool}, ih: {Dsc.tr.has(Dsc.tr.chain(q, e), Dsc.tr.hit(Dsc.tr.chain(q, e), e2), e2, q2) == String.eq(SCon{e, q}, SCon{e2, q2}) : Bool}) -> {Dsc.tr.has(Dsc.TNode{c, False{}, Dsc.tr.chain(q, e), Dsc.TEnd{}}, b, c2, SCon{e2, q2}) == String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), String.eq(SCon{e, q}, SCon{e2, q2}), cdv.same(c, c2, SCon{e, q}, SCon{e2, q2}, eb)) : {Dsc.tr.has(Dsc.tr.chain(q, e), Dsc.tr.hit(Dsc.tr.chain(q, e), e2), e2, q2) == _ : Bool}
      ih
    case False{}:
      Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), False{}, cdv.diff(c, c2, SCon{e, q}, SCon{e2, q2}, eb))

# the forest of one name holds exactly that name
def cdv.chain(r: String, +c: Char, +c2: Char, +r2: String) -> {Dsc.tr.has(Dsc.tr.chain(r, c), Dsc.tr.hit(Dsc.tr.chain(r, c), c2), c2, r2) == String.eq(SCon{c, r}, SCon{c2, r2}) : Bool}:
  match r:
    case SNil{}:
      cdv.chain_nil(Char.is_eq(c, c2), c, c2, r2, {==})
    case SCon{+e, +q}:
      match r2:
        case SNil{}:
          cdv.chain_con_nil(Char.is_eq(c, c2), c, c2, e, q, {==})
        case SCon{+e2, +q2}:
          cdv.chain_con_con(Char.is_eq(c, c2), c, c2, e, q, e2, q2, {==}, cdv.chain(q, e, e2, q2))

# ---- one name added to a forest ----

# the node's char is not c: c went to the next siblings
def cdv.add_f(b2: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +r: String, +c2: Char, +r2: String, e1: {Char.is_eq(d, c) == False{} : Bool}, e2: {Char.is_eq(d, c2) == b2 : Bool}, ihn: {Dsc.tr.has(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, r), Dsc.tr.hit(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, r), c2), c2, r2) == Bool.or(String.eq(SCon{c, r}, SCon{c2, r2}), Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, r2)) : Bool}) -> {Dsc.tr.has(Dsc.TNode{d, s, w, Dsc.tr.add(n, Dsc.tr.hit(n, c), c, r)}, b2, c2, r2) == Bool.or(String.eq(SCon{c, r}, SCon{c2, r2}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, b2, c2, r2)) : Bool}:
  match b2:
    case True{}:
      match r2:
        case SNil{}:
          %Equal.sym(Bool, String.eq(SCon{c, r}, SCon{c2, SNil{}}), False{}, cdv.diff(c, c2, r, SNil{}, cdv.other(d, c, c2, e1, e2))) : {s == Bool.or(_, s) : Bool}
          {==}
        case SCon{+e, +q}:
          %Equal.sym(Bool, String.eq(SCon{c, r}, SCon{c2, SCon{e, q}}), False{}, cdv.diff(c, c2, r, SCon{e, q}, cdv.other(d, c, c2, e1, e2))) : {Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q) == Bool.or(_, Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q)) : Bool}
          {==}
    case False{}:
      ihn

# the node's char is c and the name ends there
def cdv.add_tn(b2: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +c2: Char, +r2: String, e1: {Char.is_eq(d, c) == True{} : Bool}, e2: {Char.is_eq(d, c2) == b2 : Bool}) -> {Dsc.tr.has(Dsc.TNode{d, True{}, w, n}, b2, c2, r2) == Bool.or(String.eq(SCon{c, SNil{}}, SCon{c2, r2}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, b2, c2, r2)) : Bool}:
  match b2:
    case True{}:
      match r2:
        case SNil{}:
          %Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, SNil{}}), String.eq(SNil{}, SNil{}), cdv.same(c, c2, SNil{}, SNil{}, cdv.both(d, c, c2, e1, e2))) : {True{} == Bool.or(_, s) : Bool}
          {==}
        case SCon{+e, +q}:
          %Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, SCon{e, q}}), String.eq(SNil{}, SCon{e, q}), cdv.same(c, c2, SNil{}, SCon{e, q}, cdv.both(d, c, c2, e1, e2))) : {Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q) == Bool.or(_, Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q)) : Bool}
          %Equal.sym(Bool, String.eq(SNil{}, SCon{e, q}), False{}, cdv.nil_con(e, q)) : {Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q) == Bool.or(_, Dsc.tr.has(w, Dsc.tr.hit(w, e), e, q)) : Bool}
          {==}
    case False{}:
      %Equal.sym(Bool, String.eq(SCon{c, SNil{}}, SCon{c2, r2}), False{}, cdv.diff(c, c2, SNil{}, r2, cdv.one(d, c, c2, e1, e2))) : {Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, r2) == Bool.or(_, Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, r2)) : Bool}
      {==}

# the node's char is c, the name goes on, and the other ends at the node
def cdv.add_tcn(b2: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +e: Char, +q: String, +c2: Char, e1: {Char.is_eq(d, c) == True{} : Bool}, e2: {Char.is_eq(d, c2) == b2 : Bool}) -> {Dsc.tr.has(Dsc.TNode{d, s, Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), n}, b2, c2, SNil{}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, b2, c2, SNil{})) : Bool}:
  match b2:
    case True{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), String.eq(SCon{e, q}, SNil{}), cdv.same(c, c2, SCon{e, q}, SNil{}, cdv.both(d, c, c2, e1, e2))) : {s == Bool.or(_, s) : Bool}
      %Equal.sym(Bool, String.eq(SCon{e, q}, SNil{}), False{}, cdv.con_nil(e, q)) : {s == Bool.or(_, s) : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), False{}, cdv.diff(c, c2, SCon{e, q}, SNil{}, cdv.one(d, c, c2, e1, e2))) : {Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SNil{}) == Bool.or(_, Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SNil{})) : Bool}
      {==}

# the node's char is c and both names go on
def cdv.add_tcc(b2: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +e: Char, +q: String, +c2: Char, +e2: Char, +q2: String, e1: {Char.is_eq(d, c) == True{} : Bool}, eb: {Char.is_eq(d, c2) == b2 : Bool}, ihw: {Dsc.tr.has(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), Dsc.tr.hit(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), e2), e2, q2) == Bool.or(String.eq(SCon{e, q}, SCon{e2, q2}), Dsc.tr.has(w, Dsc.tr.hit(w, e2), e2, q2)) : Bool}) -> {Dsc.tr.has(Dsc.TNode{d, s, Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), n}, b2, c2, SCon{e2, q2}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, b2, c2, SCon{e2, q2})) : Bool}:
  match b2:
    case True{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), String.eq(SCon{e, q}, SCon{e2, q2}), cdv.same(c, c2, SCon{e, q}, SCon{e2, q2}, cdv.both(d, c, c2, e1, eb))) : {Dsc.tr.has(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), Dsc.tr.hit(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), e2), e2, q2) == Bool.or(_, Dsc.tr.has(w, Dsc.tr.hit(w, e2), e2, q2)) : Bool}
      ihw
    case False{}:
      %Equal.sym(Bool, String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), False{}, cdv.diff(c, c2, SCon{e, q}, SCon{e2, q2}, cdv.one(d, c, c2, e1, eb))) : {Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SCon{e2, q2}) == Bool.or(_, Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SCon{e2, q2})) : Bool}
      {==}

def cdv.add_n(b1: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +c2: Char, +r2: String, e1: {Char.is_eq(d, c) == b1 : Bool}, ihn: {Dsc.tr.has(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SNil{}), Dsc.tr.hit(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SNil{}), c2), c2, r2) == Bool.or(String.eq(SCon{c, SNil{}}, SCon{c2, r2}), Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, r2)) : Bool}) -> {Dsc.tr.has(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SNil{}), Dsc.tr.hit(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SNil{}), c2), c2, r2) == Bool.or(String.eq(SCon{c, SNil{}}, SCon{c2, r2}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, Char.is_eq(d, c2), c2, r2)) : Bool}:
  match b1:
    case True{}:
      cdv.add_tn(Char.is_eq(d, c2), d, s, w, n, c, c2, r2, e1, {==})
    case False{}:
      cdv.add_f(Char.is_eq(d, c2), d, s, w, n, c, SNil{}, c2, r2, e1, {==}, ihn)

def cdv.add_cn(b1: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +e: Char, +q: String, +c2: Char, e1: {Char.is_eq(d, c) == b1 : Bool}, ihn: {Dsc.tr.has(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SCon{e, q}), Dsc.tr.hit(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SCon{e, q}), c2), c2, SNil{}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SNil{})) : Bool}) -> {Dsc.tr.has(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SCon{e, q}), Dsc.tr.hit(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SCon{e, q}), c2), c2, SNil{}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SNil{}}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, Char.is_eq(d, c2), c2, SNil{})) : Bool}:
  match b1:
    case True{}:
      cdv.add_tcn(Char.is_eq(d, c2), d, s, w, n, c, e, q, c2, e1, {==})
    case False{}:
      cdv.add_f(Char.is_eq(d, c2), d, s, w, n, c, SCon{e, q}, c2, SNil{}, e1, {==}, ihn)

def cdv.add_cc(b1: Bool, +d: Char, +s: Bool, +w: Dsc.Tr, +n: Dsc.Tr, +c: Char, +e: Char, +q: String, +c2: Char, +e2: Char, +q2: String, e1: {Char.is_eq(d, c) == b1 : Bool}, ihn: {Dsc.tr.has(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SCon{e, q}), Dsc.tr.hit(Dsc.tr.add(n, Dsc.tr.hit(n, c), c, SCon{e, q}), c2), c2, SCon{e2, q2}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), Dsc.tr.has(n, Dsc.tr.hit(n, c2), c2, SCon{e2, q2})) : Bool}, ihw: {Dsc.tr.has(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), Dsc.tr.hit(Dsc.tr.add(w, Dsc.tr.hit(w, e), e, q), e2), e2, q2) == Bool.or(String.eq(SCon{e, q}, SCon{e2, q2}), Dsc.tr.has(w, Dsc.tr.hit(w, e2), e2, q2)) : Bool}) -> {Dsc.tr.has(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SCon{e, q}), Dsc.tr.hit(Dsc.tr.add(Dsc.TNode{d, s, w, n}, b1, c, SCon{e, q}), c2), c2, SCon{e2, q2}) == Bool.or(String.eq(SCon{c, SCon{e, q}}, SCon{c2, SCon{e2, q2}}), Dsc.tr.has(Dsc.TNode{d, s, w, n}, Char.is_eq(d, c2), c2, SCon{e2, q2})) : Bool}:
  match b1:
    case True{}:
      cdv.add_tcc(Char.is_eq(d, c2), d, s, w, n, c, e, q, c2, e2, q2, e1, {==}, ihw)
    case False{}:
      cdv.add_f(Char.is_eq(d, c2), d, s, w, n, c, SCon{e, q}, c2, SCon{e2, q2}, e1, {==}, ihn)

# a forest with the name c then r added holds that name and what it held
def cdv.add(t: Dsc.Tr, +c: Char, +r: String, +c2: Char, +r2: String) -> {Dsc.tr.has(Dsc.tr.add(t, Dsc.tr.hit(t, c), c, r), Dsc.tr.hit(Dsc.tr.add(t, Dsc.tr.hit(t, c), c, r), c2), c2, r2) == Bool.or(String.eq(SCon{c, r}, SCon{c2, r2}), Dsc.tr.has(t, Dsc.tr.hit(t, c2), c2, r2)) : Bool}:
  match t:
    case Dsc.TEnd{}:
      %Equal.sym(Bool, Bool.or(String.eq(SCon{c, r}, SCon{c2, r2}), False{}), String.eq(SCon{c, r}, SCon{c2, r2}), cdv.or_false(String.eq(SCon{c, r}, SCon{c2, r2}))) : {Dsc.tr.has(Dsc.tr.chain(r, c), Dsc.tr.hit(Dsc.tr.chain(r, c), c2), c2, r2) == _ : Bool}
      cdv.chain(r, c, c2, r2)
    case Dsc.TNode{+d, +s, +w, +n}:
      match r:
        case SNil{}:
          cdv.add_n(Char.is_eq(d, c), d, s, w, n, c, c2, r2, {==}, cdv.add(n, c, SNil{}, c2, r2))
        case SCon{+e, +q}:
          match r2:
            case SNil{}:
              cdv.add_cn(Char.is_eq(d, c), d, s, w, n, c, e, q, c2, {==}, cdv.add(n, c, SCon{e, q}, c2, SNil{}))
            case SCon{+e2, +q2}:
              cdv.add_cc(Char.is_eq(d, c), d, s, w, n, c, e, q, c2, e2, q2, {==}, cdv.add(n, c, SCon{e, q}, c2, SCon{e2, q2}), cdv.add(w, e, q, e2, q2))

# ---- the set of names ----

def cdv.nset_add(s: Dsc.NSet, +y: String, +x: String) -> {Dsc.nset.has(Dsc.nset.add(s, y), x) == Bool.or(String.eq(y, x), Dsc.nset.has(s, x)) : Bool}:
  match s:
    case Dsc.NSet{+e, +t}:
      match y:
        case SNil{}:
          match x:
            case SNil{}:
              {==}
            case SCon{+c2, +r2}:
              %Equal.sym(Bool, String.eq(SNil{}, SCon{c2, r2}), False{}, cdv.nil_con(c2, r2)) : {Dsc.tr.has(t, Dsc.tr.hit(t, c2), c2, r2) == Bool.or(_, Dsc.tr.has(t, Dsc.tr.hit(t, c2), c2, r2)) : Bool}
              {==}
        case SCon{+c, +r}:
          match x:
            case SNil{}:
              %Equal.sym(Bool, String.eq(SCon{c, r}, SNil{}), False{}, cdv.con_nil(c, r)) : {e == Bool.or(_, e) : Bool}
              {==}
            case SCon{+c2, +r2}:
              cdv.add(t, c, r, c2, r2)

# the set of names ns holds exactly the names of ns
def cdv.of(ns: List<&2, String>, +x: String) -> {Dsc.nset.has(Dsc.nset.of(ns), x) == CodemodeDescribe.has_name(ns, x) : Bool}:
  match ns:
    case Nil{}:
      match x:
        case SNil{}:
          {==}
        case SCon{c, r}:
          {==}
    case Con{+y, +r}:
      %Equal.sym(Bool, Dsc.nset.has(Dsc.nset.add(Dsc.nset.of(r), y), x), Bool.or(String.eq(y, x), Dsc.nset.has(Dsc.nset.of(r), x)), cdv.nset_add(Dsc.nset.of(r), y, x)) : {_ == CodemodeDescribe.has_name(Con{y, r}, x) : Bool}
      %cdv.of(r, x) : {Bool.or(String.eq(y, x), Dsc.nset.has(Dsc.nset.of(r), x)) == Bool.or(String.eq(y, x), _) : Bool}
      {==}

# ---- the walk over the tools ----

# the name of the tool at t is the first name from t on
def cdv.head(ts: List<&2, Dsc.Tool>, t: Nat) -> {Dsc.head_name(List.drop(&2, Dsc.Tool, ts, t)) == CodemodeDescribe.tool_name_spec(ts, t) : String}:
  match ts:
    case Nil{}:
      {==}
    case Con{x, r}:
      match x:
        case Dsc.Tool{nm, z}:
          match t:
            case 0n:
              {==}
            case 1n+k:
              cdv.head(r, k)

def cdv.drop0(ts: List<&2, Dsc.Tool>) -> {ts == List.drop(&2, Dsc.Tool, ts, 0n) : List<&2, Dsc.Tool>}:
  match ts:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def cdv.drop2(xs: List<&2, Dsc.Tool>, a: Nat, -b: Nat) -> {List.drop(&2, Dsc.Tool, List.drop(&2, Dsc.Tool, xs, a), b) == List.drop(&2, Dsc.Tool, xs, Nat.add(a, b)) : List<&2, Dsc.Tool>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      match a:
        case 0n:
          {==}
        case 1n+p:
          cdv.drop2(t, p, b)

# the walk's tools from t on are the tools from t on
def cdv.here(b: Bool, -cur: List<&2, Dsc.Tool>, +ts: List<&2, Dsc.Tool>, +pos: Nat, +t: Nat, eb: {Nat.is_le(pos, t) == b : Bool}, ec: {cur == List.drop(&2, Dsc.Tool, ts, pos) : List<&2, Dsc.Tool>}) -> {Dsc.vis.here(b, cur, ts, pos, t) == List.drop(&2, Dsc.Tool, ts, t) : List<&2, Dsc.Tool>}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Dsc.Tool>, cur, List.drop(&2, Dsc.Tool, ts, pos), ec) : {List.drop(&2, Dsc.Tool, _, Nat.sub(t, pos)) == List.drop(&2, Dsc.Tool, ts, t) : List<&2, Dsc.Tool>}
      %Equal.sym(List<&2, Dsc.Tool>, List.drop(&2, Dsc.Tool, List.drop(&2, Dsc.Tool, ts, pos), Nat.sub(t, pos)), List.drop(&2, Dsc.Tool, ts, Nat.add(pos, Nat.sub(t, pos))), cdv.drop2(ts, pos, Nat.sub(t, pos))) : {_ == List.drop(&2, Dsc.Tool, ts, t) : List<&2, Dsc.Tool>}
      %Equal.sym(Nat, Nat.add(pos, Nat.sub(t, pos)), t, LNatB.pu.sub_add(pos, t, eb)) : {List.drop(&2, Dsc.Tool, ts, _) == List.drop(&2, Dsc.Tool, ts, t) : List<&2, Dsc.Tool>}
      {==}
    case False{}:
      {==}

def cdv.sel(b: Bool, x: Dsc.Item, r: List<&2, Dsc.Item>) -> {Dsc.visible.sel(b, x, r) == CodemodeDescribe.shown_at(b, x, r) : List<&2, Dsc.Item>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the walk keeps the tools whose names the set holds: the spec's tools shown
def cdv.vis(xs: List<&2, Dsc.Item>, +ts: List<&2, Dsc.Tool>, -cur: List<&2, Dsc.Tool>, +pos: Nat, +shown: List<&2, String>, ec: {cur == List.drop(&2, Dsc.Tool, ts, pos) : List<&2, Dsc.Tool>}) -> {Dsc.vis(xs, ts, cur, pos, Dsc.nset.of(shown)) == CodemodeDescribe.shown_spec(xs, ts, shown) : List<&2, Dsc.Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +r}:
      match x:
        case Dsc.Item{+t, +c}:
          %Equal.sym(List<&2, Dsc.Tool>, Dsc.vis.here(Nat.is_le(pos, t), cur, ts, pos, t), List.drop(&2, Dsc.Tool, ts, t), cdv.here(Nat.is_le(pos, t), cur, ts, pos, t, {==}, ec)) : {Dsc.visible.sel(Dsc.nset.has(Dsc.nset.of(shown), Dsc.head_name(_)), Dsc.Item{t, c}, Dsc.vis(r, ts, _, t, Dsc.nset.of(shown))) == CodemodeDescribe.shown_at(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          %Equal.sym(String, Dsc.head_name(List.drop(&2, Dsc.Tool, ts, t)), CodemodeDescribe.tool_name_spec(ts, t), cdv.head(ts, t)) : {Dsc.visible.sel(Dsc.nset.has(Dsc.nset.of(shown), _), Dsc.Item{t, c}, Dsc.vis(r, ts, List.drop(&2, Dsc.Tool, ts, t), t, Dsc.nset.of(shown))) == CodemodeDescribe.shown_at(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          %Equal.sym(Bool, Dsc.nset.has(Dsc.nset.of(shown), CodemodeDescribe.tool_name_spec(ts, t)), CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), cdv.of(shown, CodemodeDescribe.tool_name_spec(ts, t))) : {Dsc.visible.sel(_, Dsc.Item{t, c}, Dsc.vis(r, ts, List.drop(&2, Dsc.Tool, ts, t), t, Dsc.nset.of(shown))) == CodemodeDescribe.shown_at(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          %Equal.sym(List<&2, Dsc.Item>, Dsc.vis(r, ts, List.drop(&2, Dsc.Tool, ts, t), t, Dsc.nset.of(shown)), CodemodeDescribe.shown_spec(r, ts, shown), cdv.vis(r, ts, List.drop(&2, Dsc.Tool, ts, t), t, shown, {==})) : {Dsc.visible.sel(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, _) == CodemodeDescribe.shown_at(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown)) : List<&2, Dsc.Item>}
          cdv.sel(CodemodeDescribe.has_name(shown, CodemodeDescribe.tool_name_spec(ts, t)), Dsc.Item{t, c}, CodemodeDescribe.shown_spec(r, ts, shown))
