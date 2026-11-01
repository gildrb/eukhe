# eukhe: lemmas of the decision proofs of area kin: the code's steps are
# the spec's (kp.*), the spec's verdict admits as the spec says (ka.*),
# what an admitted verdict names (kr.*), and the spec's links of two
# trees put one after the other (kb.*)

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ../base/staging.bend as LStg

# The code's steps are the spec's
# -------------------------------

# the code's edge test is the spec's
def kp.has(cs: List<&2, String>, ps: List<&2, String>, +a: String, +b: String) -> {K.has(cs, ps, a, b) == KinSpec.has_edge(cs, ps, a, b) : Bool}:
  match cs ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{p, pt}:
      {==}
    case Con{c, ct} Nil{}:
      {==}
    case Con{+c, +ct} Con{+p, +pt}:
      Equal.cong(Bool, Bool, z => Bool.or(Bool.and(String.eq(c, a), String.eq(p, b)), z), K.has(ct, pt, a, b), KinSpec.has_edge(ct, pt, a, b), kp.has(ct, pt, a, b))

def kp.child(y: Bool) -> {K.decide.down(y) == KinSpec.verdict.child(y) : K.Verdict}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def kp.parent(x: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> {K.decide.up(x, s, t, cs, ps) == KinSpec.verdict.parent(x, s, t, cs, ps) : K.Verdict}:
  match x:
    case True{}:
      {==}
    case False{}:
      %kp.has(cs, ps, t, s) : {K.decide.down(K.has(cs, ps, t, s)) == KinSpec.verdict.child(_) : K.Verdict}
      kp.child(K.has(cs, ps, t, s))

# the code's decision, step by step, is the spec's
def kp.self(e: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> {K.decide.self(e, s, t, cs, ps) == KinSpec.verdict.self(e, s, t, cs, ps) : K.Verdict}:
  match e:
    case True{}:
      {==}
    case False{}:
      %kp.has(cs, ps, s, t) : {K.decide.up(K.has(cs, ps, s, t), s, t, cs, ps) == KinSpec.verdict.parent(_, s, t, cs, ps) : K.Verdict}
      kp.parent(K.has(cs, ps, s, t), s, t, cs, ps)

# Admission in the spec
# ---------------------

def ka.child(y: Bool) -> {Kin.kin_admitted(KinSpec.verdict.child(y)) == y : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def ka.parent(x: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> {Kin.kin_admitted(KinSpec.verdict.parent(x, s, t, cs, ps)) == Bool.or(x, KinSpec.has_edge(cs, ps, t, s)) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      ka.child(KinSpec.has_edge(cs, ps, t, s))

# the spec's verdict admits exactly when the spec admits
def ka.self(e: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> {Kin.kin_admitted(KinSpec.verdict.self(e, s, t, cs, ps)) == Bool.and(Bool.not(e), Bool.or(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s))) : Bool}:
  match e:
    case True{}:
      {==}
    case False{}:
      ka.parent(KinSpec.has_edge(cs, ps, s, t), s, t, cs, ps)

# What an admitted verdict names
# ------------------------------

def kr.If(v: K.Verdict, G: Type) -> Type:
  match v:
    case K.Admit{r}:
      G
    case K.Refuse{f}:
      Unit

# a refusal is no admission
def kr.absurd(-G: Type, -f: K.Refusal, -r: K.Relation, e: {K.Refuse{f} == K.Admit{r} : K.Verdict}) -> G:
  %e : kr.If(_, G)
  Unit{}

def kr.rel_of(v: K.Verdict) -> K.Relation:
  match v:
    case K.Admit{r}:
      r
    case K.Refuse{f}:
      K.Parent{}

def kr.child(y: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>, +r: K.Relation, hy: {KinSpec.has_edge(cs, ps, t, s) == y : Bool}, h: {KinSpec.verdict.child(y) == K.Admit{r} : K.Verdict}) -> {Kin.kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}:
  match y:
    case True{}:
      %Equal.cong(K.Verdict, K.Relation, v => kr.rel_of(v), K.Admit{K.Child{}}, K.Admit{r}, h) : {Kin.kin_rel_holds(_, s, t, cs, ps) == True{} : Bool}
      hy
    case False{}:
      kr.absurd({Kin.kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}, K.NotKin{}, r, h)

def kr.parent(x: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>, +r: K.Relation, hx: {KinSpec.has_edge(cs, ps, s, t) == x : Bool}, h: {KinSpec.verdict.parent(x, s, t, cs, ps) == K.Admit{r} : K.Verdict}) -> {Kin.kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}:
  match x:
    case True{}:
      %Equal.cong(K.Verdict, K.Relation, v => kr.rel_of(v), K.Admit{K.Parent{}}, K.Admit{r}, h) : {Kin.kin_rel_holds(_, s, t, cs, ps) == True{} : Bool}
      hx
    case False{}:
      kr.child(KinSpec.has_edge(cs, ps, t, s), s, t, cs, ps, r, {==}, h)

# an admitted verdict of the spec names an edge that holds
def kr.self(e: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>, +r: K.Relation, h: {KinSpec.verdict.self(e, s, t, cs, ps) == K.Admit{r} : K.Verdict}) -> {Kin.kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}:
  match e:
    case True{}:
      kr.absurd({Kin.kin_rel_holds(r, s, t, cs, ps) == True{} : Bool}, K.SelfMessage{}, r, h)
    case False{}:
      kr.parent(KinSpec.has_edge(cs, ps, s, t), s, t, cs, ps, r, {==}, h)

# Two trees, one after the other
# ------------------------------

def kb.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+k:
      G

# 0 is no successor
def kb.zero_succ(-G: Type, -k: Nat, e: {0n == 1n+k : Nat}) -> G:
  %e : kb.NZ(_, G)
  Unit{}

def kb.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

# columns of one length pair the same way after more columns are put
# after them: the links of A ++ B are A's, then B's
def kb.links_app(ca: List<&2, String>, pa: List<&2, String>, -cb: List<&2, String>, -pb: List<&2, String>, hl: {List.length(&2, String, ca) == List.length(&2, String, pa) : Nat}) -> {KinSpec.links(List.append(&2, String, ca, cb), List.append(&2, String, pa, pb)) == List.append(&2, KinSpec.Link, KinSpec.links(ca, pa), KinSpec.links(cb, pb)) : List<&2, KinSpec.Link>}:
  match ca pa:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{p, pt}:
      kb.zero_succ({KinSpec.links(cb, List.append(&2, String, p <> pt, pb)) == KinSpec.links(cb, pb) : List<&2, KinSpec.Link>}, List.length(&2, String, pt), hl)
    case Con{c, ct} Nil{}:
      kb.zero_succ({KinSpec.links(List.append(&2, String, c <> ct, cb), pb) == KinSpec.links(cb, pb) : List<&2, KinSpec.Link>}, List.length(&2, String, ct), Equal.sym(Nat, 1n+List.length(&2, String, ct), 0n, hl))
    case Con{+c, +ct} Con{+p, +pt}:
      Equal.cong(List<&2, KinSpec.Link>, List<&2, KinSpec.Link>, z => KinSpec.Link{c, p} <> z, KinSpec.links(List.append(&2, String, ct, cb), List.append(&2, String, pt, pb)), List.append(&2, KinSpec.Link, KinSpec.links(ct, pt), KinSpec.links(cb, pb)), kb.links_app(ct, pt, cb, pb, Equal.cong(Nat, Nat, z => kb.pred(z), 1n+List.length(&2, String, ct), 1n+List.length(&2, String, pt), hl)))

def kb.or_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a link of xs ++ ys is a link of xs or of ys
def kb.linked_app(xs: List<&2, KinSpec.Link>, -ys: List<&2, KinSpec.Link>, +c: String, +p: String) -> {KinSpec.linked(List.append(&2, KinSpec.Link, xs, ys), c, p) == Bool.or(KinSpec.linked(xs, c, p), KinSpec.linked(ys, c, p)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+l, +t}:
      %Equal.sym(Bool, KinSpec.linked(List.append(&2, KinSpec.Link, t, ys), c, p), Bool.or(KinSpec.linked(t, c, p), KinSpec.linked(ys, c, p)), kb.linked_app(t, ys, c, p)) : {Bool.or(KinSpec.link_is(l, c, p), _) == Bool.or(Bool.or(KinSpec.link_is(l, c, p), KinSpec.linked(t, c, p)), KinSpec.linked(ys, c, p)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(KinSpec.link_is(l, c, p), KinSpec.linked(t, c, p)), KinSpec.linked(ys, c, p)), Bool.or(KinSpec.link_is(l, c, p), Bool.or(KinSpec.linked(t, c, p), KinSpec.linked(ys, c, p))), kb.or_assoc(KinSpec.link_is(l, c, p), KinSpec.linked(t, c, p), KinSpec.linked(ys, c, p)))

def kb.or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def kb.or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LStg.stg.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# no link reaches a parent the parents' column never names
def kb.no_parent(cs: List<&2, String>, ps: List<&2, String>, +c: String, +p: String, h: {KinSpec.mentions(ps, p) == False{} : Bool}) -> {KinSpec.linked(KinSpec.links(cs, ps), c, p) == False{} : Bool}:
  match cs ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      +hh = h
      %Equal.sym(Bool, String.eq(y, p), False{}, kb.or_false_l(String.eq(y, p), KinSpec.mentions(yt, p), hh)) : {Bool.or(Bool.and(String.eq(x, c), _), KinSpec.linked(KinSpec.links(xt, yt), c, p)) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(String.eq(x, c), False{}), False{}, LStg.stg.and_false(String.eq(x, c))) : {Bool.or(_, KinSpec.linked(KinSpec.links(xt, yt), c, p)) == False{} : Bool}
      kb.no_parent(xt, yt, c, p, kb.or_false_r(String.eq(y, p), KinSpec.mentions(yt, p), hh))

# no link leaves a child the children's column never names
def kb.no_child(cs: List<&2, String>, ps: List<&2, String>, +c: String, +p: String, h: {KinSpec.mentions(cs, c) == False{} : Bool}) -> {KinSpec.linked(KinSpec.links(cs, ps), c, p) == False{} : Bool}:
  match cs ps:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      {==}
    case Con{x, xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      +hh = h
      %Equal.sym(Bool, String.eq(x, c), False{}, kb.or_false_l(String.eq(x, c), KinSpec.mentions(xt, c), hh)) : {Bool.or(Bool.and(_, String.eq(y, p)), KinSpec.linked(KinSpec.links(xt, yt), c, p)) == False{} : Bool}
      kb.no_child(xt, yt, c, p, kb.or_false_r(String.eq(x, c), KinSpec.mentions(xt, c), hh))

# no edge of A ++ B from c to p when neither A nor B has one
def kb.no_edge(+ca: List<&2, String>, +pa: List<&2, String>, +cb: List<&2, String>, +pb: List<&2, String>, +c: String, +p: String, hl: {List.length(&2, String, ca) == List.length(&2, String, pa) : Nat}, ha: {KinSpec.linked(KinSpec.links(ca, pa), c, p) == False{} : Bool}, hb: {KinSpec.linked(KinSpec.links(cb, pb), c, p) == False{} : Bool}) -> {KinSpec.has_edge(List.append(&2, String, ca, cb), List.append(&2, String, pa, pb), c, p) == False{} : Bool}:
  +la = KinSpec.links(ca, pa)
  +lb = KinSpec.links(cb, pb)
  %Equal.sym(List<&2, KinSpec.Link>, KinSpec.links(List.append(&2, String, ca, cb), List.append(&2, String, pa, pb)), List.append(&2, KinSpec.Link, la, lb), kb.links_app(ca, pa, cb, pb, hl)) : {KinSpec.linked(_, c, p) == False{} : Bool}
  %Equal.sym(Bool, KinSpec.linked(List.append(&2, KinSpec.Link, la, lb), c, p), Bool.or(KinSpec.linked(la, c, p), KinSpec.linked(lb, c, p)), kb.linked_app(la, lb, c, p)) : {_ == False{} : Bool}
  %Equal.sym(Bool, KinSpec.linked(la, c, p), False{}, ha) : {Bool.or(_, KinSpec.linked(lb, c, p)) == False{} : Bool}
  hb
