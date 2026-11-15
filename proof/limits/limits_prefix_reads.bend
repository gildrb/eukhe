# eukhe: the proof of LAW limits_prefix_reads
#
# PROOF: the code reads the message char by char; the spec word by word.
# The opener is the code's first word (lpr.word, lpr.opener_at). From
# there on, by induction on the words (lpr.main): a gap reads nothing
# (lpr.gapskip), nor do a word's chars until a gap or the end closes it
# (lpr.inword, lpr.close_at); the closed word is the word as typed
# (lpr.word), its kind the spec's (lpr.kind: fold, folded, the names, the
# cut at `=`, the keys, the value read and the keys given are the spec's);
# each kind then reads on as the spec does (lpr.step_kind), the presets and
# pairs so far in front (lpr.pre).

import Base
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../autoresearch/base/line.bend as ALine

# Chars
# -----

def lpr.fsp(b: Bool, c: Char) -> {L.fold.space(b, c) == S.fold.space(b, c) : Char}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lpr.fold_in(lo: Bool, hi: Bool, +x: U32, +c: Char) -> {L.fold.in(Bool.and(lo, hi), x, c) == S.fold.wide(lo, hi, x, c) : Char}:
  match lo hi:
    case True{} True{}:
      {==}
    case True{} False{}:
      lpr.fsp(U32.is_eq(x, 12288), c)
    case False{} True{}:
      lpr.fsp(U32.is_eq(x, 12288), c)
    case False{} False{}:
      lpr.fsp(U32.is_eq(x, 12288), c)

# the code's fold is the spec's
def lpr.fold(c: Char) -> {L.fold(c) == S.fold(c) : Char}:
  match c:
    case Chr{+x}:
      lpr.fold_in(U32.is_le(65281, x), U32.is_le(x, 65374), x, Chr{x})

def lpr.code_of(d: Char) -> {L.code.of(d) == S.code(d) : Nat}:
  match d:
    case Chr{x}:
      {==}

# the code's folded code is the spec's
def lpr.code(+c: Char) -> {L.code(c) == S.code(S.fold(c)) : Nat}:
  %Equal.sym(Char, L.fold(c), S.fold(c), lpr.fold(c)) : {L.code.of(_) == S.code(S.fold(c)) : Nat}
  lpr.code_of(S.fold(c))

# the code's space is the spec's
def lpr.space(+c: Char) -> {L.is_space(c) == S.space(c) : Bool}:
  %Equal.sym(Nat, L.code(c), S.code(S.fold(c)), lpr.code(c)) : {L.is_space.n(_) == S.space(c) : Bool}
  {==}

def lpr.sp_t(+c: Char, h: {S.space(c) == True{} : Bool}) -> {True{} == L.is_space(c) : Bool}:
  Equal.trans(Bool, True{}, S.space(c), L.is_space(c), Equal.sym(Bool, S.space(c), True{}, h), Equal.sym(Bool, L.is_space(c), S.space(c), lpr.space(c)))

def lpr.sp_f(+c: Char, h: {S.space(c) == False{} : Bool}) -> {False{} == L.is_space(c) : Bool}:
  Equal.trans(Bool, False{}, S.space(c), L.is_space(c), Equal.sym(Bool, S.space(c), False{}, h), Equal.sym(Bool, L.is_space(c), S.space(c), lpr.space(c)))

def lpr.folded(s: String) -> {L.folded(s) == S.folded(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Char, L.fold(c), S.fold(c), lpr.fold(c)) : {SCon{_, L.folded(t)} == SCon{S.fold(c), S.folded(t)} : String}
      %Equal.sym(String, L.folded(t), S.folded(t), lpr.folded(t)) : {SCon{S.fold(c), _} == SCon{S.fold(c), S.folded(t)} : String}
      {==}

# Words
# -----

def lpr.first(b: Bool, i: Nat, x: Maybe<&2, Nat>) -> {L.named.at(b, i, x) == S.first(b, i, x) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def lpr.named(+w: String, ns: List<&2, String>, +i: Nat) -> {L.named(w, ns, i) == S.named(w, ns, i) : Maybe<&2, Nat>}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +t}:
      %Equal.sym(Maybe<&2, Nat>, L.named(w, t, 1n+i), S.named(w, t, 1n+i), lpr.named(w, t, 1n+i)) : {L.named.at(L.same(w, n), i, _) == S.first(S.same(w, n), i, S.named(w, t, 1n+i)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, L.same(w, n), S.same(w, n), LB.lmb.same(w, n)) : {L.named.at(_, i, S.named(w, t, 1n+i)) == S.first(S.same(w, n), i, S.named(w, t, 1n+i)) : Maybe<&2, Nat>}
      lpr.first(S.same(w, n), i, S.named(w, t, 1n+i))

def lpr.cut_at(b: Bool, c: Char, t: String, m: Maybe<&2, L.Cut>) -> {L.split.at(b, c, t, m) == S.cut.at(b, c, t, m) : Maybe<&2, L.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match m:
        case None{}:
          {==}
        case Some{L.Cut{x, y}}:
          {==}

def lpr.cut(s: String) -> {L.split(s) == S.eq_cut(s) : Maybe<&2, L.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, L.Cut>, L.split(t), S.eq_cut(t), lpr.cut(t)) : {L.split.at(Nat.is_eq(L.code(c), 61n), c, t, _) == S.cut.at(Nat.is_eq(S.code(S.fold(c)), 61n), c, t, S.eq_cut(t)) : Maybe<&2, L.Cut>}
      %Equal.sym(Nat, L.code(c), S.code(S.fold(c)), lpr.code(c)) : {L.split.at(Nat.is_eq(_, 61n), c, t, S.eq_cut(t)) == S.cut.at(Nat.is_eq(S.code(S.fold(c)), 61n), c, t, S.eq_cut(t)) : Maybe<&2, L.Cut>}
      lpr.cut_at(Nat.is_eq(S.code(S.fold(c)), 61n), c, t, S.eq_cut(t))

def lpr.key_is(b: Bool, k: L.Key, -m1: Maybe<&2, L.Key>, -m2: Maybe<&2, L.Key>, e: {m1 == m2 : Maybe<&2, L.Key>}) -> {L.key.is(b, k, m1) == S.key.at(b, k, m2) : Maybe<&2, L.Key>}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

def lpr.key(+k: String) -> {L.key(k) == S.key(k) : Maybe<&2, L.Key>}:
  %Equal.sym(Bool, L.same(k, "cost"), S.same(k, "cost"), LB.lmb.same(k, "cost")) : {L.key.is(_, L.KCost{}, L.key.is(L.same(k, "tokens"), L.KTok{}, L.key.is(L.same(k, "time"), L.KTime{}, L.key.is(L.same(k, "calls"), L.KCalls{}, L.key.is(L.same(k, "requests"), L.KReqs{}, None{}))))) == S.key(k) : Maybe<&2, L.Key>}
  %Equal.sym(Bool, L.same(k, "tokens"), S.same(k, "tokens"), LB.lmb.same(k, "tokens")) : {L.key.is(S.same(k, "cost"), L.KCost{}, L.key.is(_, L.KTok{}, L.key.is(L.same(k, "time"), L.KTime{}, L.key.is(L.same(k, "calls"), L.KCalls{}, L.key.is(L.same(k, "requests"), L.KReqs{}, None{}))))) == S.key(k) : Maybe<&2, L.Key>}
  %Equal.sym(Bool, L.same(k, "time"), S.same(k, "time"), LB.lmb.same(k, "time")) : {L.key.is(S.same(k, "cost"), L.KCost{}, L.key.is(S.same(k, "tokens"), L.KTok{}, L.key.is(_, L.KTime{}, L.key.is(L.same(k, "calls"), L.KCalls{}, L.key.is(L.same(k, "requests"), L.KReqs{}, None{}))))) == S.key(k) : Maybe<&2, L.Key>}
  %Equal.sym(Bool, L.same(k, "calls"), S.same(k, "calls"), LB.lmb.same(k, "calls")) : {L.key.is(S.same(k, "cost"), L.KCost{}, L.key.is(S.same(k, "tokens"), L.KTok{}, L.key.is(S.same(k, "time"), L.KTime{}, L.key.is(_, L.KCalls{}, L.key.is(L.same(k, "requests"), L.KReqs{}, None{}))))) == S.key(k) : Maybe<&2, L.Key>}
  %Equal.sym(Bool, L.same(k, "requests"), S.same(k, "requests"), LB.lmb.same(k, "requests")) : {L.key.is(S.same(k, "cost"), L.KCost{}, L.key.is(S.same(k, "tokens"), L.KTok{}, L.key.is(S.same(k, "time"), L.KTime{}, L.key.is(S.same(k, "calls"), L.KCalls{}, L.key.is(_, L.KReqs{}, None{}))))) == S.key(k) : Maybe<&2, L.Key>}
  +m5 = {None{} : Maybe<&2, L.Key>}
  +m4 = S.key.at(S.same(k, "requests"), L.KReqs{}, m5)
  +m3 = S.key.at(S.same(k, "calls"), L.KCalls{}, m4)
  +m2 = S.key.at(S.same(k, "time"), L.KTime{}, m3)
  +m1 = S.key.at(S.same(k, "tokens"), L.KTok{}, m2)
  lpr.key_is(S.same(k, "cost"), L.KCost{}, L.key.is(S.same(k, "tokens"), L.KTok{}, L.key.is(S.same(k, "time"), L.KTime{}, L.key.is(S.same(k, "calls"), L.KCalls{}, L.key.is(S.same(k, "requests"), L.KReqs{}, m5)))), m1,
    lpr.key_is(S.same(k, "tokens"), L.KTok{}, L.key.is(S.same(k, "time"), L.KTime{}, L.key.is(S.same(k, "calls"), L.KCalls{}, L.key.is(S.same(k, "requests"), L.KReqs{}, m5))), m2,
      lpr.key_is(S.same(k, "time"), L.KTime{}, L.key.is(S.same(k, "calls"), L.KCalls{}, L.key.is(S.same(k, "requests"), L.KReqs{}, m5)), m3,
        lpr.key_is(S.same(k, "calls"), L.KCalls{}, L.key.is(S.same(k, "requests"), L.KReqs{}, m5), m4,
          lpr.key_is(S.same(k, "requests"), L.KReqs{}, m5, m5, {==})))))

def lpr.point(b: Bool, +c: Char) -> {L.decimal.at(b, c) == S.point(b, c) : Char}:
  match b:
    case True{}:
      {==}
    case False{}:
      lpr.fold(c)

def lpr.decimal(s: String) -> {L.decimal(s) == S.decimal(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, L.decimal(t), S.decimal(t), lpr.decimal(t)) : {SCon{L.decimal.at(Nat.is_eq(L.code(c), 44n), c), _} == SCon{S.point(Nat.is_eq(S.code(S.fold(c)), 44n), c), S.decimal(t)} : String}
      %Equal.sym(Nat, L.code(c), S.code(S.fold(c)), lpr.code(c)) : {SCon{L.decimal.at(Nat.is_eq(_, 44n), c), S.decimal(t)} == SCon{S.point(Nat.is_eq(S.code(S.fold(c)), 44n), c), S.decimal(t)} : String}
      %Equal.sym(Char, L.decimal.at(Nat.is_eq(S.code(S.fold(c)), 44n), c), S.point(Nat.is_eq(S.code(S.fold(c)), 44n), c), lpr.point(Nat.is_eq(S.code(S.fold(c)), 44n), c)) : {SCon{_, S.decimal(t)} == SCon{S.point(Nat.is_eq(S.code(S.fold(c)), 44n), c), S.decimal(t)} : String}
      {==}

def lpr.key_eq(a: L.Key, b: L.Key) -> {L.key_is(a, b) == Nat.is_eq(S.key_tag(a), S.key_tag(b)) : Bool}:
  match a b:
    case L.KCost{} L.KCost{}:
      {==}
    case L.KCost{} L.KTok{}:
      {==}
    case L.KCost{} L.KTime{}:
      {==}
    case L.KCost{} L.KCalls{}:
      {==}
    case L.KCost{} L.KReqs{}:
      {==}
    case L.KTok{} L.KCost{}:
      {==}
    case L.KTok{} L.KTok{}:
      {==}
    case L.KTok{} L.KTime{}:
      {==}
    case L.KTok{} L.KCalls{}:
      {==}
    case L.KTok{} L.KReqs{}:
      {==}
    case L.KTime{} L.KCost{}:
      {==}
    case L.KTime{} L.KTok{}:
      {==}
    case L.KTime{} L.KTime{}:
      {==}
    case L.KTime{} L.KCalls{}:
      {==}
    case L.KTime{} L.KReqs{}:
      {==}
    case L.KCalls{} L.KCost{}:
      {==}
    case L.KCalls{} L.KTok{}:
      {==}
    case L.KCalls{} L.KTime{}:
      {==}
    case L.KCalls{} L.KCalls{}:
      {==}
    case L.KCalls{} L.KReqs{}:
      {==}
    case L.KReqs{} L.KCost{}:
      {==}
    case L.KReqs{} L.KTok{}:
      {==}
    case L.KReqs{} L.KTime{}:
      {==}
    case L.KReqs{} L.KCalls{}:
      {==}
    case L.KReqs{} L.KReqs{}:
      {==}

def lpr.given(+k: L.Key, ps: List<&2, L.KV>) -> {L.given(k, ps) == S.keyed(k, ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{L.KV{+kk, v}, +t}:
      %Equal.sym(Bool, L.given(k, t), S.keyed(k, t), lpr.given(k, t)) : {Bool.or(L.key_is(kk, k), _) == Bool.or(Nat.is_eq(S.key_tag(kk), S.key_tag(k)), S.keyed(k, t)) : Bool}
      %Equal.sym(Bool, L.key_is(kk, k), Nat.is_eq(S.key_tag(kk), S.key_tag(k)), lpr.key_eq(kk, k)) : {Bool.or(_, S.keyed(k, t)) == Bool.or(Nat.is_eq(S.key_tag(kk), S.key_tag(k)), S.keyed(k, t)) : Bool}
      {==}

def lpr.kind_pair(b: Bool, k: L.Key, +v: String) -> {L.pair.at(b, k, v) == S.word_kind.pair(b, k, v) : L.Wd}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, L.decimal(v), S.decimal(v), lpr.decimal(v)) : {L.WPair{L.KV{k, _}} == L.WPair{L.KV{k, S.decimal(v)}} : L.Wd}
      {==}

def lpr.kind_key(m: Maybe<&2, L.Key>, +v: String, +ps: List<&2, L.KV>) -> {L.word_kv.key(m, v, ps) == S.word_kind.key(m, v, ps) : L.Wd}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      %Equal.sym(Bool, L.given(k, ps), S.keyed(k, ps), lpr.given(k, ps)) : {L.pair.at(Bool.or(String.is_empty(v), _), k, v) == S.word_kind.pair(Bool.or(String.is_empty(v), S.keyed(k, ps)), k, v) : L.Wd}
      lpr.kind_pair(Bool.or(String.is_empty(v), S.keyed(k, ps)), k, v)

def lpr.kind_kv(m: Maybe<&2, L.Cut>, +ps: List<&2, L.KV>) -> {L.word_kv(m, ps) == S.word_kind.kv(m, ps) : L.Wd}:
  match m:
    case None{}:
      {==}
    case Some{L.Cut{+k, +v}}:
      %Equal.sym(String, L.folded(k), S.folded(k), lpr.folded(k)) : {L.word_kv.key(L.key(_), v, ps) == S.word_kind.key(S.key(S.folded(k)), v, ps) : L.Wd}
      %Equal.sym(Maybe<&2, L.Key>, L.key(S.folded(k)), S.key(S.folded(k)), lpr.key(S.folded(k))) : {L.word_kv.key(_, v, ps) == S.word_kind.key(S.key(S.folded(k)), v, ps) : L.Wd}
      lpr.kind_key(S.key(S.folded(k)), v, ps)

def lpr.kind_at(m: Maybe<&2, Nat>, +w: String, +ps: List<&2, L.KV>) -> {L.classify.at(m, w, ps) == S.word_kind.at(m, w, ps) : L.Wd}:
  match m:
    case Some{i}:
      {==}
    case None{}:
      %Equal.sym(Maybe<&2, L.Cut>, L.split(w), S.eq_cut(w), lpr.cut(w)) : {L.word_kv(_, ps) == S.word_kind.kv(S.eq_cut(w), ps) : L.Wd}
      lpr.kind_kv(S.eq_cut(w), ps)

# the code's word kind is the spec's
def lpr.kind(+w: String, +ns: List<&2, String>, +ps: List<&2, L.KV>) -> {L.classify(w, ns, ps) == S.word_kind(w, ns, ps) : L.Wd}:
  %Equal.sym(String, L.folded(w), S.folded(w), lpr.folded(w)) : {L.classify.at(L.named(_, ns, 0n), w, ps) == S.word_kind(w, ns, ps) : L.Wd}
  %Equal.sym(Maybe<&2, Nat>, L.named(S.folded(w), ns, 0n), S.named(S.folded(w), ns, 0n), lpr.named(S.folded(w), ns, 0n)) : {L.classify.at(_, w, ps) == S.word_kind(w, ns, ps) : L.Wd}
  lpr.kind_at(S.named(S.folded(w), ns, 0n), w, ps)

# The reading
# -----------

# s is empty or opens with a space
def lpr.at_gap(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      S.space(c)

# what a closed word reads on to over the text R after it
def lpr.cont(x: L.Closed, R: String, ns: List<&2, String>) -> L.Prefix:
  match x:
    case L.Next{ks, ps}:
      L.go(R, L.Gap{ks, ps}, ns)
    case L.Stop{p}:
      p

# a prefix read after the presets ks and the pairs ps
def lpr.pre(ks: List<&2, Nat>, ps: List<&2, L.KV>, p: L.Prefix) -> L.Prefix:
  match p:
    case L.Read{a, b, r}:
      L.Read{List.append(&2, Nat, ks, a), List.append(&2, L.KV, ps, b), r}
    case L.Refused{w}:
      L.Refused{w}

# the presets after a word of kind k
def lpr.ks_after(k: L.Wd, ks: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case L.WPreset{i}:
      List.append(&2, Nat, ks, [i])
    case L.WPair{p}:
      ks
    case L.WBad{}:
      ks
    case L.WEnd{}:
      ks

def lpr.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(List<&2, A>, List.append(&2, A, t, Nil{}), t, lpr.app_nil(A, t)) : {h <> _ == h <> t : List<&2, A>}
      {==}

def lpr.app_one(-A: Data, xs: List<&2, A>, -i: A, -a: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, [i]), a) == List.append(&2, A, xs, i <> a) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, t, [i]), a), List.append(&2, A, t, i <> a), lpr.app_one(A, t, i, a)) : {h <> _ == h <> List.append(&2, A, t, i <> a) : List<&2, A>}
      {==}

def lpr.pre_nil(p: L.Prefix) -> {lpr.pre(Nil{}, Nil{}, p) == p : L.Prefix}:
  match p:
    case L.Read{a, b, r}:
      {==}
    case L.Refused{w}:
      {==}

def lpr.pre_k(+ks: List<&2, Nat>, ps: List<&2, L.KV>, +i: Nat, p: L.Prefix) -> {lpr.pre(List.append(&2, Nat, ks, [i]), ps, p) == lpr.pre(ks, ps, S.with_preset(i, p)) : L.Prefix}:
  match p:
    case L.Read{+a, b, r}:
      %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, ks, [i]), a), List.append(&2, Nat, ks, i <> a), lpr.app_one(Nat, ks, i, a)) : {L.Read{_, List.append(&2, L.KV, ps, b), r} == L.Read{List.append(&2, Nat, ks, i <> a), List.append(&2, L.KV, ps, b), r} : L.Prefix}
      {==}
    case L.Refused{w}:
      {==}

def lpr.pre_p(ks: List<&2, Nat>, +ps: List<&2, L.KV>, +kv: L.KV, p: L.Prefix) -> {lpr.pre(ks, List.append(&2, L.KV, ps, [kv]), p) == lpr.pre(ks, ps, S.with_pair(kv, p)) : L.Prefix}:
  match p:
    case L.Read{a, +b, r}:
      %Equal.sym(List<&2, L.KV>, List.append(&2, L.KV, List.append(&2, L.KV, ps, [kv]), b), List.append(&2, L.KV, ps, kv <> b), lpr.app_one(L.KV, ps, kv, b)) : {L.Read{List.append(&2, Nat, ks, a), _, r} == L.Read{List.append(&2, Nat, ks, a), List.append(&2, L.KV, ps, kv <> b), r} : L.Prefix}
      {==}
    case L.Refused{w}:
      {==}

# a reading done stays done
def lpr.fin(u: String, -p: L.Prefix, +ns: List<&2, String>) -> {L.go(u, L.Fin{p}, ns) == p : L.Prefix}:
  match u:
    case SNil{}:
      {==}
    case SCon{c, t}:
      lpr.fin(t, p, ns)

# spaces between words read nothing
def lpr.gapskip(g: String, +x: String, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, +ns: List<&2, String>, h: {S.spaces(g) == True{} : Bool}) -> {L.go(String.append(g, x), L.Gap{ks, ps}, ns) == L.go(x, L.Gap{ks, ps}, ns) : L.Prefix}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +h0 = h
      %lpr.sp_t(c, LB.lmb.and_l(S.space(c), S.spaces(u), h0)) : {L.go(String.append(u, x), L.step.gap(_, SCon{c, String.append(u, x)}, ks, ps), ns) == L.go(x, L.Gap{ks, ps}, ns) : L.Prefix}
      lpr.gapskip(u, x, ks, ps, ns, LB.lmb.and_r(S.space(c), S.spaces(u), h0))

# trailing spaces end the reading
def lpr.trail(t: String, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, +ns: List<&2, String>, h: {S.spaces(t) == True{} : Bool}) -> {L.go(t, L.Gap{ks, ps}, ns) == L.Read{ks, ps, ""} : L.Prefix}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +h0 = h
      %lpr.sp_t(c, LB.lmb.and_l(S.space(c), S.spaces(u), h0)) : {L.go(u, L.step.gap(_, SCon{c, u}, ks, ps), ns) == L.Read{ks, ps, ""} : L.Prefix}
      lpr.trail(u, ks, ps, ns, LB.lmb.and_r(S.space(c), S.spaces(u), h0))

# the chars of a word read nothing until it ends
def lpr.inword(w: String, +R: String, +at: String, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, +ns: List<&2, String>, h: {S.dense(w) == True{} : Bool}) -> {L.go(String.append(w, R), L.In{at, ks, ps}, ns) == L.go(R, L.In{at, ks, ps}, ns) : L.Prefix}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +h0 = h
      %lpr.sp_f(c, LB.lmb.not_t(S.space(c), LB.lmb.and_l(Bool.not(S.space(c)), S.dense(u), h0))) : {L.go(String.append(u, R), L.step.in(_, at, ns, ks, ps), ns) == L.go(R, L.In{at, ks, ps}, ns) : L.Prefix}
      lpr.inword(u, R, at, ks, ps, ns, LB.lmb.and_r(Bool.not(S.space(c)), S.dense(u), h0))

def lpr.ended(x: L.Closed, +ns: List<&2, String>) -> {L.ended.closed(x) == lpr.cont(x, SNil{}, ns) : L.Prefix}:
  match x:
    case L.Next{ks, ps}:
      {==}
    case L.Stop{p}:
      {==}

def lpr.cont_cons(x: L.Closed, +c: Char, +u: String, +ns: List<&2, String>, hc: {S.space(c) == True{} : Bool}) -> {L.go(u, L.step.next(x), ns) == lpr.cont(x, SCon{c, u}, ns) : L.Prefix}:
  match x:
    case L.Next{+ks, +ps}:
      %lpr.sp_t(c, hc) : {L.go(u, L.Gap{ks, ps}, ns) == L.go(u, L.step.gap(_, SCon{c, u}, ks, ps), ns) : L.Prefix}
      {==}
    case L.Stop{+p}:
      lpr.fin(u, p, ns)

# a word ends at a gap or at the end of the text
def lpr.close_at(R: String, +at: String, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, +ns: List<&2, String>, h: {lpr.at_gap(R) == True{} : Bool}) -> {L.go(R, L.In{at, ks, ps}, ns) == lpr.cont(L.close(at, ns, ks, ps), R, ns) : L.Prefix}:
  match R:
    case SNil{}:
      lpr.ended(L.close(at, ns, ks, ps), ns)
    case SCon{+c, +u}:
      +h0 = h
      %lpr.sp_t(c, h0) : {L.go(u, L.step.in(_, at, ns, ks, ps), ns) == lpr.cont(L.close(at, ns, ks, ps), SCon{c, u}, ns) : L.Prefix}
      lpr.cont_cons(L.close(at, ns, ks, ps), c, u, ns, h0)

def lpr.word_end(y: String, hy: {lpr.at_gap(y) == True{} : Bool}) -> {L.word(y) == L.Cut{SNil{}, y} : L.Cut}:
  match y:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      %lpr.sp_t(c, hy) : {L.word.at(_, c, u, L.word(u)) == L.Cut{SNil{}, SCon{c, u}} : L.Cut}
      {==}

# the word of a text that is a word w then a gap or the end
def lpr.word(w: String, +y: String, hw: {S.dense(w) == True{} : Bool}, hy: {lpr.at_gap(y) == True{} : Bool}) -> {L.word(String.append(w, y)) == L.Cut{w, y} : L.Cut}:
  match w:
    case SNil{}:
      lpr.word_end(y, hy)
    case SCon{+c, +u}:
      +h0 = hw
      %lpr.sp_f(c, LB.lmb.not_t(S.space(c), LB.lmb.and_l(Bool.not(S.space(c)), S.dense(u), h0))) : {L.word.at(_, c, String.append(u, y), L.word(String.append(u, y))) == L.Cut{SCon{c, u}, y} : L.Cut}
      %Equal.sym(L.Cut, L.word(String.append(u, y)), L.Cut{u, y}, lpr.word(u, y, LB.lmb.and_r(Bool.not(S.space(c)), S.dense(u), h0), hy)) : {L.word.cons(c, _) == L.Cut{SCon{c, u}, y} : L.Cut}
      {==}

def lpr.gap_spaces(g: String, h: {S.gap(g) == True{} : Bool}) -> {S.spaces(g) == True{} : Bool}:
  match g:
    case SNil{}:
      LB.lmb.absurd_ft({S.spaces(SNil{}) == True{} : Bool}, h)
    case SCon{c, u}:
      h

def lpr.at_trail(t: String, ht: {S.spaces(t) == True{} : Bool}) -> {lpr.at_gap(t) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      LB.lmb.and_l(S.space(c), S.spaces(u), ht)

def lpr.at_gap_app(g: String, -y: String, h: {S.gap(g) == True{} : Bool}) -> {lpr.at_gap(String.append(g, y)) == True{} : Bool}:
  match g:
    case SNil{}:
      LB.lmb.absurd_ft({lpr.at_gap(y) == True{} : Bool}, h)
    case SCon{+c, +u}:
      LB.lmb.and_l(S.space(c), S.spaces(u), h)

# the text after a word of the message opens with a gap or is the end
def lpr.at_spell(xs: List<&2, S.Item>, +t: String, hx: {S.items(xs) == True{} : Bool}, ht: {S.spaces(t) == True{} : Bool}) -> {lpr.at_gap(S.spell(xs, t)) == True{} : Bool}:
  match xs:
    case Nil{}:
      lpr.at_trail(t, ht)
    case Con{x, rest}:
      match x:
        case S.Item{+g, +w}:
          lpr.at_gap_app(g, String.append(w, S.spell(rest, t)), LB.lmb.and_l(S.gap(g), Bool.and(S.solid(w), S.items(rest)), hx))

# a word's kind decides how the reading goes on
def lpr.step_kind(k: L.Wd, +w: String, +R: String, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, +ns: List<&2, String>, +t: String, +rest: List<&2, S.Item>, ih: {L.go(R, L.Gap{lpr.ks_after(k, ks), S.after(k, ps)}, ns) == lpr.pre(lpr.ks_after(k, ks), S.after(k, ps), S.prefix_of(rest, t, ns, S.after(k, ps))) : L.Prefix}) -> {lpr.cont(L.close.on(k, w, String.append(w, R), ks, ps), R, ns) == lpr.pre(ks, ps, S.prefix_of.at(k, w, R, S.prefix_of(rest, t, ns, S.after(k, ps)))) : L.Prefix}:
  match k:
    case L.WPreset{+i}:
      Equal.trans(L.Prefix, L.go(R, L.Gap{List.append(&2, Nat, ks, [i]), ps}, ns), lpr.pre(List.append(&2, Nat, ks, [i]), ps, S.prefix_of(rest, t, ns, ps)), lpr.pre(ks, ps, S.with_preset(i, S.prefix_of(rest, t, ns, ps))), ih, lpr.pre_k(ks, ps, i, S.prefix_of(rest, t, ns, ps)))
    case L.WPair{+p}:
      Equal.trans(L.Prefix, L.go(R, L.Gap{ks, List.append(&2, L.KV, ps, [p])}, ns), lpr.pre(ks, List.append(&2, L.KV, ps, [p]), S.prefix_of(rest, t, ns, List.append(&2, L.KV, ps, [p]))), lpr.pre(ks, ps, S.with_pair(p, S.prefix_of(rest, t, ns, List.append(&2, L.KV, ps, [p])))), ih, lpr.pre_p(ks, ps, p, S.prefix_of(rest, t, ns, List.append(&2, L.KV, ps, [p]))))
    case L.WBad{}:
      {==}
    case L.WEnd{}:
      %lpr.app_nil(Nat, ks) : {L.Read{_, ps, String.append(w, R)} == L.Read{List.append(&2, Nat, ks, Nil{}), List.append(&2, L.KV, ps, Nil{}), String.append(w, R)} : L.Prefix}
      %lpr.app_nil(L.KV, ps) : {L.Read{List.append(&2, Nat, ks, Nil{}), _, String.append(w, R)} == L.Read{List.append(&2, Nat, ks, Nil{}), List.append(&2, L.KV, ps, Nil{}), String.append(w, R)} : L.Prefix}
      {==}

# the reading of the words of a message, from the presets ks and pairs ps
# on, is the spec's reading of them after ks and ps
def lpr.main(xs: List<&2, S.Item>, +t: String, +ns: List<&2, String>, +ks: List<&2, Nat>, +ps: List<&2, L.KV>, hx: {S.items(xs) == True{} : Bool}, ht: {S.spaces(t) == True{} : Bool}) -> {L.go(S.spell(xs, t), L.Gap{ks, ps}, ns) == lpr.pre(ks, ps, S.prefix_of(xs, t, ns, ps)) : L.Prefix}:
  match xs:
    case Nil{}:
      %Equal.sym(L.Prefix, L.go(t, L.Gap{ks, ps}, ns), L.Read{ks, ps, ""}, lpr.trail(t, ks, ps, ns, ht)) : {_ == lpr.pre(ks, ps, L.Read{Nil{}, Nil{}, ""}) : L.Prefix}
      %lpr.app_nil(Nat, ks) : {L.Read{_, ps, ""} == L.Read{List.append(&2, Nat, ks, Nil{}), List.append(&2, L.KV, ps, Nil{}), ""} : L.Prefix}
      %lpr.app_nil(L.KV, ps) : {L.Read{List.append(&2, Nat, ks, Nil{}), _, ""} == L.Read{List.append(&2, Nat, ks, Nil{}), List.append(&2, L.KV, ps, Nil{}), ""} : L.Prefix}
      {==}
    case Con{x, +rest}:
      match x:
        case S.Item{+g, w}:
          match w:
            case SNil{}:
              LB.lmb.absurd_ft({L.go(S.spell(Con{S.Item{g, SNil{}}, rest}, t), L.Gap{ks, ps}, ns) == lpr.pre(ks, ps, S.prefix_of(Con{S.Item{g, SNil{}}, rest}, t, ns, ps)) : L.Prefix}, LB.lmb.and_r(S.gap(g), Bool.and(False{}, S.items(rest)), hx))
            case SCon{+c, +u}:
              +h0 = hx
              +ht0 = ht
              +hg = LB.lmb.and_l(S.gap(g), Bool.and(S.solid(SCon{c, u}), S.items(rest)), h0)
              +h1 = LB.lmb.and_r(S.gap(g), Bool.and(S.solid(SCon{c, u}), S.items(rest)), h0)
              +hw = LB.lmb.and_l(S.solid(SCon{c, u}), S.items(rest), h1)
              +hr = LB.lmb.and_r(S.solid(SCon{c, u}), S.items(rest), h1)
              +hc = LB.lmb.not_t(S.space(c), LB.lmb.and_l(Bool.not(S.space(c)), S.dense(u), hw))
              +hu = LB.lmb.and_r(Bool.not(S.space(c)), S.dense(u), hw)
              +R = S.spell(rest, t)
              +hR = lpr.at_spell(rest, t, hr, ht0)
              +wd = {SCon{c, u} : String}
              +at = String.append(wd, R)
              +K = S.word_kind(wd, ns, ps)
              +rhs = lpr.pre(ks, ps, S.prefix_of.at(K, wd, R, S.prefix_of(rest, t, ns, S.after(K, ps))))
              %Equal.sym(L.Prefix, L.go(String.append(g, at), L.Gap{ks, ps}, ns), L.go(at, L.Gap{ks, ps}, ns), lpr.gapskip(g, at, ks, ps, ns, lpr.gap_spaces(g, hg))) : {_ == rhs : L.Prefix}
              %lpr.sp_f(c, hc) : {L.go(String.append(u, R), L.step.gap(_, at, ks, ps), ns) == rhs : L.Prefix}
              %Equal.sym(L.Prefix, L.go(String.append(u, R), L.In{at, ks, ps}, ns), L.go(R, L.In{at, ks, ps}, ns), lpr.inword(u, R, at, ks, ps, ns, hu)) : {_ == rhs : L.Prefix}
              %Equal.sym(L.Prefix, L.go(R, L.In{at, ks, ps}, ns), lpr.cont(L.close(at, ns, ks, ps), R, ns), lpr.close_at(R, at, ks, ps, ns, hR)) : {_ == rhs : L.Prefix}
              %Equal.sym(L.Cut, L.word(at), L.Cut{wd, R}, lpr.word(wd, R, hw, hR)) : {lpr.cont(L.close.word(_, at, ns, ks, ps), R, ns) == rhs : L.Prefix}
              %Equal.sym(L.Wd, L.classify(wd, ns, ps), K, lpr.kind(wd, ns, ps)) : {lpr.cont(L.close.on(_, wd, at, ks, ps), R, ns) == rhs : L.Prefix}
              lpr.step_kind(K, wd, R, ks, ps, ns, t, rest, lpr.main(rest, t, ns, lpr.ks_after(K, ks), S.after(K, ps), hr, ht0))

def lpr.bee(+b: Char, fb: Char, eb: {S.fold(b) == fb : Char}, h: {S.same(SCon{fb, SNil{}}, "b") == True{} : Bool}) -> {S.space(b) == False{} : Bool}:
  match fb:
    case Chr{+q}:
      +e = ALine.al.eq_sound(q, 98, LB.lmb.and_l(U32.is_eq(q, 98), S.same(SNil{}, SNil{}), h))
      %Equal.sym(Char, S.fold(b), Chr{q}, eb) : {S.white(S.code(_)) == False{} : Bool}
      %Equal.sym(U32, q, 98, e) : {S.white(U32.to_nat(_)) == False{} : Bool}
      {==}

# the chars of an opener are no spaces
def lpr.opener_at(+a: Char, +b: Char, fa: Char, ea: {S.fold(a) == fa : Char}, +fb: Char, eb: {S.fold(b) == fb : Char}, h: {S.same(SCon{fa, SCon{fb, SNil{}}}, "/b") == True{} : Bool}) -> {S.dense(SCon{a, SCon{b, SNil{}}}) == True{} : Bool}:
  match fa:
    case Chr{+p}:
      +h0 = h
      +e = ALine.al.eq_sound(p, 47, LB.lmb.and_l(U32.is_eq(p, 47), S.same(SCon{fb, SNil{}}, "b"), h0))
      +hb = lpr.bee(b, fb, eb, LB.lmb.and_r(U32.is_eq(p, 47), S.same(SCon{fb, SNil{}}, "b"), h0))
      %Equal.sym(Bool, S.space(b), False{}, hb) : {Bool.and(Bool.not(S.space(a)), Bool.and(Bool.not(_), True{})) == True{} : Bool}
      %Equal.sym(Char, S.fold(a), Chr{p}, ea) : {Bool.and(Bool.not(S.white(S.code(_))), True{}) == True{} : Bool}
      %Equal.sym(U32, p, 47, e) : {Bool.and(Bool.not(S.white(U32.to_nat(_))), True{}) == True{} : Bool}
      {==}

def Limits.limits_prefix_reads(a, b, xs, t, ns, ho, hx, ht):
  +hx0 = hx
  +ht0 = ht
  +R = S.spell(xs, t)
  +ab = {SCon{a, SCon{b, SNil{}}} : String}
  +ho0 = ho
  +hd = lpr.opener_at(a, b, S.fold(a), {==}, S.fold(b), {==}, ho0)
  %Equal.sym(L.Cut, L.word(String.append(ab, R)), L.Cut{ab, R}, lpr.word(ab, R, hd, lpr.at_spell(xs, t, hx0, ht0))) : {L.prefix.word(_, ns, SCon{a, SCon{b, R}}) == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}
  %Equal.sym(String, L.folded(ab), S.folded(ab), lpr.folded(ab)) : {L.prefix.at(L.same(_, "/b"), R, ns, SCon{a, SCon{b, R}}) == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}
  %Equal.sym(Bool, L.same(S.folded(ab), "/b"), S.opener(a, b), LB.lmb.same(S.folded(ab), "/b")) : {L.prefix.at(_, R, ns, SCon{a, SCon{b, R}}) == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}
  %Equal.sym(Bool, S.opener(a, b), True{}, ho0) : {L.prefix.at(_, R, ns, SCon{a, SCon{b, R}}) == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}
  %Equal.sym(L.Prefix, L.go(R, L.Gap{Nil{}, Nil{}}, ns), lpr.pre(Nil{}, Nil{}, S.prefix_of(xs, t, ns, Nil{})), lpr.main(xs, t, ns, Nil{}, Nil{}, hx0, ht0)) : {_ == S.prefix_of(xs, t, ns, Nil{}) : L.Prefix}
  lpr.pre_nil(S.prefix_of(xs, t, ns, Nil{}))
