# eukhe: lemmas the proofs of area autoresearch share: one step of the
# model (autoresearch/step): what an accepted step leaves, per event

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../bend/autoresearch/line.bend as ArL
import ../../../bend/autoresearch/state.bend as ArS
import ../../../bend/autoresearch/step.bend as ArP
import ../../../spec/autoresearch/metric_line.bend as SL
import ../../../laws/autoresearch/model.bend as Autoresearch

# Logic
# -----

def as.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True: anything follows
def as.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : as.BD(_, A, Unit)
  Unit{}

def as.absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : as.BD(_, Unit, A)
  Unit{}

def as.MB(m: Maybe<&2, String>, g: Type) -> Type:
  match m:
    case None{}:
      g
    case Some{t}:
      Unit

# a text is no nothing
def as.some_none(-A: Type, -t: String, e: {Some{t} == None{} : Maybe<&2, String>}) -> A:
  %e : as.MB(_, A)
  Unit{}

def as.fst(-A: Type, -B: Type, p: A & B) -> A:
  (a, b) = p
  a

def as.snd(-A: Type, -B: Type, p: A & B) -> B:
  (a, b) = p
  b

def as.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      as.absurd({False{} == True{} : Bool}, e)

def as.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      as.absurd({b == True{} : Bool}, e)

# a or b, with b raised to c
def as.or_mono(a: Bool, -b: Bool, -c: Bool, f: {b == True{} : Bool} -> {c == True{} : Bool}, e: {Bool.or(a, b) == True{} : Bool}) -> {Bool.or(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(e)

def as.or_r(a: Bool, -b: Bool, e: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

# Numbers
# -------

def as.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %as.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def as.zero_add(+n: Nat) -> {n == Nat.add(n, 0n) : Nat}:
  Equal.sym(Nat, Nat.add(n, 0n), n, as.add_zero(n))

def as.add_one(n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %as.add_one(p) : {1n+Nat.add(p, 1n) == 1n+_ : Nat}
      {==}

def as.nat_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      as.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      as.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %as.nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# Strings
# -------

def as.lt_eq(-G: Type, e: {LT{} == EQ{} : Cmp}) -> G:
  as.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), LT{}, EQ{}, e))

def as.gt_eq(-G: Type, e: {GT{} == EQ{} : Cmp}) -> G:
  as.absurd(G, Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), GT{}, EQ{}, e))

def as.cmp_eq_fin(-p: Nat, -at: Word(p), -bt: Word(p), t: Cmp, +ab: Bool, +bb: Bool,
  et: {Word.cmp(p, at, bt) == t : Cmp},
  rec: {Word.cmp(p, at, bt) == EQ{} : Cmp} -> {at == bt : Word(p)},
  e: {Word.cmp.fin(ab, bb, t) == EQ{} : Cmp})
  -> {WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}:
  match t:
    case LT{}:
      as.lt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case GT{}:
      as.gt_eq({WCon{ab, at} == WCon{bb, bt} : Word.Con<p>}, e)
    case EQ{}:
      match ab bb:
        case False{} False{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{False{}, w}, at, bt, rec(et))
        case False{} True{}:
          as.lt_eq({WCon{False{}, at} == WCon{True{}, bt} : Word.Con<p>}, e)
        case True{} False{}:
          as.gt_eq({WCon{True{}, at} == WCon{False{}, bt} : Word.Con<p>}, e)
        case True{} True{}:
          Equal.cong(Word(p), Word.Con<p>, w => WCon{True{}, w}, at, bt, rec(et))

def as.word_eq(+n: Nat, +a: Word(n), +b: Word(n)) ->
  {Word.cmp(n, a, b) == EQ{} : Cmp} -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          e => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          e => as.cmp_eq_fin(p, at, bt, Word.cmp(p, at, bt), ab, bb, {==}, as.word_eq(p, at, bt), e)

def as.u32_eq(+a: U32, +b: U32) -> {U32.cmp(a, b) == EQ{} : Cmp} -> {a == b : U32}:
  match a b:
    case U32{+x} U32{+y}:
      e => Equal.cong(Word(32n), U32, w => U32{w}, x, y, as.word_eq(32n, x, y)(e))

def as.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          match b:
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, as.word_refl(p, t)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, as.word_refl(p, t)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}

def as.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case U32{w}:
      as.word_refl(32n, w)

def as.str_cons(+x: U32, +y: U32, +t1: String, -t2: String, r: {t1 == t2 : String} & {U32.cmp(x, y) == EQ{} : Cmp}) -> {SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {EQ{} == EQ{} : Cmp}:
  (p, q) = r
  %p : {SCon{Chr{x}, t1} == SCon{Chr{y}, _} : String} & {EQ{} == EQ{} : Cmp}
  %as.u32_eq(x, y)(q) : {SCon{Chr{x}, t1} == SCon{Chr{_}, t1} : String} & {EQ{} == EQ{} : Cmp}
  ({==}, {==})

# two strings the order calls equal (from EQ so far) are equal
def as.str_sound(+a: String, +b: String, c: Cmp, e: {Cmp.is_eq(String.order.go(a, b, c)) == True{} : Bool}) -> {a == b : String} & {c == EQ{} : Cmp}:
  match a b:
    case SNil{} SNil{}:
      match c:
        case LT{}:
          as.absurd({SNil{} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          ({==}, {==})
        case GT{}:
          as.absurd({SNil{} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SNil{} SCon{h, t}:
      match c:
        case LT{}:
          as.absurd({SNil{} == SCon{h, t} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          as.absurd({SNil{} == SCon{h, t} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          as.absurd({SNil{} == SCon{h, t} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{h, t} SNil{}:
      match c:
        case LT{}:
          as.absurd({SCon{h, t} == SNil{} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          as.absurd({SCon{h, t} == SNil{} : String} & {EQ{} == EQ{} : Cmp}, e)
        case GT{}:
          as.absurd({SCon{h, t} == SNil{} : String} & {GT{} == EQ{} : Cmp}, e)
    case SCon{Chr{+x}, +t1} SCon{Chr{+y}, +t2}:
      match c:
        case LT{}:
          as.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {LT{} == EQ{} : Cmp}, e)
        case EQ{}:
          as.str_cons(x, y, t1, t2, as.str_sound(t1, t2, U32.cmp(x, y), e))
        case GT{}:
          as.absurd({SCon{Chr{x}, t1} == SCon{Chr{y}, t2} : String} & {GT{} == EQ{} : Cmp}, e)

# String.eq is equality
def as.str_eq(+a: String, +b: String, e: {String.eq(a, b) == True{} : Bool}) -> {a == b : String}:
  as.fst({a == b : String}, {EQ{} == EQ{} : Cmp}, as.str_sound(a, b, EQ{}, e))

def as.str_order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{} : Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      match h:
        case Chr{x}:
          %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, as.u32_refl(x)) : {String.order.go(t, t, _) == EQ{} : Cmp}
          as.str_order_refl(t)

def as.str_refl(a: String) -> {String.eq(a, a) == True{} : Bool}:
  %Equal.sym(Cmp, String.order.go(a, a, EQ{}), EQ{}, as.str_order_refl(a)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# Init
# ----

def as.all_name(s: String) -> {SL.all_name(s) == ArP.name_ok.go(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{x}, t}:
      %as.all_name(t) : {SL.all_name(SCon{Chr{x}, t}) == Bool.and(ArL.name_char(ArL.code(Chr{x})), _) : Bool}
      {==}

# the spec's name test is the shipped one
def as.name(m: String) -> {Bool.and(SL.nonempty(m), SL.all_name(m)) == ArP.name_ok(m) : Bool}:
  match m:
    case SNil{}:
      {==}
    case SCon{h, t}:
      as.all_name(SCon{h, t})

def as.cap(m: Maybe<&2, Nat>) -> {Autoresearch.ar_cap_ok(m) == ArP.cap_ok(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def as.err_max(b: Bool, em: {ArP.init.err.max(b) == None{} : Maybe<&2, String>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      as.some_none({False{} == True{} : Bool}, ArP.t_cap(), em)

def as.err_split(b: Bool, +mx: Maybe<&2, Nat>, em: {ArP.init.err.name(b, mx) == None{} : Maybe<&2, String>}) -> {b == True{} : Bool} & {ArP.cap_ok(mx) == True{} : Bool}:
  match b:
    case True{}:
      ({==}, as.err_max(ArP.cap_ok(mx), em))
    case False{}:
      as.some_none({False{} == True{} : Bool} & {ArP.cap_ok(mx) == True{} : Bool}, ArP.t_name(), em)

# what an accepted configuration has: a METRIC name, a cap of 1 or more
def as.P1(c: ArS.Cfg) -> Type:
  {Bool.and(Bool.and(SL.nonempty(ArS.Cfg.metric(c)), SL.all_name(ArS.Cfg.metric(c))), Autoresearch.ar_cap_ok(ArS.Cfg.max(c))) == True{} : Bool}

def as.p1.of(+m: String, +mx: Maybe<&2, Nat>, pr: {ArP.name_ok(m) == True{} : Bool} & {ArP.cap_ok(mx) == True{} : Bool}) -> {Bool.and(Bool.and(SL.nonempty(m), SL.all_name(m)), Autoresearch.ar_cap_ok(mx)) == True{} : Bool}:
  (hb, hc) = pr
  %Equal.sym(Bool, Bool.and(SL.nonempty(m), SL.all_name(m)), ArP.name_ok(m), as.name(m)) : {Bool.and(_, Autoresearch.ar_cap_ok(mx)) == True{} : Bool}
  %Equal.sym(Bool, Autoresearch.ar_cap_ok(mx), ArP.cap_ok(mx), as.cap(mx)) : {Bool.and(ArP.name_ok(m), _) == True{} : Bool}
  %Equal.sym(Bool, ArP.name_ok(m), True{}, hb) : {Bool.and(_, ArP.cap_ok(mx)) == True{} : Bool}
  hc

def as.p1(+c: ArS.Cfg, em: {ArP.init.err(c) == None{} : Maybe<&2, String>}) -> as.P1(c):
  as.p1.of(ArS.Cfg.metric(c), ArS.Cfg.max(c), as.err_split(ArP.name_ok(ArS.Cfg.metric(c)), ArS.Cfg.max(c), em))

# the abandoned rows: the shipped ones are the law's
def as.gone(old: Maybe<&2, ArS.Cfg>, seg: Nat, mode: ArS.Mode, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>) -> {ArS.abandon(Autoresearch.ar_name(old), seg, pend) == Autoresearch.ar_gone(ArS.St{old, seg, mode, runs, pend}) : List<&2, ArS.Row>}:
  match pend:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case ArS.Pend{id, kvs, fin}:
          match fin:
            case None{}:
              {==}
            case Some{b}:
              {==}

def as.set_eq(-c: ArS.Cfg, -seg2: Nat, -k: Nat, -runs: List<&2, ArS.Row>, -a: List<&2, ArS.Row>, -g: List<&2, ArS.Row>, hk: {seg2 == k : Nat}, hg: {a == g : List<&2, ArS.Row>}) -> {ArS.St{Some{c}, seg2, ArS.On{}, ArS.snoc(runs, a), None{}} == ArS.St{Some{c}, k, ArS.On{}, ArS.snoc(runs, g), None{}} : ArS.St}:
  %hk : {ArS.St{Some{c}, seg2, ArS.On{}, ArS.snoc(runs, a), None{}} == ArS.St{Some{c}, _, ArS.On{}, ArS.snoc(runs, g), None{}} : ArS.St}
  %hg : {ArS.St{Some{c}, seg2, ArS.On{}, ArS.snoc(runs, a), None{}} == ArS.St{Some{c}, seg2, ArS.On{}, ArS.snoc(runs, _), None{}} : ArS.St}
  {==}

# a first init or a new segment needs the harness
def as.harnT(old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool) -> Type:
  match old:
    case None{}:
      {harness == True{} : Bool}
    case Some{o}:
      match fresh:
        case True{}:
          {harness == True{} : Bool}
        case False{}:
          Unit

# an init on the same segment keeps the metric and direction
def as.keepT(old: Maybe<&2, ArS.Cfg>, fresh: Bool, c: ArS.Cfg) -> Type:
  match old:
    case None{}:
      Unit
    case Some{o}:
      match fresh:
        case True{}:
          Unit
        case False{}:
          {ArP.same(o, c) == True{} : Bool}

def as.InitSt(+s: ArS.St, +c: ArS.Cfg, fresh: Bool, harness: Bool) -> ArS.St:
  ArS.St{Some{c}, Nat.add(Autoresearch.ar_seg(s), Autoresearch.ar_bump(s, ArS.Init{c, fresh, harness})), ArS.On{}, ArS.snoc(Autoresearch.ar_runs(s), Autoresearch.ar_gone(s)), None{}}

# what an accepted init leaves
def as.Init(r: ArS.Res, s: ArS.St, c: ArS.Cfg, fresh: Bool, harness: Bool) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      as.P1(c) & (as.harnT(Autoresearch.ar_cfg(s), fresh, harness) & ({s2 == as.InitSt(s, c, fresh, harness) : ArS.St} & ({eff == ArS.Nothing{} : ArS.Eff} & ({stop == False{} : Bool} & as.keepT(Autoresearch.ar_cfg(s), fresh, c)))))
    case ArS.Refuse{t}:
      Unit

def as.init.keep(b: Bool, +o: ArS.Cfg, +c: ArS.Cfg, harness: Bool, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, eb: {ArP.same(o, c) == b : Bool}, p1: as.P1(c))
  -> as.Init(ArP.init.keep(b, c, ArS.Cfg.metric(o), seg, runs, pend), ArS.St{Some{o}, seg, mode, runs, pend}, c, False{}, harness):
  match b:
    case True{}:
      (p1, (Unit{}, (as.set_eq(c, seg, Nat.add(seg, 0n), runs, ArS.abandon(ArS.Cfg.metric(o), seg, pend), Autoresearch.ar_gone(ArS.St{Some{o}, seg, mode, runs, pend}), as.zero_add(seg), as.gone(Some{o}, seg, mode, runs, pend)), ({==}, ({==}, eb)))))
    case False{}:
      Unit{}

def as.init.old(old: Maybe<&2, ArS.Cfg>, +c: ArS.Cfg, fresh: Bool, harness: Bool, +seg: Nat, mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, p1: as.P1(c))
  -> as.Init(ArP.init.old(old, c, fresh, harness, seg, runs, pend), ArS.St{old, seg, mode, runs, pend}, c, fresh, harness):
  match old:
    case None{}:
      match fresh:
        case True{}:
          match harness:
            case True{}:
              (p1, ({==}, (as.set_eq(c, seg, Nat.add(seg, 0n), runs, ArS.abandon("", seg, pend), Autoresearch.ar_gone(ArS.St{None{}, seg, mode, runs, pend}), as.zero_add(seg), as.gone(None{}, seg, mode, runs, pend)), ({==}, ({==}, Unit{})))))
            case False{}:
              Unit{}
        case False{}:
          match harness:
            case True{}:
              (p1, ({==}, (as.set_eq(c, seg, Nat.add(seg, 0n), runs, ArS.abandon("", seg, pend), Autoresearch.ar_gone(ArS.St{None{}, seg, mode, runs, pend}), as.zero_add(seg), as.gone(None{}, seg, mode, runs, pend)), ({==}, ({==}, Unit{})))))
            case False{}:
              Unit{}
    case Some{+o}:
      match fresh:
        case True{}:
          match harness:
            case True{}:
              (p1, ({==}, (as.set_eq(c, 1n+seg, Nat.add(seg, 1n), runs, ArS.abandon(ArS.Cfg.metric(o), seg, pend), Autoresearch.ar_gone(ArS.St{Some{o}, seg, mode, runs, pend}), Equal.sym(Nat, Nat.add(seg, 1n), 1n+seg, as.add_one(seg)), as.gone(Some{o}, seg, mode, runs, pend)), ({==}, ({==}, Unit{})))))
            case False{}:
              Unit{}
        case False{}:
          as.init.keep(ArP.same(o, c), o, c, harness, seg, mode, runs, pend, {==}, p1)

def as.init.check(m: Maybe<&2, String>, +c: ArS.Cfg, old: Maybe<&2, ArS.Cfg>, fresh: Bool, harness: Bool, seg: Nat, mode: ArS.Mode, runs: List<&2, ArS.Row>, pend: Maybe<&2, ArS.Pend>, em: {ArP.init.err(c) == m : Maybe<&2, String>})
  -> as.Init(ArP.init.check(m, old, c, fresh, harness, seg, runs, pend), ArS.St{old, seg, mode, runs, pend}, c, fresh, harness):
  match m:
    case Some{t}:
      Unit{}
    case None{}:
      as.init.old(old, c, fresh, harness, seg, mode, runs, pend, as.p1(c, em))

# every init step: refused, or what as.Init says
def as.init(s: ArS.St, +c: ArS.Cfg, fresh: Bool, harness: Bool) -> as.Init(ArP.step(s, ArS.Init{c, fresh, harness}), s, c, fresh, harness):
  match s:
    case ArS.St{old, seg, mode, runs, pend}:
      as.init.check(ArP.init.err(c), c, old, fresh, harness, seg, mode, runs, pend, {==})

def as.init_took(+s: ArS.St, +c: ArS.Cfg, +fresh: Bool, +harness: Bool, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(s, ArS.Init{c, fresh, harness}) == ArS.Took{s2, eff, stop} : ArS.Res}) -> as.Init(ArS.Took{s2, eff, stop}, s, c, fresh, harness):
  %ok : as.Init(_, s, c, fresh, harness)
  as.init(s, c, fresh, harness)

# Flags, caps, modes
# ------------------

# a flagged run stays flagged when rows are appended
def as.snoc_flag(runs: List<&2, ArS.Row>, -x: List<&2, ArS.Row>, +id: Nat, h: {Autoresearch.ar_flagged(runs, id) == True{} : Bool}) -> {Autoresearch.ar_flagged(ArS.snoc(runs, x), id) == True{} : Bool}:
  match runs:
    case Nil{}:
      as.absurd({Autoresearch.ar_flagged(x, id) == True{} : Bool}, h)
    case +r <> t:
      as.or_mono(Autoresearch.ar_flagged.at(r, id), Autoresearch.ar_flagged(t, id), Autoresearch.ar_flagged(ArS.snoc(t, x), id), h2 => as.snoc_flag(t, x, id, h2), h)

def as.or_and(a: Bool, -fl: Bool, -b: Bool) -> {Bool.or(Bool.and(a, fl), b) == True{} : Bool} -> {Bool.or(Bool.and(a, True{}), b) == True{} : Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

# setting a row's flag keeps it flagged
def as.fset(r: ArS.Row, +id: Nat, -b: Bool) -> {Bool.or(Autoresearch.ar_flagged.at(r, id), b) == True{} : Bool} -> {Bool.or(Autoresearch.ar_flagged.at(ArP.flag.set(r), id), b) == True{} : Bool}:
  match r:
    case ArS.Row{i, sg, st, m, ms, ps, fn, fl, desc}:
      as.or_and(Nat.is_eq(i, id), fl, b)

# the rows of q keep every flag of runs
def as.FstFlag(q: List<&2, ArS.Row> & Bool, runs: List<&2, ArS.Row>, +id: Nat) -> Type:
  (rs, f) = q
  {Autoresearch.ar_flagged(runs, id) == True{} : Bool} -> {Autoresearch.ar_flagged(rs, id) == True{} : Bool}

def as.fmono.miss(q: List<&2, ArS.Row> & Bool, +r: ArS.Row, -t: List<&2, ArS.Row>, +id: Nat, hq: as.FstFlag(q, t, id)) -> as.FstFlag(ArP.flag.at(False{}, r, t, q), r <> t, id):
  (rs, found) = q
  h => as.or_mono(Autoresearch.ar_flagged.at(r, id), Autoresearch.ar_flagged(t, id), Autoresearch.ar_flagged(rs, id), hq, h)

def as.fmono.at(hit: Bool, +r: ArS.Row, +t: List<&2, ArS.Row>, q: List<&2, ArS.Row> & Bool, +id: Nat, hq: as.FstFlag(q, t, id)) -> as.FstFlag(ArP.flag.at(hit, r, t, q), r <> t, id):
  match hit:
    case True{}:
      as.fset(r, id, Autoresearch.ar_flagged(t, id))
    case False{}:
      as.fmono.miss(q, r, t, id, hq)

# a flag keeps the other flags
def as.fmono(runs: List<&2, ArS.Row>, +n: Nat, +id: Nat) -> as.FstFlag(ArP.flag.rows(runs, n), runs, id):
  match runs:
    case Nil{}:
      h => h
    case +r <> +t:
      as.fmono.at(ArP.flag.hit(r, n), r, t, ArP.flag.rows(t, n), id, as.fmono(t, n, id))

def as.capped.max(m: Maybe<&2, Nat>, +n: Nat) -> {ArP.capped.max(m, n) == Autoresearch.ar_capped.max(m, n) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{k}:
      {==}

def as.capped(c: Maybe<&2, ArS.Cfg>, +n: Nat) -> {ArP.capped(c, n) == Autoresearch.ar_capped(c, n) : Bool}:
  match c:
    case None{}:
      {==}
    case Some{k}:
      as.capped.max(ArS.Cfg.max(k), n)

def as.lmode(b: Bool, -mode: ArS.Mode, -st: ArS.Status, -d: String, -w: Maybe<&2, String>, -v: Nat) -> {ArP.log.mode(b, mode) == Autoresearch.ar_mode_after(ArS.Log{st, d, w, v}, b, mode) : ArS.Mode}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# What every accepted step does
# -----------------------------

# the segment moves only by a new segment, the effect is the status's,
# the stop is the cap's, the mode the event's, and flags stay
def as.Gen(r: ArS.Res, +s: ArS.St, +e: ArS.Ev, +id: Nat) -> Type:
  match r:
    case ArS.Took{s2, eff, stop}:
      {Autoresearch.ar_seg(s2) == Nat.add(Autoresearch.ar_seg(s), Autoresearch.ar_bump(s, e)) : Nat} & ({eff == Autoresearch.ar_effect(e) : ArS.Eff} & (({stop == Bool.and(Autoresearch.ar_is_log(e), Autoresearch.ar_capped(Autoresearch.ar_cfg(s2), ArS.St.logged(s2))) : Bool} & {Autoresearch.ar_mode(s2) == Autoresearch.ar_mode_after(e, stop, Autoresearch.ar_mode(s)) : ArS.Mode}) & ({Autoresearch.ar_flagged(Autoresearch.ar_runs(s), id) == True{} : Bool} -> {Autoresearch.ar_flagged(Autoresearch.ar_runs(s2), id) == True{} : Bool})))
    case ArS.Refuse{t}:
      Unit

def as.gen_init(r: ArS.Res, +s: ArS.St, +c: ArS.Cfg, +f: Bool, +h: Bool, +id: Nat, hi: as.Init(r, s, c, f, h)) -> as.Gen(r, s, ArS.Init{c, f, h}, id):
  match r:
    case ArS.Took{s2, eff, stop}:
      (p1, r1) = hi
      (p2, r2) = r1
      (p3, r3) = r2
      (p4, r4) = r3
      (p5, p6) = r4
      %Equal.sym(ArS.St, s2, as.InitSt(s, c, f, h), p3) : as.Gen(ArS.Took{_, eff, stop}, s, ArS.Init{c, f, h}, id)
      %Equal.sym(ArS.Eff, eff, ArS.Nothing{}, p4) : as.Gen(ArS.Took{as.InitSt(s, c, f, h), _, stop}, s, ArS.Init{c, f, h}, id)
      %Equal.sym(Bool, stop, False{}, p5) : as.Gen(ArS.Took{as.InitSt(s, c, f, h), ArS.Nothing{}, _}, s, ArS.Init{c, f, h}, id)
      ({==}, ({==}, (({==}, {==}), h2 => as.snoc_flag(Autoresearch.ar_runs(s), Autoresearch.ar_gone(s), id, h2))))
    case ArS.Refuse{t}:
      Unit{}

def as.gen_begin.at(b: Bool, -n: Nat, +m: Nat, +c: ArS.Cfg, +seg: Nat, -mode: ArS.Mode, +runs: List<&2, ArS.Row>, +pend: Maybe<&2, ArS.Pend>, +id: Nat)
  -> as.Gen(ArP.begin.at(b, m, c, seg, mode, runs, pend), ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Begin{n}, id):
  match b:
    case True{}:
      (as.zero_add(seg), ({==}, (({==}, {==}), h => as.snoc_flag(runs, ArS.abandon(ArS.Cfg.metric(c), seg, pend), id, h))))
    case False{}:
      Unit{}

def as.gen_begin(s: ArS.St, +n: Nat, +id: Nat) -> as.Gen(ArP.step(s, ArS.Begin{n}), s, ArS.Begin{n}, id):
  match s:
    case ArS.St{cfg, +seg, mode, +runs, +pend}:
      match cfg:
        case None{}:
          Unit{}
        case Some{+c}:
          as.gen_begin.at(Nat.is_eq(n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend))), n, 1n+Nat.add(ArS.rlen(runs), ArS.pcount(pend)), c, seg, mode, runs, pend, id)

def as.gen_line.got(m: Maybe<&2, ArL.Kv>, -cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -pid: Nat, -kvs: List<&2, ArL.Kv>, -t: String, -id: Nat)
  -> as.Gen(ArP.line.got(m, cfg, seg, mode, runs, pid, kvs), ArS.St{cfg, seg, mode, runs, Some{ArS.Pend{pid, kvs, None{}}}}, ArS.Line{t}, id):
  match m:
    case None{}:
      (as.zero_add(seg), ({==}, (({==}, {==}), h => h)))
    case Some{kv}:
      match kv:
        case ArL.Kv{n, d}:
          (as.zero_add(seg), ({==}, (({==}, {==}), h => h)))

def as.gen_line(s: ArS.St, +t: String, +id: Nat) -> as.Gen(ArP.step(s, ArS.Line{t}), s, ArS.Line{t}, id):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, pend}:
      match pend:
        case None{}:
          Unit{}
        case Some{p}:
          match p:
            case ArS.Pend{+pid, +kvs, fin}:
              match fin:
                case None{}:
                  as.gen_line.got(ArL.metric(t), cfg, seg, mode, runs, pid, kvs, t, id)
                case Some{b}:
                  Unit{}

def as.gen_finish(s: ArS.St, -neg: Bool, -code: Nat, -to: Bool, -id: Nat) -> as.Gen(ArP.step(s, ArS.Finish{neg, code, to}), s, ArS.Finish{neg, code, to}, id):
  match s:
    case ArS.St{cfg, +seg, mode, runs, pend}:
      match pend:
        case None{}:
          Unit{}
        case Some{p}:
          match p:
            case ArS.Pend{pid, kvs, fin}:
              match fin:
                case None{}:
                  (as.zero_add(seg), ({==}, (({==}, {==}), h => h)))
                case Some{b}:
                  Unit{}

# a logged run: its row appended, the stop the cap's
def as.gen_done(+cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +st: ArS.Status, +d: String, +w: Maybe<&2, String>, +v: Nat, -eff: ArS.Eff, +id: Nat, heff: {eff == Autoresearch.ar_effect(ArS.Log{st, d, w, v}) : ArS.Eff})
  -> as.Gen(ArP.log.done(cfg, seg, mode, runs, p, st, d, eff), ArS.St{cfg, seg, mode, runs, pend}, ArS.Log{st, d, w, v}, id):
  +runs2 = ArS.snoc(runs, [ArS.row(ArS.primary(cfg), seg, p, Some{st}, d)])
  (as.zero_add(seg), (heff, ((as.capped(cfg, ArS.logged(runs2, seg)), as.lmode(ArP.capped(cfg, ArS.logged(runs2, seg)), mode, st, d, w, v)), h => as.snoc_flag(runs, [ArS.row(ArS.primary(cfg), seg, p, Some{st}, d)], id, h))))

def as.gen_keep.why(b: Bool, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat)
  -> as.Gen(ArP.keep.why(b, Some{c}, seg, mode, runs, p, d), ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, d, w, v}, id):
  match b:
    case True{}:
      as.gen_done(Some{c}, seg, mode, runs, pend, p, ArS.Keep{}, d, w, v, ArS.Commit{}, id, {==})
    case False{}:
      Unit{}

def as.gen_keep.beats(b: Bool, -x: ArD.Dec, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat)
  -> as.Gen(ArP.keep.beats(b, x, ArS.Cfg.dir(c), w, v, Some{c}, seg, mode, runs, p, d), ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, d, w, v}, id):
  match b:
    case True{}:
      as.gen_keep.why(Bool.or(Nat.is_eq(v, 0n), ArP.justified(w)), c, seg, mode, runs, pend, p, d, w, v, id)
    case False{}:
      Unit{}

def as.gen_keep.metric(m: Maybe<&2, ArD.Dec>, +c: ArS.Cfg, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat)
  -> as.Gen(ArP.keep.metric(m, c, w, v, seg, mode, runs, p, d), ArS.St{Some{c}, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, d, w, v}, id):
  match m:
    case None{}:
      Unit{}
    case Some{+x}:
      as.gen_keep.beats(ArS.beats(ArS.Cfg.dir(c), x, runs, seg), x, c, seg, mode, runs, pend, p, d, w, v, id)

def as.gen_keep(passed: Bool, cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat)
  -> as.Gen(ArP.keep(passed, cfg, w, v, seg, mode, runs, p, d), ArS.St{cfg, seg, mode, runs, pend}, ArS.Log{ArS.Keep{}, d, w, v}, id):
  match passed:
    case True{}:
      match cfg:
        case None{}:
          Unit{}
        case Some{+c}:
          as.gen_keep.metric(ArS.lookup(ArS.Pend.kvs(p), ArS.Cfg.metric(c)), c, seg, mode, runs, pend, p, d, w, v, id)
    case False{}:
      Unit{}

def as.gen_log.st(st: ArS.Status, passed: Bool, +cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, +mode: ArS.Mode, +runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, +p: ArS.Pend, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat)
  -> as.Gen(ArP.log.status(st, passed, d, w, v, cfg, seg, mode, runs, p), ArS.St{cfg, seg, mode, runs, pend}, ArS.Log{st, d, w, v}, id):
  match st:
    case ArS.Keep{}:
      as.gen_keep(passed, cfg, seg, mode, runs, pend, p, d, w, v, id)
    case ArS.Discard{}:
      as.gen_done(cfg, seg, mode, runs, pend, p, ArS.Discard{}, d, w, v, ArS.Reset{}, id, {==})
    case ArS.Crash{}:
      match passed:
        case True{}:
          Unit{}
        case False{}:
          as.gen_done(cfg, seg, mode, runs, pend, p, ArS.Crash{}, d, w, v, ArS.Reset{}, id, {==})
    case ArS.Checks{}:
      match passed:
        case True{}:
          as.gen_done(cfg, seg, mode, runs, pend, p, ArS.Checks{}, d, w, v, ArS.Reset{}, id, {==})
        case False{}:
          Unit{}

def as.gen_log(s: ArS.St, +st: ArS.Status, +d: String, +w: Maybe<&2, String>, +v: Nat, +id: Nat) -> as.Gen(ArP.step(s, ArS.Log{st, d, w, v}), s, ArS.Log{st, d, w, v}, id):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, pend}:
      match pend:
        case None{}:
          Unit{}
        case Some{p}:
          match p:
            case ArS.Pend{+pid, +kvs, fin}:
              match fin:
                case None{}:
                  Unit{}
                case Some{+passed}:
                  as.gen_log.st(st, passed, cfg, seg, mode, runs, Some{ArS.Pend{pid, kvs, Some{passed}}}, ArS.Pend{pid, kvs, Some{passed}}, d, w, v, id)

def as.gen_flag.found(q: List<&2, ArS.Row> & Bool, -n: Nat, -cfg: Maybe<&2, ArS.Cfg>, +seg: Nat, -mode: ArS.Mode, -runs: List<&2, ArS.Row>, -pend: Maybe<&2, ArS.Pend>, -reason: String, -id: Nat, hq: as.FstFlag(q, runs, id))
  -> as.Gen(ArP.flag.found(q, n, cfg, seg, mode, pend), ArS.St{cfg, seg, mode, runs, pend}, ArS.Flag{n, reason}, id):
  (rs, found) = q
  match found:
    case True{}:
      (as.zero_add(seg), ({==}, (({==}, {==}), hq)))
    case False{}:
      Unit{}

def as.gen_flag(s: ArS.St, +n: Nat, reason: String, +id: Nat) -> as.Gen(ArP.step(s, ArS.Flag{n, reason}), s, ArS.Flag{n, reason}, id):
  match s:
    case ArS.St{+cfg, +seg, +mode, +runs, +pend}:
      match reason:
        case SNil{}:
          Unit{}
        case SCon{h, t}:
          as.gen_flag.found(ArP.flag.rows(runs, n), n, cfg, seg, mode, runs, pend, SCon{h, t}, id, as.fmono(runs, n, id))

def as.gen_mode(s: ArS.St, -m: ArS.Mode, -id: Nat) -> as.Gen(ArP.step(s, ArS.SetMode{m}), s, ArS.SetMode{m}, id):
  match s:
    case ArS.St{cfg, +seg, mode, runs, pend}:
      (as.zero_add(seg), ({==}, (({==}, {==}), h => h)))

# every step: refused, or what as.Gen says
def as.gen(+s: ArS.St, e: ArS.Ev, +id: Nat) -> as.Gen(ArP.step(s, e), s, e, id):
  match e:
    case ArS.Init{+c, +f, +h}:
      as.gen_init(ArP.step(s, ArS.Init{c, f, h}), s, c, f, h, id, as.init(s, c, f, h))
    case ArS.Begin{+n}:
      as.gen_begin(s, n, id)
    case ArS.Line{+t}:
      as.gen_line(s, t, id)
    case ArS.Finish{neg, code, to}:
      as.gen_finish(s, neg, code, to, id)
    case ArS.Log{+st, +d, +w, +v}:
      as.gen_log(s, st, d, w, v, id)
    case ArS.Flag{+n, reason}:
      as.gen_flag(s, n, reason, id)
    case ArS.SetMode{m}:
      as.gen_mode(s, m, id)

def as.gen_took(+s: ArS.St, +e: ArS.Ev, +id: Nat, -s2: ArS.St, -eff: ArS.Eff, -stop: Bool, ok: {ArP.step(s, e) == ArS.Took{s2, eff, stop} : ArS.Res}) -> as.Gen(ArS.Took{s2, eff, stop}, s, e, id):
  %ok : as.Gen(_, s, e, id)
  as.gen(s, e, id)
