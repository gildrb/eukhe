# eukhe: lemmas the proofs of area staging share

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg

# ---- staging ----

# proof_staging: the staging, sweep and listing laws of LAWS.bend section storage
# (D2): a publish never takes a name that is taken; a sweep never removes
# a held, young or unreached entry, and removes every stale free leftover
# it reaches; a session is listed once, under the storage it opens as.

# Logic and numbers
# -----------------

def pg.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pg.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pg.BD(_, Unit, A)
  Unit{}

def pg.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pg.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      pg.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %pg.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def pg.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pg.eq_refl(p)

# Sweep
# -----

def pg.put_app(+n: Sg.Node, a: List<&2, Sg.Node>, +c: List<&2, Sg.Node>, b: Bool) -> {Sg.sweep.put(n, List.append(&2, Sg.Node, a, c), b) == List.append(&2, Sg.Node, Sg.sweep.put(n, a, b), c) : List<&2, Sg.Node>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.sweep_app(pre: List<&2, Sg.Node>, +x: List<&2, Sg.Node>) -> {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(x)) == Sg.sweep(List.append(&2, Sg.Node, pre, x)) : List<&2, Sg.Node>}:
  match pre:
    case Nil{}:
      {==}
    case +n <> +rest:
      %pg.put_app(n, Sg.sweep(rest), Sg.sweep(x), Sg.removes(n)) : {_ == Sg.sweep.put(n, Sg.sweep(List.append(&2, Sg.Node, rest, x)), Sg.removes(n)) : List<&2, Sg.Node>}
      %pg.sweep_app(rest, x) : {Sg.sweep.put(n, List.append(&2, Sg.Node, Sg.sweep(rest), Sg.sweep(x)), Sg.removes(n)) == Sg.sweep.put(n, _, Sg.removes(n)) : List<&2, Sg.Node>}
      {==}

# a node the sweep keeps: the sweep of the whole is the sweep of the parts
def pg.kept(+pre: List<&2, Sg.Node>, +n: Sg.Node, +post: List<&2, Sg.Node>, no: {False{} == Sg.removes(n) : Bool}) -> {Sg.sweep(List.append(&2, Sg.Node, pre, n <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  %pg.sweep_app(pre, n <> post) : {_ == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}
  %no : {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep.put(n, Sg.sweep(post), _)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}
  {==}

# An import
# ---------

def pg.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.mem_app(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Bool.or(Sg.mem(n, a), Sg.mem(n, b)) == Sg.mem(n, List.append(&2, Nat, a, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +rest:
      %pg.mem_app(n, rest, b) : {Bool.or(Bool.or(Nat.is_eq(x, n), Sg.mem(n, rest)), Sg.mem(n, b)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      pg.or_assoc(Nat.is_eq(x, n), Sg.mem(n, rest), Sg.mem(n, b))

def pg.kput_app(+m: Nat, a: List<&2, Nat>, +c: List<&2, Nat>, q: Bool) -> {Sg.keep.put(m, List.append(&2, Nat, a, c), q) == List.append(&2, Nat, Sg.keep.put(m, a, q), c) : List<&2, Nat>}:
  match q:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.dur_app(es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {List.append(&2, Nat, Sg.durables(es), Sg.durables(x)) == Sg.durables(List.append(&2, Sg.Ent, es, x)) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{+m, +a, +hd, +c}:
          +q = Bool.and(a, Bool.and(Bool.not(hd), c))
          %pg.kput_app(m, Sg.durables(rest), Sg.durables(x), q) : {_ == Sg.keep.put(m, Sg.durables(List.append(&2, Sg.Ent, rest, x)), q) : List<&2, Nat>}
          %pg.dur_app(rest, x) : {Sg.keep.put(m, List.append(&2, Nat, Sg.durables(rest), Sg.durables(x)), q) == Sg.keep.put(m, _, q) : List<&2, Nat>}
          {==}
        case Sg.Legacy{s, r}:
          pg.dur_app(rest, x)

# ---- the real rule: the sweep ----

# The code of the real rule is its spec (laws/staging.bend): the same
# decisions, helper by helper.

# ch.is(c, 46) is the test for '.'
def rr.dot(c: Char) -> {Sg.ch.is(c, 46) == Char.is_eq(c, '.') : Bool}:
  match c:
    case Chr{x}:
      {==}

def rr.in(+c: Char, cs: String) -> {Sg.ch.in(c, cs) == Staging.sp_in(c, cs) : Bool}:
  match cs:
    case SNil{}:
      {==}
    case SCon{+x, +t}:
      %rr.in(c, t) : {Bool.or(Char.is_eq(c, x), Sg.ch.in(c, t)) == Bool.or(Char.is_eq(c, x), _) : Bool}
      {==}

def rr.hexn(n: Nat, s: String) -> {Sg.hexn(n, s) == Staging.sp_hexn(n, s) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      match s:
        case SNil{}:
          {==}
        case SCon{+c, +t}:
          %rr.in(c, "0123456789abcdef") : {Bool.and(Sg.ch.in(c, "0123456789abcdef"), Sg.hexn(k, t)) == Bool.and(_, Staging.sp_hexn(k, t)) : Bool}
          %rr.hexn(k, t) : {Bool.and(Sg.ch.in(c, "0123456789abcdef"), Sg.hexn(k, t)) == Bool.and(Sg.ch.in(c, "0123456789abcdef"), _) : Bool}
          {==}

def rr.uuid(m: Maybe<&2, String>) -> {Sg.uuid(m) == Staging.sp_uuid(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      rr.hexn(32n, s)

def rr.kept(ok: Bool, m: Maybe<&2, String>) -> {Sg.kept_if(ok, m) == Staging.sp_if(ok, m) : Maybe<&2, String>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def rr.unprefix(p: String, s: String) -> {Sg.unprefix(p, s) == Staging.sp_unprefix(p, s) : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+x, +pt}:
      match s:
        case SNil{}:
          {==}
        case SCon{+y, +st}:
          %rr.unprefix(pt, st) : {Sg.kept_if(Char.is_eq(x, y), Sg.unprefix(pt, st)) == Staging.sp_if(Char.is_eq(x, y), _) : Maybe<&2, String>}
          rr.kept(Char.is_eq(x, y), Sg.unprefix(pt, st))

# the uuid of a label's prefix
def rr.lab(+p: String, +a: String) -> {Sg.uuid(Sg.unprefix(p, a)) == Staging.sp_uuid(Staging.sp_unprefix(p, a)) : Bool}:
  %rr.unprefix(p, a) : {Sg.uuid(Sg.unprefix(p, a)) == Staging.sp_uuid(_) : Bool}
  rr.uuid(Sg.unprefix(p, a))

def rr.tail(+a: String) -> {Sg.tail(a) == Staging.sp_tail(a) : Bool}:
  +i = Sg.uuid(Sg.unprefix("import-", a))
  +f = Sg.uuid(Sg.unprefix("fork-", a))
  +d = Sg.uuid(Sg.unprefix("deleted-", a))
  +sf = Staging.sp_uuid(Staging.sp_unprefix("fork-", a))
  +sd = Staging.sp_uuid(Staging.sp_unprefix("deleted-", a))
  %rr.lab("import-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(_, Bool.or(sf, sd)) : Bool}
  %rr.lab("fork-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(i, Bool.or(_, sd)) : Bool}
  %rr.lab("deleted-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(i, Bool.or(f, _)) : Bool}
  {==}

# the code's split, as the spec's
def rr.sp(m: Maybe<&2, Sg.Split>) -> Maybe<&2, Staging.SpCut>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Sg.Split{b, a}:
          Some{Staging.SpCut{b, a}}

def rr.cut_put(r: Maybe<&2, Sg.Split>, d: Bool, +c: Char, +t: String) -> {rr.sp(Sg.cut.put(r, d, c, t)) == Staging.sp_cut.put(rr.sp(r), d, c, t) : Maybe<&2, Staging.SpCut>}:
  match r:
    case Some{p}:
      match p:
        case Sg.Split{b, a}:
          {==}
    case None{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

def rr.cut(w: String) -> {rr.sp(Sg.cut(w)) == Staging.sp_cut(w) : Maybe<&2, Staging.SpCut>}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Staging.SpCut>, rr.sp(Sg.cut.put(Sg.cut(t), Sg.ch.is(c, 46), c, t)), Staging.sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t), rr.cut_put(Sg.cut(t), Sg.ch.is(c, 46), c, t)) : {_ == Staging.sp_cut.put(Staging.sp_cut(t), Char.is_eq(c, '.'), c, t) : Maybe<&2, Staging.SpCut>}
      %rr.cut(t) : {Staging.sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t) == Staging.sp_cut.put(_, Char.is_eq(c, '.'), c, t) : Maybe<&2, Staging.SpCut>}
      %rr.dot(c) : {Staging.sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t) == Staging.sp_cut.put(rr.sp(Sg.cut(t)), _, c, t) : Maybe<&2, Staging.SpCut>}
      {==}

def rr.swept_cut(m: Maybe<&2, Sg.Split>) -> {Sg.swept.cut(m) == Staging.sp_swept.cut(rr.sp(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Sg.Split{+b, +a}:
          %rr.tail(a) : {Bool.and(Bool.not(String.is_empty(b)), Sg.tail(a)) == Bool.and(Bool.not(String.is_empty(b)), _) : Bool}
          {==}

def rr.swept(s: String) -> {Sg.swept(s) == Staging.sp_swept(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x = Sg.swept.cut(Sg.cut(t))
      %rr.cut(t) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(Char.is_eq(c, '.'), Staging.sp_swept.cut(_)) : Bool}
      %rr.swept_cut(Sg.cut(t)) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(Char.is_eq(c, '.'), _) : Bool}
      %rr.dot(c) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(_, x) : Bool}
      {==}

def rr.met_dir(sw: Bool, m: Bool) -> {Sg.met.dir(sw, m) == Staging.sp_met.dir(sw, m) : Sg.Met}:
  match sw m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rr.met_lock(sw: Bool, th: Bool) -> {Sg.met.lock(sw, th) == Staging.sp_met.lock(sw, th) : Sg.Met}:
  match sw th:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rr.met_file(m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Sg.met.file(m, all) == Staging.sp_met.file(m, all) : Sg.Met}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %rr.swept(x) : {Sg.met.lock(Sg.swept(x), Sg.has_name(x, all)) == Staging.sp_met.lock(_, LawsBase.text_has_name(x, all)) : Sg.Met}
      %LStg.stg.has_name(x, all) : {Sg.met.lock(Sg.swept(x), Sg.has_name(x, all)) == Staging.sp_met.lock(Sg.swept(x), _) : Sg.Met}
      rr.met_lock(Sg.swept(x), Sg.has_name(x, all))

def rr.met_utf(k: Sg.Form, +s: String, +all: List<&2, Sg.Seen>) -> {Sg.met.utf(k, s, all) == Staging.sp_met.utf(k, s, all) : Sg.Met}:
  match k:
    case Sg.KDir{+main}:
      %rr.swept(s) : {Sg.met.dir(Sg.swept(s), main) == Staging.sp_met.dir(_, main) : Sg.Met}
      rr.met_dir(Sg.swept(s), main)
    case Sg.KFile{}:
      %LStg.stg.unsuffix(".lock", s) : {Sg.met.file(Sg.unsuffix(".lock", s), all) == Staging.sp_met.file(_, all) : Sg.Met}
      rr.met_file(Sg.unsuffix(".lock", s), all)
    case Sg.KOther{}:
      {==}

def rr.met(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Sg.met(e, all) == Staging.sp_met(e, all) : Sg.Met}:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          rr.met_utf(k, s, all)
        case Sg.Raw{}:
          match k:
            case Sg.KDir{main}:
              rr.met_dir(False{}, main)
            case Sg.KFile{}:
              {==}
            case Sg.KOther{}:
              {==}

def rr.meet_go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Sg.meet.go(es, all) == Staging.sp_meet.go(es, all) : List<&2, Sg.Met>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %rr.met(e, all) : {Sg.met(e, all) <> Sg.meet.go(rest, all) == _ <> Staging.sp_meet.go(rest, all) : List<&2, Sg.Met>}
      %rr.meet_go(rest, all) : {Sg.met(e, all) <> Sg.meet.go(rest, all) == Sg.met(e, all) <> _ : List<&2, Sg.Met>}
      {==}

def rr.stale(+now: Sg.Time, t: Sg.Time) -> {Sg.stale(now, t) == Staging.sp_old(now, t) : Bool}:
  match now:
    case Sg.Time{+ns, +nn}:
      match t:
        case Sg.Time{ts, tn}:
          {==}

def rr.stale_all(+now: Sg.Time, ts: List<&2, Sg.Time>) -> {Sg.stale_all(now, ts) == Staging.sp_all_old(now, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %rr.stale(now, t) : {Bool.and(Sg.stale(now, t), Sg.stale_all(now, rest)) == Bool.and(_, Staging.sp_all_old(now, rest)) : Bool}
      %rr.stale_all(now, rest) : {Bool.and(Sg.stale(now, t), Sg.stale_all(now, rest)) == Bool.and(Sg.stale(now, t), _) : Bool}
      {==}

def rr.judge_go(b: Bool, c: Sg.Cand, l: Sg.Lock) -> {Sg.judge.go(b, c, l) == Staging.sp_judge.go(b, c, l) : Sg.Plan}:
  match b:
    case True{}:
      match c:
        case Sg.CDir{}:
          match l:
            case Sg.LHeld{}:
              {==}
            case Sg.LFree{}:
              {==}
            case Sg.LAbsent{}:
              {==}
        case Sg.CLock{}:
          match l:
            case Sg.LHeld{}:
              {==}
            case Sg.LFree{}:
              {==}
            case Sg.LAbsent{}:
              {==}
    case False{}:
      {==}

# the plan's staleness is the spec's: judge is judge.go on sp_all_old
def rr.judge_old(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>) -> {Sg.judge.go(Staging.sp_all_old(now, own <> inner), c, l) == Sg.judge(c, l, now, own, inner) : Sg.Plan}:
  %rr.stale_all(now, own <> inner) : {Sg.judge.go(_, c, l) == Sg.judge.go(Sg.stale_all(now, own <> inner), c, l) : Sg.Plan}
  {==}

# ---- the real rule: the names Rust mints ----

# no char of s is '.'
def rr.nodot(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(Char.is_eq(c, '.')), rr.nodot(t))

def rr.not_t(+b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# a text with no '.' has no last '.'
def rr.cut_none(z: String, h: {rr.nodot(z) == True{} : Bool}) -> {Staging.sp_cut(z) == None{} : Maybe<&2, Staging.SpCut>}:
  match z:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hh = h
      +hc = rr.not_t(Char.is_eq(c, '.'), LStg.stg.and_l(Bool.not(Char.is_eq(c, '.')), rr.nodot(t), hh))
      +ht = LStg.stg.and_r(Bool.not(Char.is_eq(c, '.')), rr.nodot(t), hh)
      %Equal.sym(Maybe<&2, Staging.SpCut>, Staging.sp_cut(t), None{}, rr.cut_none(t, ht)) : {Staging.sp_cut.put(_, Char.is_eq(c, '.'), c, t) == None{} : Maybe<&2, Staging.SpCut>}
      %Equal.sym(Bool, Char.is_eq(c, '.'), False{}, hc) : {Staging.sp_cut.put(None{}, _, c, t) == None{} : Maybe<&2, Staging.SpCut>}
      {==}

# t, a '.', then a text z with no '.': the last '.' is that one
def rr.cut_last(t: String, +z: String, +h: {rr.nodot(z) == True{} : Bool}) -> {Staging.sp_cut(String.append(t, SCon{'.', z})) == Some{Staging.SpCut{t, z}} : Maybe<&2, Staging.SpCut>}:
  match t:
    case SNil{}:
      %Equal.sym(Maybe<&2, Staging.SpCut>, Staging.sp_cut(z), None{}, rr.cut_none(z, h)) : {Staging.sp_cut.put(_, Char.is_eq('.', '.'), '.', z) == Some{Staging.SpCut{SNil{}, z}} : Maybe<&2, Staging.SpCut>}
      {==}
    case SCon{+c, +u}:
      +w = String.append(u, SCon{'.', z})
      %Equal.sym(Maybe<&2, Staging.SpCut>, Staging.sp_cut(w), Some{Staging.SpCut{u, z}}, rr.cut_last(u, z, h)) : {Staging.sp_cut.put(_, Char.is_eq(c, '.'), c, w) == Some{Staging.SpCut{SCon{c, u}, z}} : Maybe<&2, Staging.SpCut>}
      {==}

def rr.in_nodot.at(+c: Char, +x: Char, -r: String, b: Bool, eb: {Char.is_eq(c, x) == b : Bool},
  hin: {Bool.or(b, Staging.sp_in(c, r)) == True{} : Bool}, hx: {Char.is_eq(x, '.') == False{} : Bool},
  ih: {Staging.sp_in(c, r) == True{} : Bool} -> {Char.is_eq(c, '.') == False{} : Bool}) -> {Char.is_eq(c, '.') == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Char, c, x, LStg.stg.char_sound(c, x, eb)) : {Char.is_eq(_, '.') == False{} : Bool}
      hx
    case False{}:
      ih(hin)

# a char of a text with no '.' is no '.'
def rr.in_nodot(+c: Char, cs: String, hin: {Staging.sp_in(c, cs) == True{} : Bool}, hcs: {rr.nodot(cs) == True{} : Bool}) -> {Char.is_eq(c, '.') == False{} : Bool}:
  match cs:
    case SNil{}:
      LStg.stg.absurdF({Char.is_eq(c, '.') == False{} : Bool}, hin)
    case SCon{+x, +r}:
      +hh = hcs
      +hx = rr.not_t(Char.is_eq(x, '.'), LStg.stg.and_l(Bool.not(Char.is_eq(x, '.')), rr.nodot(r), hh))
      +hr = LStg.stg.and_r(Bool.not(Char.is_eq(x, '.')), rr.nodot(r), hh)
      rr.in_nodot.at(c, x, r, Char.is_eq(c, x), {==}, hin, hx, h2 => rr.in_nodot(c, r, h2, hr))

# lowercase hex digits have no '.'
def rr.hex_nodot(n: Nat, s: String, h: {Staging.sp_hexn(n, s) == True{} : Bool}) -> {rr.nodot(s) == True{} : Bool}:
  match n:
    case 0n:
      match s:
        case SNil{}:
          {==}
        case SCon{c, t}:
          LStg.stg.absurdF({rr.nodot(SCon{c, t}) == True{} : Bool}, h)
    case 1n+k:
      match s:
        case SNil{}:
          LStg.stg.absurdF({rr.nodot(SNil{}) == True{} : Bool}, h)
        case SCon{+c, +t}:
          +hh = h
          +hc = rr.in_nodot(c, "0123456789abcdef", LStg.stg.and_l(Staging.sp_in(c, "0123456789abcdef"), Staging.sp_hexn(k, t), hh), {==})
          +ht = rr.hex_nodot(k, t, LStg.stg.and_r(Staging.sp_in(c, "0123456789abcdef"), Staging.sp_hexn(k, t), hh))
          %Equal.sym(Bool, Char.is_eq(c, '.'), False{}, hc) : {Bool.and(Bool.not(_), rr.nodot(t)) == True{} : Bool}
          ht

# a label, '-' and a uuid have no '.'
def rr.lab_nodot(l: Staging.SpLab, +id: String, h: {rr.nodot(id) == True{} : Bool}) -> {rr.nodot(String.append(Staging.sp_label(l), SCon{'-', id})) == True{} : Bool}:
  match l:
    case Staging.SpImport{}:
      h
    case Staging.SpFork{}:
      h
    case Staging.SpDeleted{}:
      h

# the tail of a minted name is a label, '-' and a uuid
def rr.lab_tail(l: Staging.SpLab, +id: String, u: {Staging.sp_hexn(32n, id) == True{} : Bool}) -> {Staging.sp_tail(String.append(Staging.sp_label(l), SCon{'-', id})) == True{} : Bool}:
  match l:
    case Staging.SpImport{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(_, Bool.or(Staging.sp_uuid(Staging.sp_unprefix("fork-", "import-" ++ id)), Staging.sp_uuid(Staging.sp_unprefix("deleted-", "import-" ++ id)))) == True{} : Bool}
      {==}
    case Staging.SpFork{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(False{}, Bool.or(_, Staging.sp_uuid(Staging.sp_unprefix("deleted-", "fork-" ++ id)))) == True{} : Bool}
      {==}
    case Staging.SpDeleted{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(False{}, Bool.or(False{}, _)) == True{} : Bool}
      {==}

# every name Rust mints is swept
def rr.minted(+t: String, +l: Staging.SpLab, +id: String, full: {String.is_empty(t) == False{} : Bool}, +u: {Staging.sp_hexn(32n, id) == True{} : Bool}) -> {Staging.sp_swept(Staging.sp_mint(t, l, id)) == True{} : Bool}:
  +z = String.append(Staging.sp_label(l), SCon{'-', id})
  +hz = rr.lab_nodot(l, id, rr.hex_nodot(32n, id, u))
  %Equal.sym(Maybe<&2, Staging.SpCut>, Staging.sp_cut(String.append(t, SCon{'.', z})), Some{Staging.SpCut{t, z}}, rr.cut_last(t, z, hz)) : {Bool.and(Char.is_eq('.', '.'), Staging.sp_swept.cut(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(t), False{}, full) : {Bool.and(Bool.not(_), Staging.sp_tail(z)) == True{} : Bool}
  rr.lab_tail(l, id, u)

# n + k + 1 is not n
def rr.ne_add(n: Nat, +k: Nat) -> {Nat.is_eq(Nat.add(n, 1n+k), n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      rr.ne_add(m, k)

# a name and its lock file's name are not the same
def rr.lock_ne(+x: String) -> {LawsBase.text_same(String.append(x, ".lock"), x) == False{} : Bool}:
  +el = Equal.trans(Bool, Nat.is_eq(String.length(String.append(x, ".lock")), String.length(x)), Nat.is_eq(Nat.add(String.length(x), 5n), String.length(x)), False{},
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, String.length(x)), String.length(String.append(x, ".lock")), Nat.add(String.length(x), 5n), LStg.stg.len_app(x, ".lock")),
    rr.ne_add(String.length(x), 4n))
  LStg.stg.same_len(String.append(x, ".lock"), x, el)
