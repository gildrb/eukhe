# eukhe: lemmas the proofs of area staging share

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg

# ---- staging ----

# proof_staging: the staging, sweep and listing laws of laws/staging.bend
# (D2): a sweep never removes a held, young, unreached or unswept entry,
# and removes every stale free leftover it reaches; the real rule judges
# exactly the names Rust mints; a session is listed once, under the
# storage it opens as.

# The sweep's name test, as a proof device (moved from laws/staging.bend:
# no law calls it). It restates the code's recognizer (Sg.swept: cut at
# the last '.', a label, a 32-digit lowercase hex uuid) so the proofs of
# the meet_* laws can take a name apart; the laws state which names are
# judged by the names Rust mints (Staging.sp_mint), not by this test.

def sp_if(ok: Bool, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      m
    case False{}:
      None{}

# s after the prefix p, when s starts with p
def sp_unprefix(p: String, s: String) -> Maybe<&2, String>:
  match p:
    case SNil{}:
      Some{s}
    case SCon{x, pt}:
      match s:
        case SNil{}:
          None{}
        case SCon{y, st}:
          sp_if(Char.is_eq(x, y), sp_unprefix(pt, st))

# the text before the last '.' of a text, and the text after it
type SpCut is Data:
  SpCut{before: String, after: String}

def sp_cut.cons(c: Char, p: SpCut) -> Maybe<&2, SpCut>:
  match p:
    case SpCut{b, a}:
      Some{SpCut{SCon{c, b}, a}}

def sp_cut.dot(d: Bool, t: String) -> Maybe<&2, SpCut>:
  match d:
    case True{}:
      Some{SpCut{SNil{}, t}}
    case False{}:
      None{}

def sp_cut.put(r: Maybe<&2, SpCut>, d: Bool, c: Char, t: String) -> Maybe<&2, SpCut>:
  match r:
    case Some{p}:
      sp_cut.cons(c, p)
    case None{}:
      sp_cut.dot(d, t)

# w split at its last '.'
def sp_cut(w: String) -> Maybe<&2, SpCut>:
  match w:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      sp_cut.put(sp_cut(t), Char.is_eq(c, '.'), c, t)

def sp_uuid(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Staging.sp_hexn(32n, s)

# the part after the last '.': `import-`, `fork-` or `deleted-`, then a uuid
def sp_tail(+a: String) -> Bool:
  Bool.or(sp_uuid(sp_unprefix("import-", a)), Bool.or(sp_uuid(sp_unprefix("fork-", a)), sp_uuid(sp_unprefix("deleted-", a))))

def sp_swept.cut(m: Maybe<&2, SpCut>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      match p:
        case SpCut{b, a}:
          Bool.and(Bool.not(String.is_empty(b)), sp_tail(a))

# s is `.<target>.<label>-<uuid>`, the target not empty
def sp_swept(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(Char.is_eq(c, '.'), sp_swept.cut(sp_cut(t)))

# a plain directory: no swept name, no main.jsonl (R3)
def sp_plain.k(k: Sg.Form, sw: Bool) -> Bool:
  match k:
    case Sg.KDir{main}:
      Bool.and(Bool.not(sw), Bool.not(main))
    case Sg.KFile{}:
      False{}
    case Sg.KOther{}:
      False{}

def sp_plain(e: Sg.Seen) -> Bool:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          sp_plain.k(k, sp_swept(s))
        case Sg.Raw{}:
          sp_plain.k(k, False{})

def sp_plains(es: List<&2, Sg.Seen>) -> List<&2, Bool>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      sp_plain(e) <> sp_plains(rest)

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

def rr.uuid(m: Maybe<&2, String>) -> {Sg.uuid(m) == sp_uuid(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      rr.hexn(32n, s)

def rr.kept(ok: Bool, m: Maybe<&2, String>) -> {Sg.kept_if(ok, m) == sp_if(ok, m) : Maybe<&2, String>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def rr.unprefix(p: String, s: String) -> {Sg.unprefix(p, s) == sp_unprefix(p, s) : Maybe<&2, String>}:
  match p:
    case SNil{}:
      {==}
    case SCon{+x, +pt}:
      match s:
        case SNil{}:
          {==}
        case SCon{+y, +st}:
          %rr.unprefix(pt, st) : {Sg.kept_if(Char.is_eq(x, y), Sg.unprefix(pt, st)) == sp_if(Char.is_eq(x, y), _) : Maybe<&2, String>}
          rr.kept(Char.is_eq(x, y), Sg.unprefix(pt, st))

# the uuid of a label's prefix
def rr.lab(+p: String, +a: String) -> {Sg.uuid(Sg.unprefix(p, a)) == sp_uuid(sp_unprefix(p, a)) : Bool}:
  %rr.unprefix(p, a) : {Sg.uuid(Sg.unprefix(p, a)) == sp_uuid(_) : Bool}
  rr.uuid(Sg.unprefix(p, a))

def rr.tail(+a: String) -> {Sg.tail(a) == sp_tail(a) : Bool}:
  +i = Sg.uuid(Sg.unprefix("import-", a))
  +f = Sg.uuid(Sg.unprefix("fork-", a))
  +d = Sg.uuid(Sg.unprefix("deleted-", a))
  +sf = sp_uuid(sp_unprefix("fork-", a))
  +sd = sp_uuid(sp_unprefix("deleted-", a))
  %rr.lab("import-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(_, Bool.or(sf, sd)) : Bool}
  %rr.lab("fork-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(i, Bool.or(_, sd)) : Bool}
  %rr.lab("deleted-", a) : {Bool.or(i, Bool.or(f, d)) == Bool.or(i, Bool.or(f, _)) : Bool}
  {==}

# the code's split, as the spec's
def rr.sp(m: Maybe<&2, Sg.Split>) -> Maybe<&2, SpCut>:
  match m:
    case None{}:
      None{}
    case Some{p}:
      match p:
        case Sg.Split{b, a}:
          Some{SpCut{b, a}}

def rr.cut_put(r: Maybe<&2, Sg.Split>, d: Bool, +c: Char, +t: String) -> {rr.sp(Sg.cut.put(r, d, c, t)) == sp_cut.put(rr.sp(r), d, c, t) : Maybe<&2, SpCut>}:
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

def rr.cut(w: String) -> {rr.sp(Sg.cut(w)) == sp_cut(w) : Maybe<&2, SpCut>}:
  match w:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, SpCut>, rr.sp(Sg.cut.put(Sg.cut(t), Sg.ch.is(c, 46), c, t)), sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t), rr.cut_put(Sg.cut(t), Sg.ch.is(c, 46), c, t)) : {_ == sp_cut.put(sp_cut(t), Char.is_eq(c, '.'), c, t) : Maybe<&2, SpCut>}
      %rr.cut(t) : {sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t) == sp_cut.put(_, Char.is_eq(c, '.'), c, t) : Maybe<&2, SpCut>}
      %rr.dot(c) : {sp_cut.put(rr.sp(Sg.cut(t)), Sg.ch.is(c, 46), c, t) == sp_cut.put(rr.sp(Sg.cut(t)), _, c, t) : Maybe<&2, SpCut>}
      {==}

def rr.swept_cut(m: Maybe<&2, Sg.Split>) -> {Sg.swept.cut(m) == sp_swept.cut(rr.sp(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Sg.Split{+b, +a}:
          %rr.tail(a) : {Bool.and(Bool.not(String.is_empty(b)), Sg.tail(a)) == Bool.and(Bool.not(String.is_empty(b)), _) : Bool}
          {==}

def rr.swept(s: String) -> {Sg.swept(s) == sp_swept(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +x = Sg.swept.cut(Sg.cut(t))
      %rr.cut(t) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(Char.is_eq(c, '.'), sp_swept.cut(_)) : Bool}
      %rr.swept_cut(Sg.cut(t)) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(Char.is_eq(c, '.'), _) : Bool}
      %rr.dot(c) : {Bool.and(Sg.ch.is(c, 46), x) == Bool.and(_, x) : Bool}
      {==}

# the code's test (less, or equal then nanos at most) is the order by
# seconds, then nanoseconds, for every comparison of the seconds
def rr.by(c: Cmp, +a: Nat, +b: Nat) -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Nat.is_le(a, b))) == Staging.sp_time_le.by(c, a, b) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def rr.stale(+now: Sg.Time, t: Sg.Time) -> {Sg.stale(now, t) == Staging.sp_old(now, t) : Bool}:
  match now:
    case Sg.Time{+ns, +nn}:
      match t:
        case Sg.Time{+ts, +tn}:
          rr.by(Nat.cmp(Nat.add(ts, 86400n), ns), tn, nn)

def rr.stale_all(+now: Sg.Time, ts: List<&2, Sg.Time>) -> {Sg.stale_all(now, ts) == Staging.sp_all_old(now, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +rest:
      %rr.stale(now, t) : {Bool.and(Sg.stale(now, t), Sg.stale_all(now, rest)) == Bool.and(_, Staging.sp_all_old(now, rest)) : Bool}
      %rr.stale_all(now, rest) : {Bool.and(Sg.stale(now, t), Sg.stale_all(now, rest)) == Bool.and(Sg.stale(now, t), _) : Bool}
      {==}

# the plan's staleness is the spec's: judge is judge.go on sp_all_old
def rr.judge_old(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>) -> {Sg.judge.go(Staging.sp_all_old(now, own <> inner), c, l) == Sg.judge(c, l, now, own, inner) : Sg.Plan}:
  %rr.stale_all(now, own <> inner) : {Sg.judge.go(_, c, l) == Sg.judge.go(Sg.stale_all(now, own <> inner), c, l) : Sg.Plan}
  {==}

# ---- the real rule: the sweep's class of an entry ----

# the class meet gives, on the laws' text helpers (sp_swept,
# text_unsuffix, text_has_name): a directory with a swept name is judged;
# any other directory is kept when it holds main.jsonl and entered
# otherwise; a file `<x>.lock`, x a swept name, is judged when no entry
# has the name x; everything else is kept

def rr.m.dir(sw: Bool, main: Bool) -> Sg.Met:
  match sw:
    case True{}:
      Sg.MLeftover{}
    case False{}:
      match main:
        case True{}:
          Sg.MKeep{}
        case False{}:
          Sg.MDescend{}

def rr.m.lock(sw: Bool, there: Bool) -> Sg.Met:
  match sw:
    case True{}:
      match there:
        case True{}:
          Sg.MKeep{}
        case False{}:
          Sg.MOrphan{}
    case False{}:
      Sg.MKeep{}

def rr.m.file(m: Maybe<&2, String>, all: List<&2, Sg.Seen>) -> Sg.Met:
  match m:
    case None{}:
      Sg.MKeep{}
    case Some{+x}:
      rr.m.lock(sp_swept(x), LawsBase.text_has_name(x, all))

def rr.m.utf(k: Sg.Form, +s: String, all: List<&2, Sg.Seen>) -> Sg.Met:
  match k:
    case Sg.KDir{main}:
      rr.m.dir(sp_swept(s), main)
    case Sg.KFile{}:
      rr.m.file(LawsBase.text_unsuffix(".lock", s), all)
    case Sg.KOther{}:
      Sg.MKeep{}

def rr.m(e: Sg.Seen, all: List<&2, Sg.Seen>) -> Sg.Met:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          rr.m.utf(k, s, all)
        case Sg.Raw{}:
          match k:
            case Sg.KDir{main}:
              rr.m.dir(False{}, main)
            case Sg.KFile{}:
              Sg.MKeep{}
            case Sg.KOther{}:
              Sg.MKeep{}

def rr.met_dir(sw: Bool, m: Bool) -> {Sg.met.dir(sw, m) == rr.m.dir(sw, m) : Sg.Met}:
  match sw m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rr.met_lock(sw: Bool, th: Bool) -> {Sg.met.lock(sw, th) == rr.m.lock(sw, th) : Sg.Met}:
  match sw th:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def rr.met_file(m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Sg.met.file(m, all) == rr.m.file(m, all) : Sg.Met}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %rr.swept(x) : {Sg.met.lock(Sg.swept(x), Sg.has_name(x, all)) == rr.m.lock(_, LawsBase.text_has_name(x, all)) : Sg.Met}
      %LStg.stg.has_name(x, all) : {Sg.met.lock(Sg.swept(x), Sg.has_name(x, all)) == rr.m.lock(Sg.swept(x), _) : Sg.Met}
      rr.met_lock(Sg.swept(x), Sg.has_name(x, all))

def rr.met_utf(k: Sg.Form, +s: String, +all: List<&2, Sg.Seen>) -> {Sg.met.utf(k, s, all) == rr.m.utf(k, s, all) : Sg.Met}:
  match k:
    case Sg.KDir{+main}:
      %rr.swept(s) : {Sg.met.dir(Sg.swept(s), main) == rr.m.dir(_, main) : Sg.Met}
      rr.met_dir(Sg.swept(s), main)
    case Sg.KFile{}:
      %LStg.stg.unsuffix(".lock", s) : {Sg.met.file(Sg.unsuffix(".lock", s), all) == rr.m.file(_, all) : Sg.Met}
      rr.met_file(Sg.unsuffix(".lock", s), all)
    case Sg.KOther{}:
      {==}

# the code's class of an entry is rr.m's
def rr.met(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Sg.met(e, all) == rr.m(e, all) : Sg.Met}:
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
def rr.cut_none(z: String, h: {rr.nodot(z) == True{} : Bool}) -> {sp_cut(z) == None{} : Maybe<&2, SpCut>}:
  match z:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hh = h
      +hc = rr.not_t(Char.is_eq(c, '.'), LStg.stg.and_l(Bool.not(Char.is_eq(c, '.')), rr.nodot(t), hh))
      +ht = LStg.stg.and_r(Bool.not(Char.is_eq(c, '.')), rr.nodot(t), hh)
      %Equal.sym(Maybe<&2, SpCut>, sp_cut(t), None{}, rr.cut_none(t, ht)) : {sp_cut.put(_, Char.is_eq(c, '.'), c, t) == None{} : Maybe<&2, SpCut>}
      %Equal.sym(Bool, Char.is_eq(c, '.'), False{}, hc) : {sp_cut.put(None{}, _, c, t) == None{} : Maybe<&2, SpCut>}
      {==}

# t, a '.', then a text z with no '.': the last '.' is that one
def rr.cut_last(t: String, +z: String, +h: {rr.nodot(z) == True{} : Bool}) -> {sp_cut(String.append(t, SCon{'.', z})) == Some{SpCut{t, z}} : Maybe<&2, SpCut>}:
  match t:
    case SNil{}:
      %Equal.sym(Maybe<&2, SpCut>, sp_cut(z), None{}, rr.cut_none(z, h)) : {sp_cut.put(_, Char.is_eq('.', '.'), '.', z) == Some{SpCut{SNil{}, z}} : Maybe<&2, SpCut>}
      {==}
    case SCon{+c, +u}:
      +w = String.append(u, SCon{'.', z})
      %Equal.sym(Maybe<&2, SpCut>, sp_cut(w), Some{SpCut{u, z}}, rr.cut_last(u, z, h)) : {sp_cut.put(_, Char.is_eq(c, '.'), c, w) == Some{SpCut{SCon{c, u}, z}} : Maybe<&2, SpCut>}
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
def rr.lab_tail(l: Staging.SpLab, +id: String, u: {Staging.sp_hexn(32n, id) == True{} : Bool}) -> {sp_tail(String.append(Staging.sp_label(l), SCon{'-', id})) == True{} : Bool}:
  match l:
    case Staging.SpImport{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(_, Bool.or(sp_uuid(sp_unprefix("fork-", "import-" ++ id)), sp_uuid(sp_unprefix("deleted-", "import-" ++ id)))) == True{} : Bool}
      {==}
    case Staging.SpFork{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(False{}, Bool.or(_, sp_uuid(sp_unprefix("deleted-", "fork-" ++ id)))) == True{} : Bool}
      {==}
    case Staging.SpDeleted{}:
      %Equal.sym(Bool, Staging.sp_hexn(32n, id), True{}, u) : {Bool.or(False{}, Bool.or(False{}, _)) == True{} : Bool}
      {==}

# every name Rust mints is swept
def rr.minted(+t: String, +l: Staging.SpLab, +id: String, full: {String.is_empty(t) == False{} : Bool}, +u: {Staging.sp_hexn(32n, id) == True{} : Bool}) -> {sp_swept(Staging.sp_mint(t, l, id)) == True{} : Bool}:
  +z = String.append(Staging.sp_label(l), SCon{'-', id})
  +hz = rr.lab_nodot(l, id, rr.hex_nodot(32n, id, u))
  %Equal.sym(Maybe<&2, SpCut>, sp_cut(String.append(t, SCon{'.', z})), Some{SpCut{t, z}}, rr.cut_last(t, z, hz)) : {Bool.and(Char.is_eq('.', '.'), sp_swept.cut(_)) == True{} : Bool}
  %Equal.sym(Bool, String.is_empty(t), False{}, full) : {Bool.and(Bool.not(_), sp_tail(z)) == True{} : Bool}
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

# ---- the real rule: where a class is, and what a judged name is ----

# the class of the entry after pre is the class at the index |pre|
def mm.at(pre: List<&2, Sg.Seen>, +x: Sg.Seen, +post: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {List.get(&2, Sg.Met, Sg.meet.go(List.append(&2, Sg.Seen, pre, x <> post), all), List.length(&2, Sg.Seen, pre)) == Some{Sg.met(x, all)} : Maybe<&2, Sg.Met>}:
  match pre:
    case Nil{}:
      {==}
    case e <> +rest:
      mm.at(rest, x, post, all)

# an entry anywhere in a listing gets the class rr.m gives it there
def mm.found(+pre: List<&2, Sg.Seen>, +x: Sg.Seen, +post: List<&2, Sg.Seen>, -w: Sg.Met, r: {rr.m(x, List.append(&2, Sg.Seen, pre, x <> post)) == w : Sg.Met}) -> {List.get(&2, Sg.Met, Sg.meet(List.append(&2, Sg.Seen, pre, x <> post)), List.length(&2, Sg.Seen, pre)) == Some{w} : Maybe<&2, Sg.Met>}:
  +es = List.append(&2, Sg.Seen, pre, x <> post)
  Equal.trans(Maybe<&2, Sg.Met>, List.get(&2, Sg.Met, Sg.meet(es), List.length(&2, Sg.Seen, pre)), Some{Sg.met(x, es)}, Some{w}, mm.at(pre, x, post, es),
    Equal.cong(Sg.Met, Maybe<&2, Sg.Met>, z => Some{z}, Sg.met(x, es), w, Equal.trans(Sg.Met, Sg.met(x, es), rr.m(x, es), w, rr.met(x, es), r)))

# Impossible classes

def mi.MD(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def mi.none_some(-A: Data, -G: Type, -x: A, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : mi.MD(A, _, G)
  Unit{}

def mi.val(m: Maybe<&2, Sg.Met>) -> Sg.Met:
  match m:
    case None{}:
      Sg.MKeep{}
    case Some{x}:
      x

# G at a judged directory, nothing to prove elsewhere
def mi.TL(m: Sg.Met, G: Type) -> Type:
  match m:
    case Sg.MKeep{}:
      Unit
    case Sg.MDescend{}:
      Unit
    case Sg.MLeftover{}:
      G
    case Sg.MOrphan{}:
      Unit

# G at a judged lock file, nothing to prove elsewhere
def mi.TO(m: Sg.Met, G: Type) -> Type:
  match m:
    case Sg.MKeep{}:
      Unit
    case Sg.MDescend{}:
      Unit
    case Sg.MLeftover{}:
      Unit
    case Sg.MOrphan{}:
      G

def mi.absurd_l(-G: Type, -m: Sg.Met, e: {m == Sg.MLeftover{} : Sg.Met}, u: mi.TL(m, G)) -> G:
  %e : mi.TL(_, G)
  u

def mi.absurd_o(-G: Type, -m: Sg.Met, e: {m == Sg.MOrphan{} : Sg.Met}, u: mi.TO(m, G)) -> G:
  %e : mi.TO(_, G)
  u

# a lock file's class is never a judged directory
def mi.lock_l(-G: Type, a: Bool, b: Bool) -> mi.TL(rr.m.lock(a, b), G):
  match a b:
    case True{} True{}:
      Unit{}
    case True{} False{}:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

def mi.file_l(-G: Type, m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> mi.TL(rr.m.file(m, all), G):
  match m:
    case None{}:
      Unit{}
    case Some{+x}:
      mi.lock_l(G, sp_swept(x), LawsBase.text_has_name(x, all))

# a directory with no swept name is never judged
def mi.dirf_l(-G: Type, main: Bool) -> mi.TL(rr.m.dir(False{}, main), G):
  match main:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

# a directory is never a judged lock file
def mi.dir_o(-G: Type, a: Bool, main: Bool) -> mi.TO(rr.m.dir(a, main), G):
  match a main:
    case True{} True{}:
      Unit{}
    case True{} False{}:
      Unit{}
    case False{} True{}:
      Unit{}
    case False{} False{}:
      Unit{}

# Texts taken apart

# s ends with p, x before it
def mi.US(p: String, s: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      {s == String.append(x, p) : String}

def mi.uns.nil(p: String) -> mi.US(p, SNil{}, LawsBase.text_found(String.is_empty(p), None{})):
  match p:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Unit{}

def mi.uns.cons(+c: Char, -t: String, -p: String, m: Maybe<&2, String>, ih: mi.US(p, t, m)) -> mi.US(p, SCon{c, t}, LawsBase.text_cons(c, m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      Equal.cong(String, String, z => SCon{c, z}, t, String.append(r, p), ih)

def mi.uns.found(b: Bool, +s: String, +p: String, -m: Maybe<&2, String>, eb: {LawsBase.text_same(s, p) == b : Bool}, ih: mi.US(p, s, m)) -> mi.US(p, s, LawsBase.text_found(b, m)):
  match b:
    case True{}:
      LStg.stg.same_eq(s, p, eb)
    case False{}:
      ih

# text_unsuffix(p, s) is Some{x} only when s is x then p
def mi.uns(+p: String, s: String) -> mi.US(p, s, LawsBase.text_unsuffix(p, s)):
  match s:
    case SNil{}:
      mi.uns.nil(p)
    case SCon{+c, +t}:
      mi.uns.found(LawsBase.text_same(SCon{c, t}, p), SCon{c, t}, p, LawsBase.text_cons(c, LawsBase.text_unsuffix(p, t)), {==}, mi.uns.cons(c, t, p, LawsBase.text_unsuffix(p, t), mi.uns(p, t)))

# w is b, a '.', then a
def mi.CS(w: String, m: Maybe<&2, SpCut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{q}:
      match q:
        case SpCut{b, a}:
          {w == String.append(b, SCon{'.', a}) : String}

def mi.cut.put(r: Maybe<&2, SpCut>, d: Bool, +c: Char, +t: String, ed: {Char.is_eq(c, '.') == d : Bool}, ih: mi.CS(t, r)) -> mi.CS(SCon{c, t}, sp_cut.put(r, d, c, t)):
  match r:
    case Some{q}:
      match q:
        case SpCut{b, a}:
          Equal.cong(String, String, z => SCon{c, z}, t, String.append(b, SCon{'.', a}), ih)
    case None{}:
      match d:
        case True{}:
          Equal.cong(Char, String, z => SCon{z, t}, c, '.', LStg.stg.char_sound(c, '.', ed))
        case False{}:
          Unit{}

# sp_cut splits a text only at a '.'
def mi.cut(w: String) -> mi.CS(w, sp_cut(w)):
  match w:
    case SNil{}:
      Unit{}
    case SCon{+c, +t}:
      mi.cut.put(sp_cut(t), Char.is_eq(c, '.'), c, t, {==}, mi.cut(t))

# a is p then r
def mi.PS(p: String, a: String, m: Maybe<&2, String>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      {a == String.append(p, r) : String}

def mi.pre.if(b: Bool, +x: Char, +y: Char, -pt: String, -st: String, m: Maybe<&2, String>, eb: {Char.is_eq(x, y) == b : Bool}, ih: mi.PS(pt, st, m)) -> mi.PS(SCon{x, pt}, SCon{y, st}, sp_if(b, m)):
  match b:
    case True{}:
      match m:
        case None{}:
          Unit{}
        case Some{r}:
          %LStg.stg.char_sound(x, y, eb) : {SCon{_, st} == SCon{x, String.append(pt, r)} : String}
          Equal.cong(String, String, z => SCon{x, z}, st, String.append(pt, r), ih)
    case False{}:
      Unit{}

# sp_unprefix(p, a) is Some{r} only when a is p then r
def mi.pre(p: String, a: String) -> mi.PS(p, a, sp_unprefix(p, a)):
  match p:
    case SNil{}:
      {==}
    case SCon{+x, +pt}:
      match a:
        case SNil{}:
          Unit{}
        case SCon{+y, +st}:
          mi.pre.if(Char.is_eq(x, y), x, y, pt, st, sp_unprefix(pt, st), {==}, mi.pre(pt, st))

# a judged tail: a label, '-' and a 32-digit lowercase hex uuid
def mi.TS(a: String) -> Type:
  Sigma<&1, &1, Staging.SpLab, l => Sigma<&1, &1, String, id => {a == String.append(Staging.sp_label(l), SCon{'-', id}) : String} & {Staging.sp_hexn(32n, id) == True{} : Bool}>>

def mi.lab(l: Staging.SpLab, -a: String, m: Maybe<&2, String>, ps: mi.PS(String.append(Staging.sp_label(l), "-"), a, m), h: {sp_uuid(m) == True{} : Bool}) -> mi.TS(a):
  match l:
    case Staging.SpImport{}:
      match m:
        case None{}:
          LStg.stg.absurdF(mi.TS(a), h)
        case Some{+r}:
          (Staging.SpImport{}, (r, (ps, h)))
    case Staging.SpFork{}:
      match m:
        case None{}:
          LStg.stg.absurdF(mi.TS(a), h)
        case Some{+r}:
          (Staging.SpFork{}, (r, (ps, h)))
    case Staging.SpDeleted{}:
      match m:
        case None{}:
          LStg.stg.absurdF(mi.TS(a), h)
        case Some{+r}:
          (Staging.SpDeleted{}, (r, (ps, h)))

def mi.tail.f(b: Bool, +a: String, eb: {sp_uuid(sp_unprefix("fork-", a)) == b : Bool}, h: {Bool.or(b, sp_uuid(sp_unprefix("deleted-", a))) == True{} : Bool}) -> mi.TS(a):
  match b:
    case True{}:
      mi.lab(Staging.SpFork{}, a, sp_unprefix("fork-", a), mi.pre("fork-", a), eb)
    case False{}:
      mi.lab(Staging.SpDeleted{}, a, sp_unprefix("deleted-", a), mi.pre("deleted-", a), h)

def mi.tail.i(b: Bool, +a: String, eb: {sp_uuid(sp_unprefix("import-", a)) == b : Bool}, h: {Bool.or(b, Bool.or(sp_uuid(sp_unprefix("fork-", a)), sp_uuid(sp_unprefix("deleted-", a)))) == True{} : Bool}) -> mi.TS(a):
  match b:
    case True{}:
      mi.lab(Staging.SpImport{}, a, sp_unprefix("import-", a), mi.pre("import-", a), eb)
    case False{}:
      mi.tail.f(sp_uuid(sp_unprefix("fork-", a)), a, {==}, h)

def mi.tail(+a: String, h: {sp_tail(a) == True{} : Bool}) -> mi.TS(a):
  mi.tail.i(sp_uuid(sp_unprefix("import-", a)), a, {==}, h)

# s is a name Rust mints
def mi.MS(s: String) -> Type:
  Sigma<&1, &1, String, t => Sigma<&1, &1, Staging.SpLab, l => Sigma<&1, &1, String, id => {s == Staging.sp_mint(t, l, id) : String} & ({String.is_empty(t) == False{} : Bool} & {Staging.sp_hexn(32n, id) == True{} : Bool})>>>

def mi.swept.fin(-c: Char, -w: String, +b: String, -a: String, cs: {w == String.append(b, SCon{'.', a}) : String}, ec: {c == '.' : Char}, hb: {String.is_empty(b) == False{} : Bool}, ts: mi.TS(a)) -> mi.MS(SCon{c, w}):
  (+l, (+id, (ea, hid))) = ts
  +e1 = Equal.cong(Char, String, z => SCon{z, w}, c, '.', ec)
  +e2 = Equal.cong(String, String, z => SCon{'.', z}, w, String.append(b, SCon{'.', a}), cs)
  +e3 = Equal.cong(String, String, z => SCon{'.', String.append(b, SCon{'.', z})}, a, String.append(Staging.sp_label(l), SCon{'-', id}), ea)
  +e = Equal.trans(String, SCon{c, w}, SCon{'.', w}, Staging.sp_mint(b, l, id), e1, Equal.trans(String, SCon{'.', w}, SCon{'.', String.append(b, SCon{'.', a})}, Staging.sp_mint(b, l, id), e2, e3))
  (b, (l, (id, (e, (hb, hid)))))

def mi.swept.cut(-c: Char, -w: String, m: Maybe<&2, SpCut>, cs: mi.CS(w, m), h: {sp_swept.cut(m) == True{} : Bool}, ec: {c == '.' : Char}) -> mi.MS(SCon{c, w}):
  match m:
    case None{}:
      LStg.stg.absurdF(mi.MS(SCon{c, w}), h)
    case Some{q}:
      match q:
        case SpCut{+b, +a}:
          +hh = h
          +hb = LStg.stg.and_l(Bool.not(String.is_empty(b)), sp_tail(a), hh)
          +ha = LStg.stg.and_r(Bool.not(String.is_empty(b)), sp_tail(a), hh)
          mi.swept.fin(c, w, b, a, cs, ec, rr.not_t(String.is_empty(b), hb), mi.tail(a, ha))

# a swept name is a name Rust mints
def mi.swept(s: String, h: {sp_swept(s) == True{} : Bool}) -> mi.MS(s):
  match s:
    case SNil{}:
      LStg.stg.absurdF(mi.MS(SNil{}), h)
    case SCon{+c, +w}:
      +hh = h
      +hc = LStg.stg.and_l(Char.is_eq(c, '.'), sp_swept.cut(sp_cut(w)), hh)
      +hw = LStg.stg.and_r(Char.is_eq(c, '.'), sp_swept.cut(sp_cut(w)), hh)
      mi.swept.cut(c, w, sp_cut(w), mi.cut(w), hw, LStg.stg.char_sound(c, '.', hc))
