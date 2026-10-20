# proof_documents: the lemmas behind the laws of laws/documents.bend
# (Docs.<law> in PROOF.bend delegates here; the lines and endings laws
# delegate to bend/proof_doc_lines.bend), one section per model of
# bend/doc_*.bend. Each section keeps its own name prefix: pc. (an edit of
# many files, the write tool, a move, the temp sweep), pv. (seen lines),
# ps. (what grep searched, continuations), pdt. (tags).

import Base
import ./doc_commit.bend as Cm
import ./doc_seen.bend as Ds
import ./doc_search.bend as Sr
import ./doc_tags.bend as Dt

# ==== commit ====
# proof_doc_commit: the edit, write, move and sweep laws of
# laws/documents.bend (F1, F9, F2, F5, F10): the reply of an edit names
# exactly the files that landed, a conflict lands nothing, a sound edit
# lands every file; a write never replaces a version the session did not
# see; a move never replaces a file; a sweep removes only the free
# temporary files of its target, and all of them.
# Logic and numbers
# -----------------

def pc.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pc.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pc.BD(_, Unit, A)
  Unit{}

def pc.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pc.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      pc.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %pc.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def pc.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_refl(p)

def pc.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.or_false_l(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pc.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pc.or_false_r(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pc.absurd({b == False{} : Bool}, h)
    case False{}:
      h

# Edit
# ----

# with no publish, the reply applies no file
def pc.none_applied(fs: List<&2, Cm.Doc>, +n: Nat) -> {Cm.applied(Cm.report(fs, Nil{}), n) == Nil{} : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      pc.none_applied(rest, 1n+n)

def pc.step(-f: Cm.Doc, +rest: List<&2, Cm.Doc>, +n: Nat, o: Cm.Out, ih: {Cm.applied(Cm.report(rest, Cm.run(rest)), 1n+n) == Cm.landed.go(rest, 1n+n) : List<&2, Nat>}) -> {Cm.applied(Cm.report(f <> rest, Cm.run.put(o, Cm.run(rest))), n) == Cm.landed.put(n, Cm.landed.go(rest, 1n+n), o) : List<&2, Nat>}:
  match o:
    case Cm.Landed{w}:
      %ih : {n <> Cm.applied(Cm.report(rest, Cm.run(rest)), 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Failed{}:
      pc.none_applied(rest, 1n+n)

# the reply built from the publishes applies the files that landed
def pc.reported(fs: List<&2, Cm.Doc>, +n: Nat) -> {Cm.applied(Cm.report(fs, Cm.run(fs)), n) == Cm.landed.go(fs, n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      pc.step(f, rest, n, Cm.publish(f), pc.reported(rest, 1n+n))

def pc.go.step(-f: Cm.Doc, +rest: List<&2, Cm.Doc>, o: Cm.Out) -> {Cm.reported(Cm.reply.go(Cm.run.put(o, Cm.run(rest)), f <> rest)) == Cm.landed.put(0n, Cm.landed.go(rest, 1n), o) : List<&2, Nat>}:
  match o:
    case Cm.Landed{+w}:
      pc.step(f, rest, 0n, Cm.Landed{w}, pc.reported(rest, 1n))
    case Cm.Failed{}:
      {==}

def pc.go(fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply.go(Cm.run(fs), fs)) == Cm.landed.go(fs, 0n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case +f <> +rest:
      pc.go.step(f, rest, Cm.publish(f))

def pc.pick(c: Bool, +fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply.pick(c, fs)) == Cm.landed.pick(c, fs) : List<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      pc.go(fs)

# the law edit_reports_what_landed
def pc.reports_what_landed(+fs: List<&2, Cm.Doc>) -> {Cm.reported(Cm.reply(fs)) == Cm.landed(fs) : List<&2, Nat>}:
  pc.pick(Cm.conflict(fs), fs)

# a changed file anywhere is a conflict
def pc.conflict_at(pre: List<&2, Cm.Doc>, +k: Cm.Op, +x: Cm.Fault, +post: List<&2, Cm.Doc>) -> {Cm.conflict(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      {==}
    case g <> rest:
      match g:
        case Cm.Doc{gk, gc, gx}:
          %Equal.sym(Bool, Cm.conflict(List.append(&2, Cm.Doc, rest, Cm.Doc{k, True{}, x} <> post)), True{}, pc.conflict_at(rest, k, x, post)) : {Bool.or(gc, _) == True{} : Bool}
          pc.or_t(gc)

# the law edit_all_or_nothing_on_conflict
def pc.all_or_nothing(+pre: List<&2, Cm.Doc>, +k: Cm.Op, +x: Cm.Fault, +post: List<&2, Cm.Doc>) -> {Cm.landed(List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post)) == Nil{} : List<&2, Nat>}:
  +fs = {List.append(&2, Cm.Doc, pre, Cm.Doc{k, True{}, x} <> post) : List<&2, Cm.Doc>}
  %Equal.sym(Bool, Cm.conflict(fs), True{}, pc.conflict_at(pre, k, x, post)) : {Cm.landed.pick(_, fs) == Nil{} : List<&2, Nat>}
  {==}

def pc.lands_put(x: Cm.Fault, k: Cm.Op, -rest: List<&2, Cm.Doc>, +n: Nat, ok: {Bool.or(Cm.Fault.fails(x), Cm.failing(rest)) == False{} : Bool}, ih: {Cm.failing(rest) == False{} : Bool} -> {Cm.landed.go(rest, 1n+n) == Cm.ids(rest, 1n+n) : List<&2, Nat>}) -> {Cm.landed.put(n, Cm.landed.go(rest, 1n+n), Cm.publish.go(x, k)) == n <> Cm.ids(rest, 1n+n) : List<&2, Nat>}:
  match x:
    case Cm.Clean{}:
      %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Sync{}:
      %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
      {==}
    case Cm.Publish{}:
      pc.absurd({Cm.landed.put(n, Cm.landed.go(rest, 1n+n), Cm.Failed{}) == n <> Cm.ids(rest, 1n+n) : List<&2, Nat>}, ok)
    case Cm.Remove{}:
      match k:
        case Cm.Update{}:
          %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
          {==}
        case Cm.Moving{}:
          %ih(ok) : {n <> Cm.landed.go(rest, 1n+n) == n <> _ : List<&2, Nat>}
          {==}

# with no failed publish, every file lands
def pc.lands_go(fs: List<&2, Cm.Doc>, +n: Nat, ok: {Cm.failing(fs) == False{} : Bool}) -> {Cm.landed.go(fs, n) == Cm.ids(fs, n) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case g <> +rest:
      match g:
        case Cm.Doc{k, c, x}:
          pc.lands_put(x, k, rest, n, ok, h => pc.lands_go(rest, 1n+n, h))

# the law edit_lands_every_file
def pc.lands_every_file(+fs: List<&2, Cm.Doc>, same: {Cm.conflict(fs) == False{} : Bool}, sound: {Cm.failing(fs) == False{} : Bool}) -> {Cm.landed(fs) == Cm.ids(fs, 0n) : List<&2, Nat>}:
  %Equal.sym(Bool, Cm.conflict(fs), False{}, same) : {Cm.landed.pick(_, fs) == Cm.ids(fs, 0n) : List<&2, Nat>}
  pc.lands_go(fs, 0n, sound)

# Write
# -----

# the law write_never_loses_unseen
def pc.write_refused(+d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, lost: {Cm.unseen(d, s) == True{} : Bool}) -> {Cm.write(d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}:
  %Equal.sym(Bool, Cm.unseen(d, s), True{}, lost) : {Cm.write.go(_, d, s, c) == Cm.Wt{False{}, d, s} : Cm.Wt}
  {==}

# the law write_writes_seen
def pc.write_writes(+d: Maybe<&2, Nat>, +s: List<&2, Nat>, +c: Nat, kept: {Cm.unseen(d, s) == False{} : Bool}) -> {Cm.write(d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}:
  %Equal.sym(Bool, Cm.unseen(d, s), False{}, kept) : {Cm.write.go(_, d, s, c) == Cm.Wt{True{}, Some{c}, Cm.saw(c, s)} : Cm.Wt}
  {==}

# Move
# ----

# the law move_never_overwrites
def pc.move_taken(+s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, taken: {Cm.has(t, es) == True{} : Bool}) -> {Cm.move(s, t, es) == Cm.Mv{False{}, es} : Cm.Mv}:
  %Equal.sym(Bool, Cm.has(t, es), True{}, taken) : {Cm.move.go(s, t, _, es) == Cm.Mv{False{}, es} : Cm.Mv}
  {==}

# a free name is not the name of a file that is there
def pc.ne.go(+t: Nat, +s: Nat, -es: List<&2, Cm.Entry>, b: Bool, eb: {Nat.is_eq(t, s) == b : Bool}, free: {Cm.has(t, es) == False{} : Bool}, from: {Cm.has(s, es) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      same = {Equal.cong(Nat, Bool, y => Cm.has(y, es), s, t, Equal.sym(Nat, t, s, pc.eq_true(t, s, eb))) : {Cm.has(s, es) == Cm.has(t, es) : Bool}}
      Equal.trans(Bool, True{}, Cm.has(s, es), False{}, Equal.sym(Bool, Cm.has(s, es), True{}, from), Equal.trans(Bool, Cm.has(s, es), Cm.has(t, es), False{}, same, free))
    case False{}:
      {==}

def pc.gone.put(+s: Nat, +t: Nat, +m: Nat, g: Nat, -r: List<&2, Cm.Entry>, b: Bool, eb: {Nat.is_eq(m, s) == b : Bool}, ne: {Nat.is_eq(t, s) == False{} : Bool}, ih: {Cm.has(s, r) == False{} : Bool}) -> {Cm.has(s, Cm.rename.put(t, m, g, r, b)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(t, s), False{}, ne) : {Bool.or(_, Cm.has(s, r)) == False{} : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(m, s), False{}, eb) : {Bool.or(_, Cm.has(s, r)) == False{} : Bool}
      ih

# after the move no file has the source name
def pc.gone(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>, +ne: {Nat.is_eq(t, s) == False{} : Bool}) -> {Cm.has(s, Cm.rename(s, t, es)) == False{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, g}:
          pc.gone.put(s, t, m, g, Cm.rename(s, t, rest), Nat.is_eq(m, s), {==}, ne, pc.gone(s, t, rest, ne))

def pc.lands.put(+s: Nat, +t: Nat, +m: Nat, +g: Nat, -r: List<&2, Cm.Entry>, -rest: List<&2, Cm.Entry>, b: Bool, hm: {Nat.is_eq(m, t) == False{} : Bool}, ih: {Cm.get(t, r) == Cm.get(s, rest) : Maybe<&2, Nat>}) -> {Cm.get(t, Cm.rename.put(t, m, g, r, b)) == Cm.get.put(b, g, Cm.get(s, rest)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(t, t), True{}, pc.eq_refl(t)) : {Cm.get.put(_, g, Cm.get(t, r)) == Some{g} : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(m, t), False{}, hm) : {Cm.get.put(_, g, Cm.get(t, r)) == Cm.get(s, rest) : Maybe<&2, Nat>}
      ih

# after the move the destination holds what the source held
def pc.lands(+s: Nat, +t: Nat, es: List<&2, Cm.Entry>, +free: {Cm.has(t, es) == False{} : Bool}) -> {Cm.get(t, Cm.rename(s, t, es)) == Cm.get(s, es) : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cm.Entry{+m, +g}:
          pc.lands.put(s, t, m, g, Cm.rename(s, t, rest), rest, Nat.is_eq(m, s), pc.or_false_l(Nat.is_eq(m, t), Cm.has(t, rest), free), pc.lands(s, t, rest, pc.or_false_r(Nat.is_eq(m, t), Cm.has(t, rest), free)))

# the law move_moves
def pc.move_moves(+s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, +free: {Cm.has(t, es) == False{} : Bool}, +from: {Cm.has(s, es) == True{} : Bool}) -> {Cm.Mv.ok(Cm.move(s, t, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move(s, t, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move(s, t, es))) == Cm.get(s, es) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Cm.has(t, es), False{}, free) : {Cm.Mv.ok(Cm.move.go(s, t, _, es)) == True{} : Bool} & {Cm.has(s, Cm.Mv.es(Cm.move.go(s, t, _, es))) == False{} : Bool} & {Cm.get(t, Cm.Mv.es(Cm.move.go(s, t, _, es))) == Cm.get(s, es) : Maybe<&2, Nat>}
  ({==}, (pc.gone(s, t, es, pc.ne.go(t, s, es, Nat.is_eq(t, s), {==}, free, from)), pc.lands(s, t, es, free)))

# Sweep
# -----

def pc.put_app(+n: Cm.Temp, a: List<&2, Cm.Temp>, +c: List<&2, Cm.Temp>, b: Bool) -> {Cm.sweep.put(n, List.append(&2, Cm.Temp, a, c), b) == List.append(&2, Cm.Temp, Cm.sweep.put(n, a, b), c) : List<&2, Cm.Temp>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.sweep_app(pre: List<&2, Cm.Temp>, +x: List<&2, Cm.Temp>) -> {List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(x)) == Cm.sweep(List.append(&2, Cm.Temp, pre, x)) : List<&2, Cm.Temp>}:
  match pre:
    case Nil{}:
      {==}
    case +n <> +rest:
      %pc.put_app(n, Cm.sweep(rest), Cm.sweep(x), Cm.removes(n)) : {_ == Cm.sweep.put(n, Cm.sweep(List.append(&2, Cm.Temp, rest, x)), Cm.removes(n)) : List<&2, Cm.Temp>}
      %pc.sweep_app(rest, x) : {Cm.sweep.put(n, List.append(&2, Cm.Temp, Cm.sweep(rest), Cm.sweep(x)), Cm.removes(n)) == Cm.sweep.put(n, _, Cm.removes(n)) : List<&2, Cm.Temp>}
      {==}

# an entry the sweep keeps: the sweep of the whole is the sweep of the parts
def pc.kept(+pre: List<&2, Cm.Temp>, +n: Cm.Temp, +post: List<&2, Cm.Temp>, no: {False{} == Cm.removes(n) : Bool}) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, n <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  %pc.sweep_app(pre, n <> post) : {_ == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}
  %no : {List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep.put(n, Cm.sweep(post), _)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}
  {==}

def pc.no_held(+i: Nat, k: Cm.Sort) -> {False{} == Cm.removes(Cm.Temp{i, k, True{}}) : Bool}:
  match k:
    case Cm.Own{}:
      {==}
    case Cm.Foreign{}:
      {==}
    case Cm.Plain{}:
      {==}

# the law temp_sweep_never_held
def pc.sweep_never_held(+pre: List<&2, Cm.Temp>, +i: Nat, +k: Cm.Sort, +post: List<&2, Cm.Temp>) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, True{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  pc.kept(pre, Cm.Temp{i, k, True{}}, post, pc.no_held(i, k))

def pc.no_other(+i: Nat, +k: Cm.Sort, +h: Bool, other: {Cm.Sort.own(k) == False{} : Bool}) -> {False{} == Cm.removes(Cm.Temp{i, k, h}) : Bool}:
  %Equal.sym(Bool, Cm.Sort.own(k), False{}, other) : {False{} == Bool.and(_, Bool.not(h)) : Bool}
  {==}

# the law temp_sweep_only_own
def pc.sweep_only_own(+pre: List<&2, Cm.Temp>, +i: Nat, +k: Cm.Sort, +h: Bool, +post: List<&2, Cm.Temp>, other: {Cm.Sort.own(k) == False{} : Bool}) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, k, h} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.sweep(post)) : List<&2, Cm.Temp>}:
  pc.kept(pre, Cm.Temp{i, k, h}, post, pc.no_other(i, k, h, other))

# the law temp_sweep_removes_free
def pc.sweep_removes_free(+pre: List<&2, Cm.Temp>, +i: Nat, +post: List<&2, Cm.Temp>) -> {Cm.sweep(List.append(&2, Cm.Temp, pre, Cm.Temp{i, Cm.Own{}, False{}} <> post)) == List.append(&2, Cm.Temp, Cm.sweep(pre), Cm.Temp{i, Cm.Own{}, False{}} <> Cm.sweep(post)) : List<&2, Cm.Temp>}:
  +n = {Cm.Temp{i, Cm.Own{}, False{}} : Cm.Temp}
  %pc.sweep_app(pre, n <> post) : {_ == List.append(&2, Cm.Temp, Cm.sweep(pre), n <> Cm.sweep(post)) : List<&2, Cm.Temp>}
  {==}

# ==== seen ====
# proof_doc_seen: the seen-line laws of laws/documents.bend (F11): an
# edit applies only on seen anchors, an edit on seen anchors applies, and
# a rejection marks its anchors seen, so a straight retry applies.
# Logic and numbers
# -----------------

def pv.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pv.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pv.BD(_, Unit, A)
  Unit{}

def pv.LD(xs: List<&2, Nat>, A: Type) -> Type:
  match xs:
    case Nil{}:
      A
    case x <> rest:
      Unit

def pv.cons_nil(-A: Type, +a: Nat, u: List<&2, Nat>, e: {a <> u == Nil{} : List<&2, Nat>}) -> A:
  %e : pv.LD(_, A)
  Unit{}

def pv.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pv.eq_refl(p)

def pv.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pv.and_l(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {p == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      pv.absurd({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def pv.and_r(p: Bool, q: Bool, h: {Bool.and(p, q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      h
    case False{}:
      pv.absurd({q == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def pv.and_tt(p: Bool, q: Bool, hp: {p == True{} : Bool}, hq: {q == True{} : Bool}) -> {Bool.and(p, q) == True{} : Bool}:
  %Equal.sym(Bool, p, True{}, hp) : {Bool.and(_, q) == True{} : Bool}
  hq

def pv.le_succ(m: Nat, k: Nat, h: {Nat.is_le(m, k) == True{} : Bool}) -> {Nat.is_le(m, 1n+k) == True{} : Bool}:
  match m k:
    case 0n k:
      {==}
    case 1n+p 0n:
      pv.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      pv.le_succ(p, q, h)

# Membership
# ----------

def pv.mem_head(+a: Nat, ys: List<&2, Nat>) -> {Ds.mem(a, a <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_eq(a, a), True{}, pv.eq_refl(a)) : {Bool.or(_, Ds.mem(a, ys)) == True{} : Bool}
  {==}

def pv.mem_cons(+b: Nat, +x: Nat, ys: List<&2, Nat>, h: {Ds.mem(x, ys) == True{} : Bool}) -> {Ds.mem(x, b <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Ds.mem(x, ys), True{}, h) : {Bool.or(Nat.is_eq(b, x), _) == True{} : Bool}
  pv.or_t(Nat.is_eq(b, x))

def pv.mem_app(+a: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, h: {Ds.mem(a, ys) == True{} : Bool}) -> {Ds.mem(a, List.append(&2, Nat, xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +rest:
      pv.mem_cons(x, a, List.append(&2, Nat, rest, ys), pv.mem_app(a, rest, ys, h))

def pv.sub_cons(xs: List<&2, Nat>, +b: Nat, +ys: List<&2, Nat>, +h: {Ds.subset(xs, ys) == True{} : Bool}) -> {Ds.subset(xs, b <> ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hm = pv.and_l(Ds.mem(x, ys), Ds.subset(rest, ys), h)
      +hr = pv.and_r(Ds.mem(x, ys), Ds.subset(rest, ys), h)
      pv.and_tt(Ds.mem(x, b <> ys), Ds.subset(rest, b <> ys), pv.mem_cons(b, x, ys, hm), pv.sub_cons(rest, b, ys, hr))

# An applied edit: its anchors are seen
# -------------------------------------

def pv.applied_nil(+seen: List<&2, Nat>, u: List<&2, Nat>, h: {Ds.Step.applied(Ds.edit.go(seen, u)) == True{} : Bool}) -> {u == Nil{} : List<&2, Nat>}:
  match u:
    case Nil{}:
      {==}
    case x <> rest:
      pv.absurd({x <> rest == Nil{} : List<&2, Nat>}, Equal.sym(Bool, False{}, True{}, h))

def pv.put_nil_seen(+a: Nat, u: List<&2, Nat>, b: Bool, h: {Ds.unseen.put(a, u, b) == Nil{} : List<&2, Nat>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pv.cons_nil({False{} == True{} : Bool}, a, u, h)

def pv.put_nil_rest(+a: Nat, u: List<&2, Nat>, b: Bool, h: {Ds.unseen.put(a, u, b) == Nil{} : List<&2, Nat>}) -> {u == Nil{} : List<&2, Nat>}:
  match b:
    case True{}:
      h
    case False{}:
      pv.cons_nil({u == Nil{} : List<&2, Nat>}, a, u, h)

def pv.nil_subset(+seen: List<&2, Nat>, anchors: List<&2, Nat>, +h: {Ds.unseen(seen, anchors) == Nil{} : List<&2, Nat>}) -> {Ds.subset(anchors, seen) == True{} : Bool}:
  match anchors:
    case Nil{}:
      {==}
    case +a <> +rest:
      +u = Ds.unseen(seen, rest)
      +b = Ds.mem(a, seen)
      pv.and_tt(b, Ds.subset(rest, seen), pv.put_nil_seen(a, u, b, h), pv.nil_subset(seen, rest, pv.put_nil_rest(a, u, b, h)))

def pv.edit_only_seen_lines(+seen: List<&2, Nat>, +anchors: List<&2, Nat>, ok: {Ds.Step.applied(Ds.edit(seen, anchors)) == True{} : Bool}) -> {Ds.subset(anchors, seen) == True{} : Bool}:
  pv.nil_subset(seen, anchors, pv.applied_nil(seen, Ds.unseen(seen, anchors), ok))

# Seen anchors: the edit applies
# ------------------------------

def pv.subset_nil(+seen: List<&2, Nat>, anchors: List<&2, Nat>, +h: {Ds.subset(anchors, seen) == True{} : Bool}) -> {Ds.unseen(seen, anchors) == Nil{} : List<&2, Nat>}:
  match anchors:
    case Nil{}:
      {==}
    case +a <> +rest:
      +hm = pv.and_l(Ds.mem(a, seen), Ds.subset(rest, seen), h)
      +hr = pv.and_r(Ds.mem(a, seen), Ds.subset(rest, seen), h)
      %Equal.sym(Bool, Ds.mem(a, seen), True{}, hm) : {Ds.unseen.put(a, Ds.unseen(seen, rest), _) == Nil{} : List<&2, Nat>}
      pv.subset_nil(seen, rest, hr)

def pv.edit_seen_applies(+seen: List<&2, Nat>, +anchors: List<&2, Nat>, all: {Ds.subset(anchors, seen) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(seen, anchors)) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Ds.unseen(seen, anchors), Nil{}, pv.subset_nil(seen, anchors, all)) : {Ds.Step.applied(Ds.edit.go(seen, _)) == True{} : Bool}
  {==}

# A rejection, then a retry
# -------------------------

# every anchor is seen or unseen
def pv.cover.go(+seen: List<&2, Nat>, +a: Nat, +rest: List<&2, Nat>, b: Bool, e: {Ds.mem(a, seen) == b : Bool}, ih: {Ds.subset(rest, List.append(&2, Nat, Ds.unseen(seen, rest), seen)) == True{} : Bool}) -> {Ds.subset(a <> rest, List.append(&2, Nat, Ds.unseen.put(a, Ds.unseen(seen, rest), b), seen)) == True{} : Bool}:
  match b:
    case True{}:
      +u = Ds.unseen(seen, rest)
      pv.and_tt(Ds.mem(a, List.append(&2, Nat, u, seen)), Ds.subset(rest, List.append(&2, Nat, u, seen)), pv.mem_app(a, u, seen, e), ih)
    case False{}:
      +y = List.append(&2, Nat, Ds.unseen(seen, rest), seen)
      pv.and_tt(Ds.mem(a, a <> y), Ds.subset(rest, a <> y), pv.mem_head(a, y), pv.sub_cons(rest, a, y, ih))

def pv.cover(+seen: List<&2, Nat>, anchors: List<&2, Nat>) -> {Ds.subset(anchors, List.append(&2, Nat, Ds.unseen(seen, anchors), seen)) == True{} : Bool}:
  match anchors:
    case Nil{}:
      {==}
    case +a <> +rest:
      pv.cover.go(seen, a, rest, Ds.mem(a, seen), {==}, pv.cover(seen, rest))

def pv.short.go(+a: Nat, u: List<&2, Nat>, +k: Nat, b: Bool, ih: {Nat.is_le(List.length(&2, Nat, u), k) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, Ds.unseen.put(a, u, b)), 1n+k) == True{} : Bool}:
  match b:
    case True{}:
      pv.le_succ(List.length(&2, Nat, u), k, ih)
    case False{}:
      ih

# a rejection has no more unseen anchors than anchors
def pv.short(+seen: List<&2, Nat>, anchors: List<&2, Nat>, n: Nat, h: {Nat.is_le(List.length(&2, Nat, anchors), n) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, Ds.unseen(seen, anchors)), n) == True{} : Bool}:
  match anchors n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      {==}
    case +a <> rest 0n:
      pv.absurd({Nat.is_le(List.length(&2, Nat, Ds.unseen(seen, a <> rest)), 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case +a <> +rest 1n+(+k):
      pv.short.go(a, Ds.unseen(seen, rest), k, Ds.mem(a, seen), pv.short(seen, rest, k, h))

def pv.retry.go(+seen: List<&2, Nat>, +anchors: List<&2, Nat>, u: List<&2, Nat>, eu: {Ds.unseen(seen, anchors) == u : List<&2, Nat>}, few: {Nat.is_le(List.length(&2, Nat, u), Ds.cap) == True{} : Bool}, cover: {Ds.subset(anchors, List.append(&2, Nat, u, seen)) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit.go(seen, u)), anchors)) == True{} : Bool}:
  match u:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, Ds.unseen(seen, anchors), Nil{}, eu) : {Ds.Step.applied(Ds.edit.go(seen, _)) == True{} : Bool}
      {==}
    case +x <> +rest:
      %Equal.sym(Bool, Nat.is_le(List.length(&2, Nat, x <> rest), Ds.cap), True{}, few) : {Ds.Step.applied(Ds.edit(Ds.reveal(x <> rest, seen, _), anchors)) == True{} : Bool}
      pv.edit_seen_applies(List.append(&2, Nat, x <> rest, seen), anchors, cover)

def pv.reveal_then_retry(+seen: List<&2, Nat>, +anchors: List<&2, Nat>, few: {Nat.is_le(List.length(&2, Nat, anchors), Ds.cap) == True{} : Bool}) -> {Ds.Step.applied(Ds.edit(Ds.Step.seen(Ds.edit(seen, anchors)), anchors)) == True{} : Bool}:
  pv.retry.go(seen, anchors, Ds.unseen(seen, anchors), {==}, pv.short(seen, anchors, Ds.cap, few), pv.cover(seen, anchors))

# ==== search ====
# proof_doc_search: the grep and continuation laws of laws/documents.bend
# (F6, F7): grep puts every walked entry in exactly one class, has a
# notice of each class it left out exactly when that class is not empty,
# and a notice for each shown file it cut; a continuation gives a page
# that is not empty, follows on from the page before it with nothing left
# out and nothing twice, and has no item in common with it.
# Logic and numbers
# -----------------

def ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ps.BD(_, Unit, A)
  Unit{}

def ps.MD(m: Maybe<&2, Nat>, t: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      t

def ps.none_some(-A: Type, -c: Nat, e: {None{} == Some{c} : Maybe<&2, Nat>}) -> A:
  %e : ps.MD(_, A)
  Unit{}

def ps.some_inj(-a: Nat, -b: Nat, e: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{a}, Some{b}, e)

def ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ps.absurd({0n == 1n+q : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 0n:
      ps.absurd({1n+p == 0n : Nat}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      %ps.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def ps.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ps.eq_refl(p)

def ps.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ps.absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def ps.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ps.absurd({False{} == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def ps.not_t(a: Bool, h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      ps.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      {==}

def ps.or_fr(a: Bool, -b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      ps.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(Bool.or(a, b), c) == Bool.or(a, Bool.or(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.add_sr(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ps.add_sr(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# Pages
# -----

def ps.take_drop(xs: List<&2, Nat>, k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, xs, k), List.drop(&2, Nat, xs, k)) == xs : List<&2, Nat>}:
  match xs k:
    case Nil{} k:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+p:
      %ps.take_drop(t, p) : {h <> List.append(&2, Nat, List.take(&2, Nat, t, p), List.drop(&2, Nat, t, p)) == h <> _ : List<&2, Nat>}
      {==}

def ps.drop_drop(xs: List<&2, Nat>, s: Nat, +k: Nat) -> {List.drop(&2, Nat, List.drop(&2, Nat, xs, s), k) == List.drop(&2, Nat, xs, Nat.add(s, k)) : List<&2, Nat>}:
  match xs s:
    case Nil{} s:
      match k:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      ps.drop_drop(t, p, k)

def ps.put_c(after: List<&2, Nat>, -c0: Nat, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {c0 == c : Nat}:
  match after:
    case Nil{}:
      ps.none_some({c0 == c : Nat}, c, h)
    case x <> t:
      ps.some_inj(c0, c, h)

# the continuation is S + K
def ps.next_c(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {Nat.add(s, k) == c : Nat}:
  match k:
    case 0n:
      ps.none_some({Nat.add(s, 0n) == c : Nat}, c, h)
    case 1n+j:
      ps.put_c(List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), Nat.add(s, 1n+j), c, h)

# the page of a continuation is not empty
def ps.prog_go(+ps: List<&2, Nat>, -c0: Nat, +j: Nat, after: List<&2, Nat>, e: {List.drop(&2, Nat, ps, c0) == after : List<&2, Nat>}, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {List.is_empty(&2, Nat, Sr.page(ps, c, 1n+j)) == False{} : Bool}:
  match after:
    case Nil{}:
      ps.none_some({List.is_empty(&2, Nat, Sr.page(ps, c, 1n+j)) == False{} : Bool}, c, h)
    case x <> t:
      %ps.some_inj(c0, c, h) : {List.is_empty(&2, Nat, Sr.page(ps, _, 1n+j)) == False{} : Bool}
      %Equal.sym(List<&2, Nat>, List.drop(&2, Nat, ps, c0), x <> t, e) : {List.is_empty(&2, Nat, List.take(&2, Nat, _, 1n+j)) == False{} : Bool}
      {==}

# the law continuation_progresses
def ps.progresses(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {List.is_empty(&2, Nat, Sr.page(ps, c, k)) == False{} : Bool}:
  match k:
    case 0n:
      ps.none_some({List.is_empty(&2, Nat, Sr.page(ps, c, 0n)) == False{} : Bool}, c, h)
    case 1n+j:
      ps.prog_go(ps, Nat.add(s, 1n+j), j, List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), {==}, c, h)

# the page at S + K and what follows it are the list after S
def ps.contig(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, Nat.add(s, k), k), List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  +d = List.drop(&2, Nat, ps, Nat.add(s, k))
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, d, k), List.drop(&2, Nat, d, k)), d, ps.take_drop(d, k)) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  %ps.drop_drop(ps, s, k) : {List.append(&2, Nat, Sr.page(ps, s, k), _) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  ps.take_drop(List.drop(&2, Nat, ps, s), k)

def ps.contig_at(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, e: {Nat.add(s, k) == c : Nat}) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), List.drop(&2, Nat, List.drop(&2, Nat, ps, c), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  %e : {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, _, k), List.drop(&2, Nat, List.drop(&2, Nat, ps, _), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  ps.contig(ps, s, k)

# the law continuation_contiguous
def ps.contiguous(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> &rest: List<&2, Nat> -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), rest)) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  (List.drop(&2, Nat, List.drop(&2, Nat, ps, c), k), ps.contig_at(ps, s, k, c, ps.next_c(ps, s, k, c, h)))

def ps.or_mono(a: Bool, -x: Bool, -y: Bool, h: {Bool.or(a, x) == True{} : Bool}, f: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def ps.mem_app(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Bool.or(Sr.mem(n, a), Sr.mem(n, b)) == Sr.mem(n, List.append(&2, Nat, a, b)) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ps.mem_app(n, rest, b) : {Bool.or(Bool.or(Nat.is_eq(x, n), Sr.mem(n, rest)), Sr.mem(n, b)) == Bool.or(Nat.is_eq(x, n), _) : Bool}
      ps.or_assoc(Nat.is_eq(x, n), Sr.mem(n, rest), Sr.mem(n, b))

def ps.mem_app_l(+n: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, h: {Sr.mem(n, a) == True{} : Bool}) -> {Sr.mem(n, List.append(&2, Nat, a, b)) == True{} : Bool}:
  match a:
    case Nil{}:
      ps.absurd({Sr.mem(n, b) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case +x <> +rest:
      ps.or_mono(Nat.is_eq(x, n), Sr.mem(n, rest), Sr.mem(n, List.append(&2, Nat, rest, b)), h, hh => ps.mem_app_l(n, rest, b, hh))

def ps.nodup_drop(xs: List<&2, Nat>, s: Nat, nd: {Sr.nodup(xs) == True{} : Bool}) -> {Sr.nodup(List.drop(&2, Nat, xs, s)) == True{} : Bool}:
  match xs s:
    case Nil{} s:
      {==}
    case h <> t 0n:
      nd
    case +h <> +t 1n+p:
      ps.nodup_drop(t, p, ps.and_r(Bool.not(Sr.mem(h, t)), Sr.nodup(t), nd))

def ps.nd_hit(-y: Nat, +x: Nat, e: {y == x : Nat}, +t: List<&2, Nat>, +b: List<&2, Nat>, ny: {Sr.mem(y, List.append(&2, Nat, t, b)) == False{} : Bool}) -> {Bool.or(Sr.mem(x, t), Sr.mem(x, b)) == False{} : Bool}:
  %Equal.sym(Bool, Bool.or(Sr.mem(x, t), Sr.mem(x, b)), Sr.mem(x, List.append(&2, Nat, t, b)), ps.mem_app(x, t, b)) : {_ == False{} : Bool}
  %e : {Sr.mem(_, List.append(&2, Nat, t, b)) == False{} : Bool}
  ny

def ps.nd_step(+y: Nat, +x: Nat, q: Bool, eq: {Nat.is_eq(y, x) == q : Bool}, +t: List<&2, Nat>, +b: List<&2, Nat>, ny: {Sr.mem(y, List.append(&2, Nat, t, b)) == False{} : Bool}, ih: {Bool.and(Sr.mem(x, t), Sr.mem(x, b)) == False{} : Bool}) -> {Bool.and(Bool.or(q, Sr.mem(x, t)), Sr.mem(x, b)) == False{} : Bool}:
  match q:
    case True{}:
      ps.or_fr(Sr.mem(x, t), Sr.mem(x, b), ps.nd_hit(y, x, ps.eq_true(y, x, eq), t, b, ny))
    case False{}:
      ih

def ps.nd_app(a: List<&2, Nat>, +b: List<&2, Nat>, +x: Nat, +nd: {Sr.nodup(List.append(&2, Nat, a, b)) == True{} : Bool}) -> {Bool.and(Sr.mem(x, a), Sr.mem(x, b)) == False{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case +y <> +t:
      +ab = List.append(&2, Nat, t, b)
      +ny = ps.not_t(Sr.mem(y, ab), ps.and_l(Bool.not(Sr.mem(y, ab)), Sr.nodup(ab), nd))
      ps.nd_step(y, x, Nat.is_eq(y, x), {==}, t, b, ny, ps.nd_app(t, b, x, ps.and_r(Bool.not(Sr.mem(y, ab)), Sr.nodup(ab), nd)))

def ps.and_imp(a: Bool, b: Bool, -c: Bool, h: {Bool.and(a, c) == False{} : Bool}, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      ps.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, c, False{}, Equal.sym(Bool, c, True{}, f({==})), h))

def ps.disj_at(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +x: Nat, nd: {Sr.nodup(ps) == True{} : Bool}) -> {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, Nat.add(s, k), k))) == False{} : Bool}:
  +p1 = Sr.page(ps, s, k)
  +p2 = Sr.page(ps, Nat.add(s, k), k)
  +r = List.drop(&2, Nat, List.drop(&2, Nat, ps, Nat.add(s, k)), k)
  +all = List.append(&2, Nat, p1, List.append(&2, Nat, p2, r))
  +whole = Equal.trans(Bool, Sr.nodup(all), Sr.nodup(List.drop(&2, Nat, ps, s)), True{}, Equal.cong(List<&2, Nat>, Bool, l => Sr.nodup(l), all, List.drop(&2, Nat, ps, s), ps.contig(ps, s, k)), ps.nodup_drop(ps, s, nd))
  ps.and_imp(Sr.mem(x, p1), Sr.mem(x, p2), Sr.mem(x, List.append(&2, Nat, p2, r)), ps.nd_app(p1, List.append(&2, Nat, p2, r), x, whole), hh => ps.mem_app_l(x, p2, r, hh))

# the law continuation_disjoint
def ps.disjoint(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, +x: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}, nd: {Sr.nodup(ps) == True{} : Bool}) -> {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, c, k))) == False{} : Bool}:
  %ps.next_c(ps, s, k, c, h) : {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, _, k))) == False{} : Bool}
  ps.disj_at(ps, s, k, x, nd)

# Grep: every entry in one class
# ------------------------------

def ps.sum_mid(pre: List<&2, Nat>, +x: Nat, +post: List<&2, Nat>) -> {Sr.sum(List.append(&2, Nat, pre, (1n+x) <> post)) == 1n+Sr.sum(List.append(&2, Nat, pre, x <> post)) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case +y <> +t:
      +a = Sr.sum(List.append(&2, Nat, t, (1n+x) <> post))
      +b = Sr.sum(List.append(&2, Nat, t, x <> post))
      Equal.trans(Nat, Nat.add(y, a), Nat.add(y, 1n+b), 1n+Nat.add(y, b), Equal.cong(Nat, Nat, z => Nat.add(y, z), a, 1n+b, ps.sum_mid(t, x, post)), ps.add_sr(y, b))

def ps.total_part(pa: Bool, c: Sr.Count) -> {Sr.Count.total(Sr.Count.part(pa, c)) == Sr.Count.total(c) : Nat}:
  match pa:
    case True{}:
      match c:
        case Sr.Count{a, b, d, e, f, g, h, i, j, q}:
          {==}
    case False{}:
      {==}

# one more entry in a class is one more in all
def ps.total_add(c: Sr.Count, x: Sr.Class) -> {Sr.Count.total(Sr.Count.add(c, x)) == 1n+Sr.Count.total(c) : Nat}:
  match c:
    case Sr.Count{+a, +b, +d, +e, +f, +g, +h, +i, +j, q}:
      match x:
        case Sr.NoMatch{}:
          ps.sum_mid([], a, [b, d, e, f, g, h, i, j])
        case Sr.Shown{}:
          ps.sum_mid([a], b, [d, e, f, g, h, i, j])
        case Sr.PagedOut{}:
          ps.sum_mid([a, b], d, [e, f, g, h, i, j])
        case Sr.Unsearched{}:
          ps.sum_mid([a, b, d], e, [f, g, h, i, j])
        case Sr.Skipped{w}:
          match w:
            case Sr.Binary{}:
              ps.sum_mid([a, b, d, e], f, [g, h, i, j])
            case Sr.Unreadable{}:
              ps.sum_mid([a, b, d, e, f], g, [h, i, j])
            case Sr.Excluded{}:
              ps.sum_mid([a, b, d, e, f, g], h, [i, j])
            case Sr.Link{}:
              ps.sum_mid([a, b, d, e, f, g, h], i, [j])
            case Sr.Broken{}:
              ps.sum_mid([a, b, d, e, f, g, h, i], j, [])

def ps.total_account(os: List<&2, Sr.Out>) -> {Sr.Count.total(Sr.account(os)) == List.length(&2, Sr.Out, os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{i, +c, t, +pa}:
          +acc = Sr.account(rest)
          +grown = Sr.Count.add(acc, c)
          Equal.trans(Nat, Sr.Count.total(Sr.Count.part(pa, grown)), Sr.Count.total(grown), 1n+List.length(&2, Sr.Out, rest), ps.total_part(pa, grown), Equal.trans(Nat, Sr.Count.total(grown), 1n+Sr.Count.total(acc), 1n+List.length(&2, Sr.Out, rest), ps.total_add(acc, c), Equal.cong(Nat, Nat, z => 1n+z, Sr.Count.total(acc), List.length(&2, Sr.Out, rest), ps.total_account(rest))))

def ps.len_run(es: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> {List.length(&2, Sr.Out, Sr.run(es, p, s, k, rem, n)) == List.length(&2, Sr.Ent, es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      %ps.len_run(rest, p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n)) : {1n+List.length(&2, Sr.Out, Sr.run(rest, p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n))) == 1n+_ : Nat}
      {==}

# the law grep_accounts_every_file
def ps.accounts_every_file(+es: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> {Sr.Count.total(Sr.account(Sr.run(es, p, s, k, rem, n))) == List.length(&2, Sr.Ent, es) : Nat}:
  +os = Sr.run(es, p, s, k, rem, n)
  Equal.trans(Nat, Sr.Count.total(Sr.account(os)), List.length(&2, Sr.Out, os), List.length(&2, Sr.Ent, es), ps.total_account(os), ps.len_run(es, p, s, k, rem, n))

# Grep: a notice for each class left out
# --------------------------------------

def ps.bump(b: Bool, x: Nat) -> Nat:
  match b:
    case True{}:
      1n+x
    case False{}:
      x

# the count of a notice after one more entry: one more when the notice
# reports the entry
def ps.count_step(c: Sr.Count, pa: Bool, x: Sr.Class, n: Sr.Note) -> {Sr.Note.count(Sr.Count.part(pa, Sr.Count.add(c, x)), n) == ps.bump(Sr.Note.cls(n, x, pa), Sr.Note.count(c, n)) : Nat}:
  match c:
    case Sr.Count{a, b, d, e, f, g, h, i, j, q}:
      match pa:
        case True{}:
          match x:
            case Sr.NoMatch{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Shown{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.PagedOut{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Unsearched{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Skipped{v}:
              match v:
                case Sr.Binary{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Unreadable{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Excluded{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Link{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Broken{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
        case False{}:
          match x:
            case Sr.NoMatch{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Shown{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.PagedOut{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Unsearched{}:
              match n:
                case Sr.NSkip{w}:
                  match w:
                    case Sr.Binary{}:
                      {==}
                    case Sr.Unreadable{}:
                      {==}
                    case Sr.Excluded{}:
                      {==}
                    case Sr.Link{}:
                      {==}
                    case Sr.Broken{}:
                      {==}
                case Sr.NPartial{}:
                  {==}
                case Sr.NUnsearched{}:
                  {==}
            case Sr.Skipped{v}:
              match v:
                case Sr.Binary{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Unreadable{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Excluded{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Link{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}
                case Sr.Broken{}:
                  match n:
                    case Sr.NSkip{w}:
                      match w:
                        case Sr.Binary{}:
                          {==}
                        case Sr.Unreadable{}:
                          {==}
                        case Sr.Excluded{}:
                          {==}
                        case Sr.Link{}:
                          {==}
                        case Sr.Broken{}:
                          {==}
                    case Sr.NPartial{}:
                      {==}
                    case Sr.NUnsearched{}:
                      {==}

def ps.count_zero(n: Sr.Note) -> {Sr.Note.count(Sr.Count.zero(), n) == 0n : Nat}:
  match n:
    case Sr.NSkip{w}:
      match w:
        case Sr.Binary{}:
          {==}
        case Sr.Unreadable{}:
          {==}
        case Sr.Excluded{}:
          {==}
        case Sr.Link{}:
          {==}
        case Sr.Broken{}:
          {==}
    case Sr.NPartial{}:
      {==}
    case Sr.NUnsearched{}:
      {==}

def ps.or_bump(b: Bool, +x: Nat) -> {Bool.or(b, Bool.not(Nat.is_eq(x, 0n))) == Bool.not(Nat.is_eq(ps.bump(b, x), 0n)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the law grep_notes_every_gap
def ps.notes_every_gap(os: List<&2, Sr.Out>, +n: Sr.Note) -> {Sr.noted(n, os) == Bool.not(Nat.is_eq(Sr.Note.count(Sr.account(os), n), 0n)) : Bool}:
  match os:
    case Nil{}:
      %Equal.sym(Nat, Sr.Note.count(Sr.Count.zero(), n), 0n, ps.count_zero(n)) : {False{} == Bool.not(Nat.is_eq(_, 0n)) : Bool}
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{i, +c, t, +pa}:
          +acc = Sr.account(rest)
          +b = Sr.Note.cls(n, c, pa)
          +x = Sr.Note.count(acc, n)
          +after = Sr.Note.count(Sr.Count.part(pa, Sr.Count.add(acc, c)), n)
          +ih = Equal.cong(Bool, Bool, y => Bool.or(b, y), Sr.noted(n, rest), Bool.not(Nat.is_eq(x, 0n)), ps.notes_every_gap(rest, n))
          +last = Equal.cong(Nat, Bool, y => Bool.not(Nat.is_eq(y, 0n)), ps.bump(b, x), after, Equal.sym(Nat, after, ps.bump(b, x), ps.count_step(acc, pa, c, n)))
          Equal.trans(Bool, Bool.or(b, Sr.noted(n, rest)), Bool.or(b, Bool.not(Nat.is_eq(x, 0n))), Bool.not(Nat.is_eq(after, 0n)), ih, Equal.trans(Bool, Bool.or(b, Bool.not(Nat.is_eq(x, 0n))), Bool.not(Nat.is_eq(ps.bump(b, x), 0n)), Bool.not(Nat.is_eq(after, 0n)), ps.or_bump(b, x), last))

# Grep: a notice for each cut file shown
# --------------------------------------

def ps.or_r(a: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ps.cut_keep(+i: Nat, +i2: Nat, c: Sr.Class, t: Bool, +l: List<&2, Nat>, h: {Sr.mem(i, l) == True{} : Bool}) -> {Sr.mem(i, Sr.cut.put(i2, c, t, l)) == True{} : Bool}:
  match c:
    case Sr.NoMatch{}:
      h
    case Sr.Shown{}:
      match t:
        case True{}:
          ps.or_r(Nat.is_eq(i2, i), Sr.mem(i, l), h)
        case False{}:
          h
    case Sr.PagedOut{}:
      h
    case Sr.Unsearched{}:
      h
    case Sr.Skipped{w}:
      h

# the law grep_notes_every_cut
def ps.notes_every_cut(pre: List<&2, Sr.Out>, +i: Nat, +pa: Bool, +post: List<&2, Sr.Out>) -> {Sr.mem(i, Sr.cuts(List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post))) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(i, i), True{}, ps.eq_refl(i)) : {Bool.or(_, Sr.mem(i, Sr.cuts(post))) == True{} : Bool}
      {==}
    case o <> +rest:
      match o:
        case Sr.Out{+i2, c, t, pa2}:
          ps.cut_keep(i, i2, c, t, Sr.cuts(List.append(&2, Sr.Out, rest, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post)), ps.notes_every_cut(rest, i, pa, post))

# ==== tags ====
# proof_doc_tags: the tag law of laws/documents.bend (F3): the tag of a
# read or grep result names the text its rows come from.
def pdt.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pdt.eq_refl(p)

def pdt.app_assoc(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>) -> {List.append(&2, Nat, List.append(&2, Nat, xs, ys), zs) == List.append(&2, Nat, xs, List.append(&2, Nat, ys, zs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> t:
      %pdt.app_assoc(t, ys, zs) : {h <> List.append(&2, Nat, List.append(&2, Nat, t, ys), zs) == h <> _ : List<&2, Nat>}
      {==}

def pdt.len_snoc(pre: List<&2, Nat>, +x: Nat) -> {List.length(&2, Nat, List.append(&2, Nat, pre, [x])) == 1n+List.length(&2, Nat, pre) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case h <> t:
      %pdt.len_snoc(t, x) : {1n+List.length(&2, Nat, List.append(&2, Nat, t, [x])) == 1n+_ : Nat}
      {==}

# the line after pre is x
def pdt.get_app(pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>) -> {List.get(&2, Nat, List.append(&2, Nat, pre, x <> rest), List.length(&2, Nat, pre)) == Some{x} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      {==}
    case h <> t:
      pdt.get_app(t, x, rest)

def pdt.line_at(+pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>) -> {Dt.is_line(List.append(&2, Nat, pre, x <> rest), 1n+List.length(&2, Nat, pre), x) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, List.append(&2, Nat, pre, x <> rest), List.length(&2, Nat, pre)), Some{x}, pdt.get_app(pre, x, rest)) : {Maybe.default(&2, Bool, Maybe.bind(&2, Nat, Bool, _, y => Some{Nat.is_eq(y, x)}), False{}) == True{} : Bool}
  pdt.eq_refl(x)

# a row of line 1 + |pre| kept or not: the rows stay lines of the text
def pdt.keep_ok(s: Bool, +pre: List<&2, Nat>, +x: Nat, +rest: List<&2, Nat>, +rs: List<&2, Dt.Row>, ih: {Dt.from_text(List.append(&2, Nat, pre, x <> rest), rs) == True{} : Bool}) -> {Dt.from_text(List.append(&2, Nat, pre, x <> rest), Dt.keep(s, Dt.Row{1n+List.length(&2, Nat, pre), x}, rs)) == True{} : Bool}:
  match s:
    case True{}:
      %Equal.sym(Bool, Dt.is_line(List.append(&2, Nat, pre, x <> rest), 1n+List.length(&2, Nat, pre), x), True{}, pdt.line_at(pre, x, rest)) : {Bool.and(_, Dt.from_text(List.append(&2, Nat, pre, x <> rest), rs)) == True{} : Bool}
      ih
    case False{}:
      ih

# the rows after line x, seen from pre ++ [x]
def pdt.shift(+rest: List<&2, Nat>, +more: List<&2, Bool>, +pre: List<&2, Nat>, +x: Nat, ih: {Dt.from_text(List.append(&2, Nat, List.append(&2, Nat, pre, [x]), rest), Dt.rows(rest, more, 1n+List.length(&2, Nat, List.append(&2, Nat, pre, [x])))) == True{} : Bool}) -> {Dt.from_text(List.append(&2, Nat, pre, x <> rest), Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre)))) == True{} : Bool}:
  %pdt.app_assoc(pre, [x], rest) : {Dt.from_text(_, Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre)))) == True{} : Bool}
  %pdt.len_snoc(pre, x) : {Dt.from_text(List.append(&2, Nat, List.append(&2, Nat, pre, [x]), rest), Dt.rows(rest, more, 1n+_)) == True{} : Bool}
  ih

# every row cut from the lines ts after the lines pre is a line of
# pre ++ ts
def pdt.rows_from(ts: List<&2, Nat>, sel: List<&2, Bool>, +pre: List<&2, Nat>) -> {Dt.from_text(List.append(&2, Nat, pre, ts), Dt.rows(ts, sel, 1n+List.length(&2, Nat, pre))) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +x <> +rest:
      match sel:
        case Nil{}:
          {==}
        case s <> +more:
          pdt.keep_ok(s, pre, x, rest, Dt.rows(rest, more, 1n+(1n+List.length(&2, Nat, pre))), pdt.shift(rest, more, pre, x, pdt.rows_from(rest, more, List.append(&2, Nat, pre, [x]))))

# the law tag_names_shown_text
def pdt.tag_names(+t: List<&2, Nat>, op: Dt.Op) -> {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}:
  match op:
    case Dt.Read{sel}:
      ({==}, pdt.rows_from(t, sel, Nil{}))
    case Dt.Grep{sel, later}:
      ({==}, pdt.rows_from(t, sel, Nil{}))
