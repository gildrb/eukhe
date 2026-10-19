# proof_staging: the staging, sweep and listing laws of laws/storage.bend
# (D2): a publish never takes a name that is taken; a sweep never removes
# a held, young or unreached entry, and removes every stale free leftover
# it reaches; a session is listed once, under the storage it opens as.

import Base
import ./staging.bend as Sg

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

def pg.or_t(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.or_f(a: Bool) -> {a == Bool.or(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Publish
# -------

def pg.publish_taken(+s: Nat, +t: Nat, +es: List<&2, Sg.Entry>, taken: {Sg.has(t, es) == True{} : Bool}) -> {Sg.publish(s, t, es) == Sg.Pub{False{}, es} : Sg.Pub}:
  %Equal.sym(Bool, Sg.has(t, es), True{}, taken) : {Sg.publish.go(s, t, _, es) == Sg.Pub{False{}, es} : Sg.Pub}
  {==}

def pg.publish_free(+s: Nat, +t: Nat, +es: List<&2, Sg.Entry>, free: {Sg.has(t, es) == False{} : Bool}) -> {Sg.Pub.ok(Sg.publish(s, t, es)) == True{} : Bool}:
  %Equal.sym(Bool, Sg.has(t, es), False{}, free) : {Sg.Pub.ok(Sg.publish.go(s, t, _, es)) == True{} : Bool}
  {==}

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

def pg.no_held(+i: Nat, +k: Sg.Sort, +s: Bool, o: Bool) -> {False{} == Sg.removes(Sg.Node{i, k, True{}, s, o}) : Bool}:
  match o:
    case True{}:
      {==}
    case False{}:
      {==}

def pg.no_young(+i: Nat, +k: Sg.Sort, h: Bool, o: Bool) -> {False{} == Sg.removes(Sg.Node{i, k, h, False{}, o}) : Bool}:
  match h o:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def pg.sweep_never_live(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +s: Bool, +o: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, True{}, s, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  pg.kept(pre, Sg.Node{i, k, True{}, s, o}, post, pg.no_held(i, k, s, o))

def pg.sweep_never_young(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +h: Bool, +o: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, False{}, o} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  pg.kept(pre, Sg.Node{i, k, h, False{}, o}, post, pg.no_young(i, k, h, o))

def pg.sweep_stays_out(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +h: Bool, +s: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, s, False{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  pg.kept(pre, Sg.Node{i, k, h, s, False{}}, post, {==})

def pg.sweep_reaches(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +post: List<&2, Sg.Node>, sw: {Sg.Sort.swept(k) == True{} : Bool}) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, False{}, True{}, True{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.Node{i, k, False{}, True{}, True{}} <> Sg.sweep(post)) : List<&2, Sg.Node>}:
  +n = {Sg.Node{i, k, False{}, True{}, True{}} : Sg.Node}
  %pg.sweep_app(pre, n <> post) : {_ == List.append(&2, Sg.Node, Sg.sweep(pre), n <> Sg.sweep(post)) : List<&2, Sg.Node>}
  %Equal.sym(Bool, Sg.Sort.swept(k), True{}, sw) : {List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep.put(n, Sg.sweep(post), _)) == List.append(&2, Sg.Node, Sg.sweep(pre), n <> Sg.sweep(post)) : List<&2, Sg.Node>}
  {==}

# Listing
# -------

def pg.or_mono(a: Bool, -x: Bool, -y: Bool, h: {Bool.or(a, x) == True{} : Bool}, f: {x == True{} : Bool} -> {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def pg.or_r(a: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(a, y) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

# a storage listed is a directory of that name
def pg.dur_put(+m: Nat, +n: Nat, -d: List<&2, Nat>, -r: List<&2, Sg.Ent>, q: Bool, h: {Sg.mem(n, Sg.keep.put(m, d, q)) == True{} : Bool}, ih: {Sg.mem(n, d) == True{} : Bool} -> {Sg.dirn(n, r) == True{} : Bool}) -> {Bool.or(Nat.is_eq(m, n), Sg.dirn(n, r)) == True{} : Bool}:
  match q:
    case True{}:
      pg.or_mono(Nat.is_eq(m, n), Sg.mem(n, d), Sg.dirn(n, r), h, ih)
    case False{}:
      pg.or_r(Nat.is_eq(m, n), Sg.dirn(n, r), ih(h))

def pg.dur_dirn(+n: Nat, es: List<&2, Sg.Ent>, h: {Sg.mem(n, Sg.durables(es)) == True{} : Bool}) -> {Sg.dirn(n, es) == True{} : Bool}:
  match es:
    case Nil{}:
      pg.absurd({Sg.dirn(n, Nil{}) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case e <> +rest:
      match e:
        case Sg.Dir{+m, a, hd, c}:
          pg.dur_put(m, n, Sg.durables(rest), rest, Bool.and(a, Bool.and(Bool.not(hd), c)), h, hh => pg.dur_dirn(n, rest, hh))
        case Sg.Legacy{s, r}:
          pg.dur_dirn(n, rest, h)

def pg.and_not(r: Bool, d: Bool, h: {Bool.and(r, Bool.not(d)) == True{} : Bool}) -> {d == False{} : Bool}:
  match r d:
    case True{} True{}:
      pg.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case True{} False{}:
      {==}
    case False{} True{}:
      pg.absurd({True{} == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case False{} False{}:
      {==}

def pg.leg_hit(-all: List<&2, Sg.Ent>, +n: Nat, +s: Nat, -l: List<&2, Nat>, b: Bool, eb: {Nat.is_eq(s, n) == b : Bool}, h: {Bool.or(b, Sg.mem(n, l)) == True{} : Bool}, nd: {Sg.dirn(s, all) == False{} : Bool}, ih: {Sg.mem(n, l) == True{} : Bool} -> {Sg.dirn(n, all) == False{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match b:
    case True{}:
      %pg.eq_true(s, n, eb) : {Sg.dirn(_, all) == False{} : Bool}
      nd
    case False{}:
      ih(h)

def pg.leg_put(+all: List<&2, Sg.Ent>, +n: Nat, +s: Nat, +r: Bool, -l: List<&2, Nat>, q: Bool, eq: {Bool.and(r, Bool.not(Sg.dirn(s, all))) == q : Bool}, h: {Sg.mem(n, Sg.keep.put(s, l, q)) == True{} : Bool}, ih: {Sg.mem(n, l) == True{} : Bool} -> {Sg.dirn(n, all) == False{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match q:
    case True{}:
      pg.leg_hit(all, n, s, l, Nat.is_eq(s, n), {==}, h, pg.and_not(r, Sg.dirn(s, all), eq), ih)
    case False{}:
      ih(h)

# a legacy file listed has no directory of its name
def pg.leg_dirn(+all: List<&2, Sg.Ent>, +n: Nat, es: List<&2, Sg.Ent>, h: {Sg.mem(n, Sg.legacies(all, es)) == True{} : Bool}) -> {Sg.dirn(n, all) == False{} : Bool}:
  match es:
    case Nil{}:
      pg.absurd({Sg.dirn(n, all) == False{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case e <> +rest:
      match e:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_dirn(all, n, rest, h)
        case Sg.Legacy{+s, +r}:
          pg.leg_put(all, n, s, r, Sg.legacies(all, rest), Bool.and(r, Bool.not(Sg.dirn(s, all))), {==}, h, hh => pg.leg_dirn(all, n, rest, hh))

def pg.one_go(+es: List<&2, Sg.Ent>, +n: Nat, b1: Bool, e1: {Sg.mem(n, Sg.durables(es)) == b1 : Bool}, b2: Bool, e2: {Sg.mem(n, Sg.legacies(es, es)) == b2 : Bool}) -> {Bool.and(b1, b2) == False{} : Bool}:
  match b1 b2:
    case True{} True{}:
      pg.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Sg.dirn(n, es), False{}, Equal.sym(Bool, Sg.dirn(n, es), True{}, pg.dur_dirn(n, es, e1)), pg.leg_dirn(es, n, es, e2)))
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the law list_one_location
def pg.one_location(+es: List<&2, Sg.Ent>, +n: Nat) -> {Bool.and(Sg.mem(n, Sg.durables(es)), Sg.mem(n, Sg.legacies(es, es))) == False{} : Bool}:
  pg.one_go(es, n, Sg.mem(n, Sg.durables(es)), {==}, Sg.mem(n, Sg.legacies(es, es)), {==})

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

# the law list_import_lists_storage
def pg.import_lists(+es: List<&2, Sg.Ent>, +s: Nat) -> {Sg.mem(s, Sg.durables(Sg.imported(s, es))) == True{} : Bool}:
  +d = {[Sg.Dir{s, True{}, False{}, True{}}] : List<&2, Sg.Ent>}
  %pg.dur_app(es, d) : {Sg.mem(s, _) == True{} : Bool}
  %pg.mem_app(s, Sg.durables(es), [s]) : {_ == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, s), True{}, pg.eq_refl(s)) : {Bool.or(Sg.mem(s, Sg.durables(es)), Bool.or(_, False{})) == True{} : Bool}
  pg.or_t(Sg.mem(s, Sg.durables(es)))

def pg.dirn_app(+n: Nat, es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {Bool.or(Sg.dirn(n, es), Sg.dirn(n, x)) == Sg.dirn(n, List.append(&2, Sg.Ent, es, x)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{+m, a, hd, c}:
          %pg.dirn_app(n, rest, x) : {Bool.or(Bool.or(Nat.is_eq(m, n), Sg.dirn(n, rest)), Sg.dirn(n, x)) == Bool.or(Nat.is_eq(m, n), _) : Bool}
          pg.or_assoc(Nat.is_eq(m, n), Sg.dirn(n, rest), Sg.dirn(n, x))
        case Sg.Legacy{st, r}:
          pg.dirn_app(n, rest, x)

# with the directory s added, dirn is the same for a name that is not s
def pg.dirn_other(+n: Nat, +all: List<&2, Sg.Ent>, +s: Nat, ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.dirn(n, all) == Sg.dirn(n, Sg.imported(s, all)) : Bool}:
  %pg.dirn_app(n, all, [Sg.Dir{s, True{}, False{}, True{}}]) : {Sg.dirn(n, all) == _ : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, n), False{}, ne) : {Sg.dirn(n, all) == Bool.or(Sg.dirn(n, all), Bool.or(_, False{})) : Bool}
  pg.or_f(Sg.dirn(n, all))

def pg.mem_miss(+st: Nat, +n: Nat, +l: List<&2, Nat>, q: Bool, ec: {Nat.is_eq(st, n) == False{} : Bool}) -> {Sg.mem(n, l) == Sg.mem(n, Sg.keep.put(st, l, q)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(st, n), False{}, ec) : {Sg.mem(n, l) == Bool.or(_, Sg.mem(n, l)) : Bool}
      {==}
    case False{}:
      {==}

def pg.mem_same(+n: Nat, +l1: List<&2, Nat>, +l2: List<&2, Nat>, q: Bool, ih: {Sg.mem(n, l1) == Sg.mem(n, l2) : Bool}) -> {Sg.mem(n, Sg.keep.put(n, l1, q)) == Sg.mem(n, Sg.keep.put(n, l2, q)) : Bool}:
  match q:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(n, n), True{}, pg.eq_refl(n)) : {Bool.or(_, Sg.mem(n, l1)) == Bool.or(_, Sg.mem(n, l2)) : Bool}
      {==}
    case False{}:
      ih

def pg.leg_step(c: Bool, +st: Nat, +r: Bool, +n: Nat, +all: List<&2, Sg.Ent>, +s: Nat, +l1: List<&2, Nat>, +l2: List<&2, Nat>, +ec: {Nat.is_eq(st, n) == c : Bool}, ne: {Nat.is_eq(s, n) == False{} : Bool}, ih: {Sg.mem(n, l1) == Sg.mem(n, l2) : Bool}) -> {Sg.mem(n, Sg.keep.put(st, l1, Bool.and(r, Bool.not(Sg.dirn(st, Sg.imported(s, all)))))) == Sg.mem(n, Sg.keep.put(st, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, st, n, pg.eq_true(st, n, ec)) : {Sg.mem(n, Sg.keep.put(_, l1, Bool.and(r, Bool.not(Sg.dirn(_, Sg.imported(s, all)))))) == Sg.mem(n, Sg.keep.put(_, l2, Bool.and(r, Bool.not(Sg.dirn(_, all))))) : Bool}
      %pg.dirn_other(n, all, s, ne) : {Sg.mem(n, Sg.keep.put(n, l1, Bool.and(r, Bool.not(_)))) == Sg.mem(n, Sg.keep.put(n, l2, Bool.and(r, Bool.not(Sg.dirn(n, all))))) : Bool}
      pg.mem_same(n, l1, l2, Bool.and(r, Bool.not(Sg.dirn(n, all))), ih)
    case False{}:
      %pg.mem_miss(st, n, l1, Bool.and(r, Bool.not(Sg.dirn(st, Sg.imported(s, all)))), ec) : {_ == Sg.mem(n, Sg.keep.put(st, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))))) : Bool}
      %pg.mem_miss(st, n, l2, Bool.and(r, Bool.not(Sg.dirn(st, all))), ec) : {Sg.mem(n, l1) == _ : Bool}
      ih

# the legacy files listed with the directory s added, for a name not s
def pg.leg_other(+all: List<&2, Sg.Ent>, +s: Nat, +n: Nat, ys: List<&2, Sg.Ent>, +ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.mem(n, Sg.legacies(Sg.imported(s, all), ys)) == Sg.mem(n, Sg.legacies(all, ys)) : Bool}:
  match ys:
    case Nil{}:
      {==}
    case y <> +rest:
      match y:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_other(all, s, n, rest, ne)
        case Sg.Legacy{+st, +r}:
          pg.leg_step(Nat.is_eq(st, n), st, r, n, all, s, Sg.legacies(Sg.imported(s, all), rest), Sg.legacies(all, rest), {==}, ne, pg.leg_other(all, s, n, rest, ne))

def pg.leg_tail(+all: List<&2, Sg.Ent>, es: List<&2, Sg.Ent>, +x: List<&2, Sg.Ent>) -> {List.append(&2, Nat, Sg.legacies(all, es), Sg.legacies(all, x)) == Sg.legacies(all, List.append(&2, Sg.Ent, es, x)) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Sg.Dir{m, a, hd, c}:
          pg.leg_tail(all, rest, x)
        case Sg.Legacy{+st, +r}:
          +q = Bool.and(r, Bool.not(Sg.dirn(st, all)))
          %pg.kput_app(st, Sg.legacies(all, rest), Sg.legacies(all, x), q) : {_ == Sg.keep.put(st, Sg.legacies(all, List.append(&2, Sg.Ent, rest, x)), q) : List<&2, Nat>}
          %pg.leg_tail(all, rest, x) : {Sg.keep.put(st, List.append(&2, Nat, Sg.legacies(all, rest), Sg.legacies(all, x)), q) == Sg.keep.put(st, _, q) : List<&2, Nat>}
          {==}

# the law list_import_keeps_others
def pg.app_nil(xs: List<&2, Nat>) -> {xs == List.append(&2, Nat, xs, Nil{}) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> rest:
      %pg.app_nil(rest) : {x <> rest == x <> _ : List<&2, Nat>}
      {==}

def pg.import_keeps(+es: List<&2, Sg.Ent>, +s: Nat, +n: Nat, +ne: {Nat.is_eq(s, n) == False{} : Bool}) -> {Sg.mem(n, Sg.listing(Sg.imported(s, es))) == Sg.mem(n, Sg.listing(es)) : Bool}:
  +d = {[Sg.Dir{s, True{}, False{}, True{}}] : List<&2, Sg.Ent>}
  +all = Sg.imported(s, es)
  +ds = List.append(&2, Nat, Sg.durables(es), [s])
  %pg.dur_app(es, d) : {Sg.mem(n, List.append(&2, Nat, _, Sg.legacies(all, all))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.leg_tail(all, es, d) : {Sg.mem(n, List.append(&2, Nat, ds, _)) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.mem_app(n, ds, List.append(&2, Nat, Sg.legacies(all, es), Nil{})) : {_ == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.app_nil(Sg.legacies(all, es)) : {Bool.or(Sg.mem(n, ds), Sg.mem(n, _)) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.mem_app(n, Sg.durables(es), [s]) : {Bool.or(_, Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %Equal.sym(Bool, Nat.is_eq(s, n), False{}, ne) : {Bool.or(Bool.or(Sg.mem(n, Sg.durables(es)), Bool.or(_, False{})), Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %pg.or_f(Sg.mem(n, Sg.durables(es))) : {Bool.or(_, Sg.mem(n, Sg.legacies(all, es))) == Sg.mem(n, Sg.listing(es)) : Bool}
  %Equal.sym(Bool, Sg.mem(n, Sg.legacies(all, es)), Sg.mem(n, Sg.legacies(es, es)), pg.leg_other(es, s, n, es, ne)) : {Bool.or(Sg.mem(n, Sg.durables(es)), _) == Sg.mem(n, Sg.listing(es)) : Bool}
  pg.mem_app(n, Sg.durables(es), Sg.legacies(es, es))

