# proof_config: lemmas for laws/config.bend over bend/config.bend (and
# bend/default_model.bend, proved in bend/proof_default_model.bend).
#
# Writes. A broken read writes nothing by definition. A set puts the new
# entry first and drops the old entries of its key; a delete drops them.
# Neither changes the first entry of another key (`pcf.del_keeps`, an
# induction on the document).
#
# Leaves. Each leaf adds its path to the applied list when it is good,
# and to the reported list when it is not; the proofs follow the skill
# loading proofs of bend/proof_progress_report.bend, whose logic lemmas
# they reuse.
#
# Trust and entries. An untrusted project adds only its preferences; a
# key no preference names is looked up past them in the global document
# (an induction on the items). A merged map puts the project entries
# first, so a name the project has is found there, and another name is
# found in the global map (an induction on the project entries).
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

import Base
import ./config.bend as Cf
import ./proof_progress_report.bend as Ppr
import ./default_model.bend as Dm
import ./proof_default_model.bend as Pdm

# Writes
# ------

# a false pick is the later value
def pcf.pick_false(b: Bool, v: Nat, +later: Maybe<&2, Nat>, h: {b == False{} : Bool}) -> {Cf.pick(b, v, later) == later : Maybe<&2, Nat>}:
  match b:
    case True{}:
      Ppr.ppr.absurd({Cf.pick(True{}, v, later) == later : Maybe<&2, Nat>}, h)
    case False{}:
      {==}

# one entry of key i before rest, b saying whether i is k
def pcf.del_step(b: Bool, +i: Nat, v: Nat, +rest: List<&2, Cf.Entry>, +k: Nat, +j: Nat, eb: {Nat.is_eq(i, k) == b : Bool}, h: {Nat.is_eq(k, j) == False{} : Bool}, ih: {Cf.lookup(Cf.del(rest, k), j) == Cf.lookup(rest, j) : Maybe<&2, Nat>}) -> {Cf.lookup(Cf.keep(b, Cf.Entry{i, v}, Cf.del(rest, k)), j) == Cf.pick(Nat.is_eq(i, j), v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Nat, i, k, Ppr.ppr.nat_eq_true(i, k, eb)) : {Cf.lookup(Cf.del(rest, k), j) == Cf.pick(Nat.is_eq(_, j), v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_eq(k, j), False{}, h) : {Cf.lookup(Cf.del(rest, k), j) == Cf.pick(_, v, Cf.lookup(rest, j)) : Maybe<&2, Nat>}
      ih
    case False{}:
      %ih : {Cf.pick(Nat.is_eq(i, j), v, Cf.lookup(Cf.del(rest, k), j)) == Cf.pick(Nat.is_eq(i, j), v, _) : Maybe<&2, Nat>}
      {==}

# a delete of key k keeps the first entry of every other key j
def pcf.del_keeps(d: List<&2, Cf.Entry>, +k: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(Cf.del(d, k), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Entry{+i, v}:
          pcf.del_step(Nat.is_eq(i, k), i, v, rest, k, j, {==}, h, pcf.del_keeps(rest, k, j, h))

# LAW rmw_refuses_broken
def pcf.rmw_refuses_broken(e: Cf.Edit) -> {Cf.rmw(Cf.Broken{}, e) == Cf.Refused{} : Cf.Write}:
  {==}

# LAW rmw_keeps_others: an edit of key k keeps every other key j
def pcf.rmw_keeps_others(+d: List<&2, Cf.Entry>, +e: Cf.Edit, +j: Nat, +h: {Cf.touches(e, j) == False{} : Bool}) -> {Cf.kept(Cf.rmw(Cf.Parsed{d}, e), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match e:
    case Cf.Set{+k, v}:
      %Equal.sym(Maybe<&2, Nat>, Cf.pick(Nat.is_eq(k, j), v, Cf.lookup(Cf.del(d, k), j)), Cf.lookup(Cf.del(d, k), j), pcf.pick_false(Nat.is_eq(k, j), v, Cf.lookup(Cf.del(d, k), j), h)) : {_ == Cf.lookup(d, j) : Maybe<&2, Nat>}
      pcf.del_keeps(d, k, j, h)
    case Cf.Del{+k}:
      pcf.del_keeps(d, k, j, h)

# LAW rmw_applies_change
def pcf.rmw_applies_change(+d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.kept(Cf.rmw(Cf.Parsed{d}, Cf.Set{k, v}), k) == Some{v} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, Ppr.ppr.nat_eq_refl(k)) : {Cf.pick(_, v, Cf.lookup(Cf.del(d, k), k)) == Some{v} : Maybe<&2, Nat>}
  {==}

# LAW settings_save_preserves
def pcf.settings_save_preserves(loaded: List<&2, Cf.Entry>, d: List<&2, Cf.Entry>, +k: Nat, v: Nat) -> {Cf.save(loaded, Cf.Parsed{d}, k, v) == Cf.Wrote{Cf.set(d, k, v)} : Cf.Write}:
  {==}

# Leaves
# ------

# the leaf x applies or is reported
def pcf.leaf_head(+x: Cf.Leaf, +rest: List<&2, Cf.Leaf>) -> {Bool.or(Cf.listed(Cf.applied(x <> rest), Cf.Leaf.path(x)), Cf.listed(Cf.reported(x <> rest), Cf.Leaf.path(x))) == True{} : Bool}:
  match x:
    case Cf.Leaf{+p, o}:
      match o:
        case Cf.Good{}:
          +a = Cf.listed(Cf.applied(rest), p)
          Ppr.ppr.or_l(Bool.or(Nat.is_eq(p, p), a), Cf.listed(Cf.reported(rest), p), Ppr.ppr.or_l(Nat.is_eq(p, p), a, Ppr.ppr.nat_eq_refl(p)))
        case Cf.BadType{}:
          +b = Cf.listed(Cf.reported(rest), p)
          Ppr.ppr.or_r(Cf.listed(Cf.applied(rest), p), Bool.or(Nat.is_eq(p, p), b), Ppr.ppr.or_l(Nat.is_eq(p, p), b, Ppr.ppr.nat_eq_refl(p)))
        case Cf.Undeclared{}:
          +b = Cf.listed(Cf.reported(rest), p)
          Ppr.ppr.or_r(Cf.listed(Cf.applied(rest), p), Bool.or(Nat.is_eq(p, p), b), Ppr.ppr.or_l(Nat.is_eq(p, p), b, Ppr.ppr.nat_eq_refl(p)))

# a path that applies or is reported in rest stays so with x before rest
def pcf.leaf_cons(+x: Cf.Leaf, +rest: List<&2, Cf.Leaf>, +n: Nat, h: {Bool.or(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == True{} : Bool}) -> {Bool.or(Cf.listed(Cf.applied(x <> rest), n), Cf.listed(Cf.reported(x <> rest), n)) == True{} : Bool}:
  match x:
    case Cf.Leaf{+p, o}:
      match o:
        case Cf.Good{}:
          Ppr.ppr.or_in_l(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)
        case Cf.BadType{}:
          Ppr.ppr.or_in_r(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)
        case Cf.Undeclared{}:
          Ppr.ppr.or_in_r(Nat.is_eq(p, n), Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n), h)

# LAW leaf_applied_or_reported
def pcf.leaf_applied_or_reported(ls: List<&2, Cf.Leaf>, +l: Cf.Leaf, i: Cf.In(l, ls)) -> {Bool.or(Cf.listed(Cf.applied(ls), Cf.Leaf.path(l)), Cf.listed(Cf.reported(ls), Cf.Leaf.path(l))) == True{} : Bool}:
  match ls:
    case Nil{}:
      match i:
    case +x <> +rest:
      match i:
        case Inl{eq}:
          %Equal.sym(Cf.Leaf, l, x, eq) : {Bool.or(Cf.listed(Cf.applied(x <> rest), Cf.Leaf.path(_)), Cf.listed(Cf.reported(x <> rest), Cf.Leaf.path(_))) == True{} : Bool}
          pcf.leaf_head(x, rest)
        case Inr{it}:
          pcf.leaf_cons(x, rest, Cf.Leaf.path(l), pcf.leaf_applied_or_reported(rest, l, it))

# an applied path is the path of a leaf
def pcf.applied_sub(ls: List<&2, Cf.Leaf>, +q: Nat) -> {Cf.listed(Cf.applied(ls), q) == True{} : Bool} -> {Cf.listed(Cf.paths(ls), q) == True{} : Bool}:
  match ls:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              h => Ppr.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.applied(rest), q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q), h)
            case Cf.BadType{}:
              h => Ppr.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q)(h))
            case Cf.Undeclared{}:
              h => Ppr.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.applied_sub(rest, q)(h))

# a reported path is the path of a leaf
def pcf.reported_sub(ls: List<&2, Cf.Leaf>, +q: Nat) -> {Cf.listed(Cf.reported(ls), q) == True{} : Bool} -> {Cf.listed(Cf.paths(ls), q) == True{} : Bool}:
  match ls:
    case Nil{}:
      h => h
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              h => Ppr.ppr.or_r(Nat.is_eq(p, q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q)(h))
            case Cf.BadType{}:
              h => Ppr.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.reported(rest), q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q), h)
            case Cf.Undeclared{}:
              h => Ppr.ppr.or_mono(Nat.is_eq(p, q), Cf.listed(Cf.reported(rest), q), Cf.listed(Cf.paths(rest), q), pcf.reported_sub(rest, q), h)

# a list of paths of rest does not name q when the paths of rest do not
def pcf.not_in(b: Bool, +ns: List<&2, Nat>, +rest: List<&2, Cf.Leaf>, +q: Nat, eb: {Cf.listed(ns, q) == b : Bool}, sub: {Cf.listed(ns, q) == True{} : Bool} -> {Cf.listed(Cf.paths(rest), q) == True{} : Bool}, out: {Cf.listed(Cf.paths(rest), q) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Ppr.ppr.absurd({True{} == False{} : Bool}, Equal.trans(Bool, True{}, Cf.listed(Cf.paths(rest), q), False{}, Equal.sym(Bool, Cf.listed(Cf.paths(rest), q), True{}, sub(eb)), out))
    case False{}:
      {==}

# a good leaf of path p, c saying whether p is n
def pcf.good_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Cf.Leaf>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Cf.listed(Cf.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}) -> {Bool.and(Bool.or(c, Cf.listed(Cf.applied(rest), n)), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}:
  match c:
    case True{}:
      %Ppr.ppr.nat_eq_true(p, n, ec) : {Cf.listed(Cf.reported(rest), _) == False{} : Bool}
      pcf.not_in(Cf.listed(Cf.reported(rest), p), Cf.reported(rest), rest, p, {==}, pcf.reported_sub(rest, p), dp)
    case False{}:
      ih

# a leaf of path p that does not apply, c saying whether p is n
def pcf.bad_at(c: Bool, +p: Nat, +n: Nat, +rest: List<&2, Cf.Leaf>, +ec: {Nat.is_eq(p, n) == c : Bool}, +dp: {Cf.listed(Cf.paths(rest), p) == False{} : Bool}, ih: {Bool.and(Cf.listed(Cf.applied(rest), n), Cf.listed(Cf.reported(rest), n)) == False{} : Bool}) -> {Bool.and(Cf.listed(Cf.applied(rest), n), Bool.or(c, Cf.listed(Cf.reported(rest), n))) == False{} : Bool}:
  match c:
    case True{}:
      +eL = pcf.not_in(Cf.listed(Cf.applied(rest), p), Cf.applied(rest), rest, p, {==}, pcf.applied_sub(rest, p), dp)
      %Ppr.ppr.nat_eq_true(p, n, ec) : {Bool.and(Cf.listed(Cf.applied(rest), _), True{}) == False{} : Bool}
      %Equal.sym(Bool, Cf.listed(Cf.applied(rest), p), False{}, eL) : {Bool.and(_, True{}) == False{} : Bool}
      {==}
    case False{}:
      ih

# LAW leaf_not_both
def pcf.leaf_not_both(ls: List<&2, Cf.Leaf>, +n: Nat, +d: {Cf.distinct(ls) == True{} : Bool}) -> {Bool.and(Cf.listed(Cf.applied(ls), n), Cf.listed(Cf.reported(ls), n)) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Leaf{+p, o}:
          match o:
            case Cf.Good{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = Ppr.ppr.not_t(Cf.listed(Cf.paths(rest), p), Ppr.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.good_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, Ppr.ppr.and_r(nd, Cf.distinct(rest), d)))
            case Cf.BadType{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = Ppr.ppr.not_t(Cf.listed(Cf.paths(rest), p), Ppr.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, Ppr.ppr.and_r(nd, Cf.distinct(rest), d)))
            case Cf.Undeclared{}:
              +nd = Bool.not(Cf.listed(Cf.paths(rest), p))
              +dp = Ppr.ppr.not_t(Cf.listed(Cf.paths(rest), p), Ppr.ppr.and_l(nd, Cf.distinct(rest), d))
              pcf.bad_at(Nat.is_eq(p, n), p, n, rest, {==}, dp, pcf.leaf_not_both(rest, n, Ppr.ppr.and_r(nd, Cf.distinct(rest), d)))

# Admission limits
# ----------------

def pcf.malformed_cap(m: Maybe<&2, Cf.Val>, h: {Cf.malformed_val(m) == True{} : Bool}) -> {Cf.slot_limit(m) == Cf.Cap{1n} : Cf.Lim}:
  match m:
    case None{}:
      Ppr.ppr.absurdF({Cf.slot_limit(None{}) == Cf.Cap{1n} : Cf.Lim}, h)
    case Some{v}:
      match v:
        case Cf.Num{n}:
          Ppr.ppr.absurdF({Cf.slot_limit(Some{Cf.Num{n}}) == Cf.Cap{1n} : Cf.Lim}, h)
        case Cf.Malformed{}:
          {==}

# LAW limit_malformed_fails_closed
def pcf.limit_malformed_fails_closed(s: Cf.InFlight, +p: Nat, h: {Cf.malformed_at(s, p) == True{} : Bool}) -> {Cf.limit(s, p) == Cf.Cap{1n} : Cf.Lim}:
  match s:
    case Cf.Unset{}:
      Ppr.ppr.absurdF({Cf.limit(Cf.Unset{}, p) == Cf.Cap{1n} : Cf.Lim}, h)
    case Cf.Entries{es}:
      pcf.malformed_cap(Cf.slot(es, p), h)
    case Cf.NotMap{}:
      {==}

# LAW limit_number_applies
def pcf.limit_number_applies(es: List<&2, Cf.Slot>, +p: Nat, +n: Nat, h: {Cf.slot(es, p) == Some{Cf.Num{n}} : Maybe<&2, Cf.Val>}) -> {Cf.limit(Cf.Entries{es}, p) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}:
  %Equal.sym(Maybe<&2, Cf.Val>, Cf.slot(es, p), Some{Cf.Num{n}}, h) : {Cf.slot_limit(_) == Cf.val_limit(Cf.Num{n}) : Cf.Lim}
  {==}

# Trust
# -----

# LAW untrusted_changes_nothing_guarded
def pcf.untrusted_changes_nothing_guarded(+g: List<&2, Cf.Entry>, items: List<&2, Cf.Item>, +k: Nat, +h: {Cf.only_guarded(items, k) == True{} : Bool}) -> {Cf.lookup(Cf.effective(Cf.Untrusted{}, g, items), k) == Cf.lookup(g, k) : Maybe<&2, Nat>}:
  match items:
    case Nil{}:
      {==}
    case i <> +rest:
      match i:
        case Cf.Item{+j, kind, v}:
          match kind:
            case Cf.Pref{}:
              +ne = Bool.not(Nat.is_eq(j, k))
              +og = Cf.only_guarded(rest, k)
              +ejk = Ppr.ppr.not_t(Nat.is_eq(j, k), Ppr.ppr.and_l(ne, og, h))
              +later = Cf.lookup(Cf.effective(Cf.Untrusted{}, g, rest), k)
              %Equal.sym(Maybe<&2, Nat>, Cf.pick(Nat.is_eq(j, k), v, later), later, pcf.pick_false(Nat.is_eq(j, k), v, later, ejk)) : {_ == Cf.lookup(g, k) : Maybe<&2, Nat>}
              pcf.untrusted_changes_nothing_guarded(g, rest, k, Ppr.ppr.and_r(ne, og, h))
            case Cf.Limit{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)
            case Cf.Prompt{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)
            case Cf.Credential{}:
              pcf.untrusted_changes_nothing_guarded(g, rest, k, h)

# LAW trusted_project_applies
def pcf.trusted_project_applies(g: List<&2, Cf.Entry>, +k: Nat, kind: Cf.Class, v: Nat, items: List<&2, Cf.Item>) -> {Cf.lookup(Cf.effective(Cf.Trusted{}, g, Cf.Item{k, kind, v} <> items), k) == Some{v} : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Nat.is_eq(k, k), True{}, Ppr.ppr.nat_eq_refl(k)) : {Cf.pick(_, v, Cf.lookup(Cf.effective(Cf.Trusted{}, g, items), k)) == Some{v} : Maybe<&2, Nat>}
  {==}

# Named entries
# -------------

# the first project entry, b saying whether it is named n
def pcf.merge_at(b: Bool, +fs: List<&2, Cf.Entry>, +x: Maybe<&2, List<&2, Cf.Entry>>, +y: Maybe<&2, List<&2, Cf.Entry>>, +r: Bool, h: {Bool.or(b, r) == True{} : Bool}, ih: {r == True{} : Bool} -> {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Cf.find.pick(b, fs, y) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# LAW project_entry_never_merges
def pcf.project_entry_never_merges(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat, h: {Cf.has(p, n) == True{} : Bool}) -> {Cf.find(Cf.merge(g, p), n) == Cf.find(p, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      Ppr.ppr.absurdF({Cf.find(Cf.merge(g, Nil{}), n) == Cf.find(Nil{}, n) : Maybe<&2, List<&2, Cf.Entry>>}, h)
    case e <> +rest:
      match e:
        case Cf.Named{+m, +fs}:
          pcf.merge_at(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Cf.find(rest, n), Cf.has(rest, n), h, hr => pcf.project_entry_never_merges(g, rest, n, hr))

# the first project entry when the project does not name n
def pcf.kept_at(b: Bool, +fs: List<&2, Cf.Entry>, +x: Maybe<&2, List<&2, Cf.Entry>>, +y: Maybe<&2, List<&2, Cf.Entry>>, +r: Bool, h: {Bool.or(b, r) == False{} : Bool}, ih: {r == False{} : Bool} -> {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == y : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      Ppr.ppr.absurd({Cf.find.pick(True{}, fs, x) == y : Maybe<&2, List<&2, Cf.Entry>>}, h)
    case False{}:
      ih(h)

# LAW global_entry_kept
def pcf.global_entry_kept(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat, h: {Cf.has(p, n) == False{} : Bool}) -> {Cf.find(Cf.merge(g, p), n) == Cf.find(g, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Named{+m, +fs}:
          pcf.kept_at(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Cf.find(g, n), Cf.has(rest, n), h, hr => pcf.global_entry_kept(g, rest, n, hr))

# The saved default model
# -----------------------
# The proofs are in bend/proof_default_model.bend.

def pcf.default_honoured_or_reported(x: Dm.In) -> {Dm.reported(x, Dm.open(Dm.resolve(x))) == True{} : Bool}:
  Pdm.pdm.default_honoured_or_reported(x)

def pcf.default_quiet_when_honoured(x: Dm.In, h: {Dm.on_saved(Dm.Session.run(Dm.open(Dm.resolve(x)))) == True{} : Bool}) -> {Dm.none(Dm.Session.notes(Dm.open(Dm.resolve(x)))) == True{} : Bool}:
  Pdm.pdm.default_quiet_when_honoured(x, h)

def pcf.default_quiet_when_unset(cat: Bool, key: Bool, out: Bool, next: Dm.Next) -> {Dm.Session.notes(Dm.open(Dm.resolve(Dm.In{Dm.NoDefault{}, cat, key, out, next}))) == Nil{} : List<&2, Dm.Key>}:
  Pdm.pdm.default_quiet_when_unset(cat, key, out, next)

def pcf.default_unkeyed_never_moves(m: Nat, out: Bool, next: Dm.Next) -> {Dm.Session.run(Dm.open(Dm.resolve(Dm.In{Dm.Default{m}, True{}, False{}, out, next}))) == Dm.Idle{} : Dm.Run}:
  Pdm.pdm.default_unkeyed_never_moves(m, out, next)
