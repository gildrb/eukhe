# eukhe: lemmas the proofs of area config share

import Base
import ../../../bend/config.bend as Cf
import ../../../laws/config.bend as Config
import ../../../spec/settings/config_rules.bend as CR
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat
import ../../base/logic/nat.bend as LLogicNat

# ---- config ----

# proof_config: lemmas for LAWS.bend section config over bend/config.bend (and
# bend/default_model.bend, proved in PROOF.bend section default_model).
#
# Writes. A broken read writes nothing by definition. A set gives every
# entry of its key the new value in its place, or puts a new entry last;
# a delete drops the entries of its key. Neither changes the first entry
# of another key (`pcf.del_keeps`, `pcf.set_miss`, inductions on the
# document).
#
# Leaves. Each leaf adds its path to the applied list when it is good,
# and to the reported list when it is not; the proofs follow the skill
# loading proofs of PROOF.bend section progress_report, whose logic lemmas
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

# Writes
# ------

# a false pick is the later value
def pcf.pick_false(b: Bool, v: Nat, +later: Maybe<&2, Nat>, h: {b == False{} : Bool}) -> {Cf.pick(b, v, later) == later : Maybe<&2, Nat>}:
  match b:
    case True{}:
      LLogicLogic.ppr.absurd({Cf.pick(True{}, v, later) == later : Maybe<&2, Nat>}, h)
    case False{}:
      {==}

# Sets
# ----

# Some v when b, else none
def pcf.some_if(b: Bool, v: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{v}
    case False{}:
      None{}

# m, or Some v when m is none
def pcf.or_some(m: Maybe<&2, Nat>, v: Nat) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{v}
    case Some{x}:
      Some{x}

# none when b, else m
def pcf.none_unless(b: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      None{}
    case False{}:
      m

def pcf.rep_hit.step(b: Bool, w: Nat, +v: Nat, later: Maybe<&2, Nat>, h: Bool, ih: {later == pcf.some_if(h, v) : Maybe<&2, Nat>}) -> {Cf.pick(b, Cf.pick_v(b, v, w), later) == pcf.some_if(Bool.or(b, h), v) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a replace of key k: the first entry of k holds v when d has k
def pcf.rep_hit(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.lookup(Cf.replace(d, k, v), k) == pcf.some_if(Cf.has_key(d, k), v) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, w}:
          pcf.rep_hit.step(Nat.is_eq(j, k), w, v, Cf.lookup(Cf.replace(rest, k, v), k), Cf.has_key(rest, k), pcf.rep_hit(rest, k, v))

def pcf.app_hit.step(b: Bool, w: Nat, v: Nat, l1: Maybe<&2, Nat>, l2: Maybe<&2, Nat>, ih: {l1 == pcf.or_some(l2, v) : Maybe<&2, Nat>}) -> {Cf.pick(b, w, l1) == pcf.or_some(Cf.pick(b, w, l2), v) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# an entry of key k put last: the first entry of k is d's, else the new one
def pcf.app_hit(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.lookup(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}]), k) == pcf.or_some(Cf.lookup(d, k), v) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, LNat.ppr.nat_eq_refl(k)) : {Cf.pick(_, v, None{}) == Some{v} : Maybe<&2, Nat>}
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, w}:
          pcf.app_hit.step(Nat.is_eq(j, k), w, v, Cf.lookup(List.append(&2, Cf.Entry, rest, [Cf.Entry{k, v}]), k), Cf.lookup(rest, k), pcf.app_hit(rest, k, v))

def pcf.miss.step(b: Bool, w: Nat, l: Maybe<&2, Nat>, h: Bool, ih: {pcf.none_unless(h, l) == None{} : Maybe<&2, Nat>}) -> {pcf.none_unless(Bool.or(b, h), Cf.pick(b, w, l)) == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a document without key k has no entry of k
def pcf.miss(d: List<&2, Cf.Entry>, +k: Nat) -> {pcf.none_unless(Cf.has_key(d, k), Cf.lookup(d, k)) == None{} : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, w}:
          pcf.miss.step(Nat.is_eq(j, k), w, Cf.lookup(rest, k), Cf.has_key(rest, k), pcf.miss(rest, k))

def pcf.unless_false(b: Bool, m: Maybe<&2, Nat>, e: {b == False{} : Bool}, h: {pcf.none_unless(b, m) == None{} : Maybe<&2, Nat>}) -> {m == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      LLogicLogic.ppr.absurd({m == None{} : Maybe<&2, Nat>}, e)
    case False{}:
      h

def pcf.set_hit.go(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, eb: {Cf.has_key(d, k) == b : Bool}) -> {Cf.lookup(Cf.set.go(b, d, k, v), k) == Some{v} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Nat>, Cf.lookup(Cf.replace(d, k, v), k), pcf.some_if(Cf.has_key(d, k), v), pcf.rep_hit(d, k, v)) : {_ == Some{v} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Cf.has_key(d, k), True{}, eb) : {pcf.some_if(_, v) == Some{v} : Maybe<&2, Nat>}
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Nat>, Cf.lookup(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}]), k), pcf.or_some(Cf.lookup(d, k), v), pcf.app_hit(d, k, v)) : {_ == Some{v} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Cf.lookup(d, k), None{}, pcf.unless_false(Cf.has_key(d, k), Cf.lookup(d, k), eb, pcf.miss(d, k))) : {pcf.or_some(_, v) == Some{v} : Maybe<&2, Nat>}
      {==}

# a set of key k to v: the first entry of k holds v
def pcf.set_hit(+d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.lookup(Cf.set(d, k, v), k) == Some{v} : Maybe<&2, Nat>}:
  pcf.set_hit.go(Cf.has_key(d, k), d, k, v, {==})

def pcf.not_both.go(b: Bool, +i: Nat, +j: Nat, +k: Nat, e: {Nat.is_eq(i, k) == b : Bool}, h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Bool.and(b, Nat.is_eq(i, j)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, i, k, LLogicNat.ppr.nat_eq_true(i, k, e)) : {Nat.is_eq(_, j) == False{} : Bool}
      h
    case False{}:
      {==}

def pcf.rep_miss.step(b1: Bool, b2: Bool, w: Nat, v: Nat, l1: Maybe<&2, Nat>, l2: Maybe<&2, Nat>, ih: {l1 == l2 : Maybe<&2, Nat>}, no: {Bool.and(b2, b1) == False{} : Bool}) -> {Cf.pick(b1, Cf.pick_v(b2, v, w), l1) == Cf.pick(b1, w, l2) : Maybe<&2, Nat>}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          LLogicLogic.ppr.absurd({Cf.pick(True{}, Cf.pick_v(True{}, v, w), l1) == Cf.pick(True{}, w, l2) : Maybe<&2, Nat>}, no)
        case False{}:
          {==}
    case False{}:
      ih

# a replace of key k keeps the first entry of every other key j
def pcf.rep_miss(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(Cf.replace(d, k, v), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+i, w}:
          pcf.rep_miss.step(Nat.is_eq(i, j), Nat.is_eq(i, k), w, v, Cf.lookup(Cf.replace(rest, k, v), j), Cf.lookup(rest, j), pcf.rep_miss(rest, k, v, j, h), pcf.not_both.go(Nat.is_eq(i, k), i, j, k, {==}, h))

# an entry of key k put last keeps the first entry of every other key j
def pcf.app_miss(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(List.append(&2, Cf.Entry, d, [Cf.Entry{k, v}]), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      pcf.pick_false(Nat.is_eq(k, j), v, None{}, h)
    case e <> +rest:
      match e:
        case Cf.Entry{+i, w}:
          %pcf.app_miss(rest, k, v, j, h) : {Cf.pick(Nat.is_eq(i, j), w, Cf.lookup(List.append(&2, Cf.Entry, rest, [Cf.Entry{k, v}]), j)) == Cf.pick(Nat.is_eq(i, j), w, _) : Maybe<&2, Nat>}
          {==}

def pcf.set_miss.go(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(Cf.set.go(b, d, k, v), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      pcf.rep_miss(d, k, v, j, h)
    case False{}:
      pcf.app_miss(d, k, v, j, h)

# a set of key k keeps the first entry of every other key j
def pcf.set_miss(+d: List<&2, Cf.Entry>, +k: Nat, +v: Nat, +j: Nat, +h: {Nat.is_eq(k, j) == False{} : Bool}) -> {Cf.lookup(Cf.set(d, k, v), j) == Cf.lookup(d, j) : Maybe<&2, Nat>}:
  pcf.set_miss.go(Cf.has_key(d, k), d, k, v, j, h)

# Project keys
# ------------

def pcf.cl.prefix(a: List<&2, String>, b: List<&2, String>) -> {Cf.prefix(a, b) == Config.cf_prefix(a, b) : Bool}:
  match a:
    case Nil{}:
      {==}
    case +x <> +xs:
      match b:
        case Nil{}:
          {==}
        case +y <> +ys:
          %pcf.cl.prefix(xs, ys) : {Bool.and(String.eq(x, y), Cf.prefix(xs, ys)) == Bool.and(String.eq(x, y), _) : Bool}
          {==}

def pcf.cl.join.go(xs: List<&2, String>, +x: String) -> {Cf.join(x <> xs) == Config.cf_join.go(xs, x) : String}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +ys:
      %pcf.cl.join.go(ys, y) : {String.append(x, SCon{'.', Cf.join(y <> ys)}) == String.append(x, SCon{'.', _}) : String}
      {==}

# the model joins a path as the laws do
def pcf.cl.join(p: List<&2, String>) -> {Cf.join(p) == Config.cf_join(p) : String}:
  match p:
    case Nil{}:
      {==}
    case x <> xs:
      pcf.cl.join.go(xs, x)

def pcf.cl.head(p: List<&2, String>) -> {Cf.first_name(p) == Config.cf_head(p) : String}:
  match p:
    case Nil{}:
      {==}
    case x <> xs:
      {==}

def pcf.cl.pick(b: Bool, +q: List<&2, String>, s: Cf.Scope, x: Cf.Hit, y: Cf.Hit, ih: {x == y : Cf.Hit}) -> {Cf.classify.pick(b, q, s, x) == Config.cf_hit.pick(b, q, s, y) : Cf.Hit}:
  match b:
    case True{}:
      %pcf.cl.join(q) : {Cf.Hit{Cf.join(q), s} == Cf.Hit{_, s} : Cf.Hit}
      {==}
    case False{}:
      ih

# the first rule whose path is a prefix, over any table
def pcf.cl.go(rs: List<&2, Cf.Rule>, +p: List<&2, String>) -> {Cf.classify.go(rs, p) == Config.cf_hit(rs, p) : Cf.Hit}:
  match rs:
    case Nil{}:
      %pcf.cl.head(p) : {Cf.Hit{Cf.first_name(p), Cf.Proj{Cf.Code{}}} == Cf.Hit{_, Cf.Proj{Cf.Code{}}} : Cf.Hit}
      {==}
    case r <> +rest:
      match r:
        case Cf.Rule{+q, s}:
          %pcf.cl.prefix(q, p) : {Cf.classify.pick(Cf.prefix(q, p), q, s, Cf.classify.go(rest, p)) == Config.cf_hit.pick(_, q, s, Config.cf_hit(rest, p)) : Cf.Hit}
          pcf.cl.pick(Cf.prefix(q, p), q, s, Cf.classify.go(rest, p), Config.cf_hit(rest, p), pcf.cl.go(rest, p))

def pcf.cl.rules() -> {Cf.rules() == Config.cf_rules() : List<&2, Cf.Rule>}:
  {==}

# the model classifies a path as the laws do
def pcf.classify(+p: List<&2, String>) -> {Cf.classify(p) == Config.cf_hit(Config.cf_rules(), p) : Cf.Hit}:
  %pcf.cl.rules() : {Cf.classify.go(Cf.rules(), p) == Config.cf_hit(_, p) : Cf.Hit}
  pcf.cl.go(Cf.rules(), p)

# the model's verdict on a scope is the laws'
def pcf.applies(t: Cf.Trust, s: Cf.Scope) -> {Cf.applies(t, s) == Config.cf_applies(t, s) : Bool}:
  match t:
    case Cf.Trusted{}:
      match s:
        case Cf.Proj{c}:
          {==}
        case Cf.GlobalOnly{}:
          {==}
    case Cf.Untrusted{}:
      match s:
        case Cf.Proj{c}:
          match c:
            case Cf.Pref{}:
              {==}
            case Cf.Limit{}:
              {==}
            case Cf.Prompt{}:
              {==}
            case Cf.Credential{}:
              {==}
            case Cf.Code{}:
              {==}
        case Cf.GlobalOnly{}:
          {==}

# The model's helpers are the laws' restatements
# ----------------------------------------------

def pcf.wx.pv(b: Bool, v: Nat, w: Nat) -> {Cf.pick_v(b, v, w) == Config.cf_put_v(b, v, w) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's replace is the laws'
def pcf.wx.rep(d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.replace(d, k, v) == Config.cf_replace(d, k, v) : List<&2, Cf.Entry>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+j, +w}:
          %pcf.wx.pv(Nat.is_eq(j, k), v, w) : {Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> Cf.replace(t, k, v) == Cf.Entry{j, _} <> Config.cf_replace(t, k, v) : List<&2, Cf.Entry>}
          %pcf.wx.rep(t, k, v) : {Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> Cf.replace(t, k, v) == Cf.Entry{j, Cf.pick_v(Nat.is_eq(j, k), v, w)} <> _ : List<&2, Cf.Entry>}
          {==}

# d has key k when its keys hold k
def pcf.wx.has(d: List<&2, Cf.Entry>, +k: Nat) -> {Cf.has_key(d, k) == Config.cf_mem(Config.cf_keys(d), k) : Bool}:
  match d:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Entry{+j, v}:
          %pcf.wx.has(rest, k) : {Bool.or(Nat.is_eq(j, k), Cf.has_key(rest, k)) == Bool.or(Nat.is_eq(j, k), _) : Bool}
          {==}

def pcf.wx.del.step(b: Bool, +j: Nat, +w: Nat, r: List<&2, Cf.Entry>, x: List<&2, Cf.Entry>, ih: {r == x : List<&2, Cf.Entry>}) -> {Cf.keep(b, Cf.Entry{j, w}, r) == Config.cf_without.keep(b, Cf.Entry{j, w}, x) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      ih
    case False{}:
      %ih : {Cf.Entry{j, w} <> r == Cf.Entry{j, w} <> _ : List<&2, Cf.Entry>}
      {==}

# the model's delete is the laws'
def pcf.wx.del(d: List<&2, Cf.Entry>, +k: Nat) -> {Cf.del(d, k) == Config.cf_without(d, k) : List<&2, Cf.Entry>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+j, w}:
          pcf.wx.del.step(Nat.is_eq(j, k), j, w, Cf.del(t, k), Config.cf_without(t, k), pcf.wx.del(t, k))

def pcf.wx.set(b: Bool, +d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.set.go(b, d, k, v) == Config.cf_set_in(b, d, k, v) : List<&2, Cf.Entry>}:
  match b:
    case True{}:
      pcf.wx.rep(d, k, v)
    case False{}:
      {==}

# a set is the laws' edit of a Set
def pcf.set_spec(+d: List<&2, Cf.Entry>, +k: Nat, +v: Nat) -> {Cf.set(d, k, v) == Config.cf_edited(d, Cf.Set{k, v}) : List<&2, Cf.Entry>}:
  %pcf.wx.has(d, k) : {Cf.set.go(Cf.has_key(d, k), d, k, v) == Config.cf_set_in(_, d, k, v) : List<&2, Cf.Entry>}
  pcf.wx.set(Cf.has_key(d, k), d, k, v)

def pcf.lim.val(v: Cf.Val) -> {Cf.val_limit(v) == Config.cf_lim_val(v) : Cf.Lim}:
  match v:
    case Cf.Num{n}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case Cf.Malformed{}:
      {==}

def pcf.lim.pick(b: Bool, v: Cf.Val, m: Maybe<&2, Cf.Val>, l: Cf.Lim, ih: {Cf.slot_limit(m) == l : Cf.Lim}) -> {Cf.slot_limit(Cf.slot.pick(b, v, m)) == Config.cf_slot_lim.pick(b, v, l) : Cf.Lim}:
  match b:
    case True{}:
      pcf.lim.val(v)
    case False{}:
      ih

def pcf.lim.slots(es: List<&2, Cf.Slot>, +p: Nat) -> {Cf.slot_limit(Cf.slot(es, p)) == Config.cf_slot_lim(es, p) : Cf.Lim}:
  match es:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Cf.Slot{q, v}:
          pcf.lim.pick(Nat.is_eq(q, p), v, Cf.slot(rest, p), Config.cf_slot_lim(rest, p), pcf.lim.slots(rest, p))

def pcf.lim.one(s: Cf.InFlight, +p: Nat) -> {Cf.limit(s, p) == Config.cf_limit(s, p) : Cf.Lim}:
  match s:
    case Cf.Unset{}:
      {==}
    case Cf.Entries{es}:
      pcf.lim.slots(es, p)
    case Cf.NotMap{}:
      {==}

def pcf.limit(s: Cf.InFlight, +p: Nat) -> {Cf.limit(s, p) == Config.cf_limit(s, p) : Cf.Lim}:
  pcf.lim.one(s, p)

def pcf.mf.pick(b: Bool, fs: List<&2, Cf.Entry>, x: Maybe<&2, List<&2, Cf.Entry>>, y: Maybe<&2, List<&2, Cf.Entry>>, ih: {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Config.cf_find.pick(b, fs, y) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the model's find is the laws' restatement
def pcf.mf.find(es: List<&2, Cf.Named>, +n: Nat) -> {Cf.find(es, n) == Config.cf_find(es, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Named{+m, fs}:
          pcf.mf.pick(Nat.is_eq(m, n), fs, Cf.find(rest, n), Config.cf_find(rest, n), pcf.mf.find(rest, n))

def pcf.mf.first(b: Bool, fs: List<&2, Cf.Entry>, x: Maybe<&2, List<&2, Cf.Entry>>, y: Maybe<&2, List<&2, Cf.Entry>>, z: Maybe<&2, List<&2, Cf.Entry>>, ih: {x == Config.cf_or(y, z) : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Config.cf_or(Config.cf_find.pick(b, fs, y), z) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a name in the merged map: the project's entry, else the global one
def pcf.mf.merged(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat) -> {Cf.find(Cf.merge(g, p), n) == Config.cf_or(Config.cf_find(p, n), Config.cf_find(g, n)) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      pcf.mf.find(g, n)
    case e <> +rest:
      match e:
        case Cf.Named{+m, fs}:
          pcf.mf.first(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Config.cf_find(rest, n), Config.cf_find(g, n), pcf.mf.merged(g, rest, n))

def pcf.lk.pick(b: Bool, v: Nat, x: Maybe<&2, Nat>, y: Maybe<&2, Nat>, ih: {x == y : Maybe<&2, Nat>}) -> {Cf.pick(b, v, x) == CR.cr_first(b, v, y) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pcf.lookup(d: List<&2, Cf.Entry>, +j: Nat) -> {Cf.lookup(d, j) == CR.cr_lookup(d, j) : Maybe<&2, Nat>}:
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{k, v}:
          pcf.lk.pick(Nat.is_eq(k, j), v, Cf.lookup(t, j), CR.cr_lookup(t, j), pcf.lookup(t, j))

def pcf.sl.pick(b: Bool, v: Cf.Val, x: Maybe<&2, Cf.Val>, y: Maybe<&2, Cf.Val>, ih: {x == y : Maybe<&2, Cf.Val>}) -> {Cf.slot.pick(b, v, x) == CR.cr_slot.pick(b, v, y) : Maybe<&2, Cf.Val>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def pcf.slot(es: List<&2, Cf.Slot>, +p: Nat) -> {Cf.slot(es, p) == CR.cr_slot(es, p) : Maybe<&2, Cf.Val>}:
  match es:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case Cf.Slot{q, v}:
          pcf.sl.pick(Nat.is_eq(q, p), v, Cf.slot(t, p), CR.cr_slot(t, p), pcf.slot(t, p))
