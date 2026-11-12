# eukhe: the proof of LAW semver_ffi_release_behind

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/semver.bend as Semver
import ../base/nat.bend as LNat
import ./base.bend as LASemver

# PROOF of LAW semver_ffi_release_behind: the request reads back whole and
# passes the 7-digit guard (svr.reply); with no release from X.Y.0 the
# entry answers 2, the next release n written, and FSv.newer(n, ts). The
# mask is each tag's answer to "names n or a newer version" (bh.mask); the
# tags it keeps are FSv.newer(n, ts) (bh.pick: newer drops a tag exactly
# when it names no version or one older than n, Rel.older), each of which
# names n or a newer version (bh.all), as many as there are (bh.len).

# the mask: for each tag, whether it names n or a newer version
def bh.mask(+n: Sv.Ver, ts: List<&2, String>) -> List<&2, Bool>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      Semver.behind_spec(n, t) <> bh.mask(n, r)

def bh.pick_k(k: Bool, -t: String, -rest: List<&2, String>) -> {Semver.pick_spec.at(k, t, rest) == FSv.newer.keep(Bool.not(k), t, rest) : List<&2, String>}:
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

def bh.pick_at(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, -t: String, -rest: List<&2, String>) -> {Semver.pick_spec.at(Semver.behind_spec.of(m, n), t, rest) == FSv.newer.keep(Sv.Rel.older(n, m), t, rest) : List<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      bh.pick_k(Sv.Ver.le(n, v), t, rest)

# the tags the mask keeps are the newer tags of the entry
def bh.pick(+n: Sv.Ver, ts: List<&2, String>) -> {Semver.pick_spec(ts, bh.mask(n, ts)) == FSv.newer(n, ts) : List<&2, String>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %Equal.sym(List<&2, String>, Semver.pick_spec(r, bh.mask(n, r)), FSv.newer(n, r), bh.pick(n, r)) : {Semver.pick_spec.at(Semver.behind_spec(n, t), t, _) == FSv.newer(n, t <> r) : List<&2, String>}
      bh.pick_at(Sv.Tag.ver(t), n, t, FSv.newer(n, r))

def bh.all_k(k: Bool, +n: Sv.Ver, +v: Sv.Ver, +t: String, +rest: List<&2, String>, ek: {Sv.Ver.le(n, v) == k : Bool}, em: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, ih: {Semver.behind_all(n, rest) == True{} : Bool}) -> {Semver.behind_all(n, FSv.newer.keep(Bool.not(k), t, rest)) == True{} : Bool}:
  match k:
    case True{}:
      %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Tag.ver(t), Some{v}, em) : {Bool.and(Semver.behind_spec.of(_, n), Semver.behind_all(n, rest)) == True{} : Bool}
      %Equal.sym(Bool, Sv.Ver.le(n, v), True{}, ek) : {Bool.and(_, Semver.behind_all(n, rest)) == True{} : Bool}
      ih
    case False{}:
      ih

def bh.all_at(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, +t: String, +rest: List<&2, String>, em: {Sv.Tag.ver(t) == m : Maybe<&2, Sv.Ver>}, ih: {Semver.behind_all(n, rest) == True{} : Bool}) -> {Semver.behind_all(n, FSv.newer.keep(Sv.Rel.older(n, m), t, rest)) == True{} : Bool}:
  match m:
    case None{}:
      ih
    case Some{+v}:
      bh.all_k(Sv.Ver.le(n, v), n, v, t, rest, {==}, em, ih)

# every newer tag names n or a newer version
def bh.all(+n: Sv.Ver, ts: List<&2, String>) -> {Semver.behind_all(n, FSv.newer(n, ts)) == True{} : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      bh.all_at(Sv.Tag.ver(t), n, t, FSv.newer(n, r), {==}, bh.all(n, r))

def bh.len_k(k: Bool, -t: String, +rest: List<&2, String>, -K: Nat, ih: {List.length(&2, String, rest) == K : Nat}) -> {List.length(&2, String, FSv.newer.keep(Bool.not(k), t, rest)) == Semver.behind_count.add(k, K) : Nat}:
  match k:
    case True{}:
      Equal.cong(Nat, Nat, x => 1n+x, List.length(&2, String, rest), K, ih)
    case False{}:
      ih

def bh.len_at(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, -t: String, +rest: List<&2, String>, -K: Nat, ih: {List.length(&2, String, rest) == K : Nat}) -> {List.length(&2, String, FSv.newer.keep(Sv.Rel.older(n, m), t, rest)) == Semver.behind_count.add(Semver.behind_spec.of(m, n), K) : Nat}:
  match m:
    case None{}:
      ih
    case Some{+v}:
      bh.len_k(Sv.Ver.le(n, v), t, rest, K, ih)

# as many newer tags as tags that name n or a newer version
def bh.len(+n: Sv.Ver, ts: List<&2, String>) -> {List.length(&2, String, FSv.newer(n, ts)) == Semver.behind_count(n, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      bh.len_at(Sv.Tag.ver(t), n, t, FSv.newer(n, r), Semver.behind_count(n, r), bh.len(n, r))

# the reply: 2, n written, the tags the mask keeps
def bh.put(+c: String, +ts: List<&2, String>, +a: Nat, +b: Nat, +parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}, none: {Sv.Rel.release(c, ts) == None{} : Maybe<&2, Sv.Ver>}) -> {FSv.release.put(Sv.Rel.release(c, ts), c, ts) == Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)), Semver.spell_tags(Semver.pick_spec(ts, bh.mask(Sv.Rel.next(Sv.Ver{a, b, 0n}, ts), ts)), ""))) : String}:
  +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Rel.release(c, ts), None{}, none) : {FSv.release.put(_, c, ts) == Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(n), Semver.spell_tags(Semver.pick_spec(ts, bh.mask(n, ts)), ""))) : String}
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 0n}}, parsed) : {FSv.release.miss(_, ts) == Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(n), Semver.spell_tags(Semver.pick_spec(ts, bh.mask(n, ts)), ""))) : String}
  %Equal.sym(List<&2, String>, Semver.pick_spec(ts, bh.mask(n, ts)), FSv.newer(n, ts), bh.pick(n, ts)) : {FSv.release.patch(a, b, 0n, ts) == Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(n), Semver.spell_tags(_, ""))) : String}
  {==}

# the kept tags each name n or a newer version, as many as the tags that do
def bh.count(+n: Sv.Ver, +ts: List<&2, String>) -> {Bool.and(Semver.behind_all(n, Semver.pick_spec(ts, bh.mask(n, ts))), Nat.is_eq(List.length(&2, String, Semver.pick_spec(ts, bh.mask(n, ts))), Semver.behind_count(n, ts))) == True{} : Bool}:
  %Equal.sym(List<&2, String>, Semver.pick_spec(ts, bh.mask(n, ts)), FSv.newer(n, ts), bh.pick(n, ts)) : {Bool.and(Semver.behind_all(n, _), Nat.is_eq(List.length(&2, String, _), Semver.behind_count(n, ts))) == True{} : Bool}
  %Equal.sym(Bool, Semver.behind_all(n, FSv.newer(n, ts)), True{}, bh.all(n, ts)) : {Bool.and(_, Nat.is_eq(List.length(&2, String, FSv.newer(n, ts)), Semver.behind_count(n, ts))) == True{} : Bool}
  %Equal.sym(Nat, List.length(&2, String, FSv.newer(n, ts)), Semver.behind_count(n, ts), bh.len(n, ts)) : {Nat.is_eq(_, Semver.behind_count(n, ts)) == True{} : Bool}
  LNat.ppr.nat_eq_refl(Semver.behind_count(n, ts))

def Semver.semver_ffi_release_behind(c, ts, fit, few, a, b, parsed, none):
  +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)
  (bh.mask(n, ts), (LASemver.svr.reply(c, ts, fit, few, Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(n), Semver.spell_tags(Semver.pick_spec(ts, bh.mask(n, ts)), ""))), bh.put(c, ts, a, b, parsed, none)), bh.count(n, ts)))
