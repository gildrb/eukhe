# eukhe: the proof of LAW catalog_union_ffi_exact
# The entry reads every input as the spec's reader does and answers the
# spec's union: the fast union is the model's (union_fast), and the
# model's lookup, merge, bundled and extra parts are the spec's.

import Base
import ../../bend/catalog_union.bend as CU
import ../../bend/ffi_catalog_union.bend as FCu
import ../../bend/wire.bend as Wr
import ../../laws/catalog_union.bend as CatalogUnion
import ./union_fast.bend as PUnionFast

# The union
# ---------

def cx.pick(b: Bool, -e: CU.Ent, -rest: List<&2, CU.Ent>, -k: Nat, ih: {CU.find(rest, k) == CatalogUnion.cu_sp_find(rest, k) : Maybe<&2, CU.Ent>}) -> {CU.find.go(e <> rest, k, b) == CatalogUnion.cu_sp_pick(b, e, CatalogUnion.cu_sp_find(rest, k)) : Maybe<&2, CU.Ent>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def cx.find(xs: List<&2, CU.Ent>, +k: Nat) -> {CU.find(xs, k) == CatalogUnion.cu_sp_find(xs, k) : Maybe<&2, CU.Ent>}:
  match xs:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case CU.Ent{ek, ea, ed, et, ec, ef, eh}:
          cx.pick(Nat.is_eq(ek, k), CU.Ent{ek, ea, ed, et, ec, ef, eh}, rest, k, cx.find(rest, k))

def cx.has(+xs: List<&2, CU.Ent>, +k: Nat) -> {CU.has(xs, k) == Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_sp_find(xs, k)) : Bool}:
  %Equal.sym(Maybe<&2, CU.Ent>, CU.find(xs, k), CatalogUnion.cu_sp_find(xs, k), cx.find(xs, k)) : {Maybe.is_some(&2, CU.Ent, _) == Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_sp_find(xs, k)) : Bool}
  {==}

def cx.fill(o: Maybe<&2, Nat>, -c: Maybe<&2, Nat>, same: Bool) -> {CU.fill(o, c, same) == CatalogUnion.cu_sp_fill(o, c, same) : Maybe<&2, Nat>}:
  match o:
    case Some{v}:
      {==}
    case None{}:
      match same:
        case True{}:
          {==}
        case False{}:
          {==}

def cx.merge(b: CU.Ent, c: CU.Ent) -> {CU.merge(b, c) == CatalogUnion.cu_sp_merge(b, c) : CU.Ent}:
  match b c:
    case CU.Ent{bk, +ba, bd, +bt, +bc, +bf, +bh} CU.Ent{ck, +ca, cd, +ct, +cc, +cf, +ch}:
      %Equal.sym(Maybe<&2, Nat>, CU.fill(bt, ct, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bt, ct, Nat.is_eq(ba, ca)), cx.fill(bt, ct, Nat.is_eq(ba, ca))) : {CU.Ent{bk, ba, bd, _, CU.fill(bc, cc, Nat.is_eq(ba, ca)), CU.fill(bf, cf, Nat.is_eq(ba, ca)), CU.fill(bh, ch, Nat.is_eq(ba, ca))} == CatalogUnion.cu_sp_merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(bc, cc, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bc, cc, Nat.is_eq(ba, ca)), cx.fill(bc, cc, Nat.is_eq(ba, ca))) : {CU.Ent{bk, ba, bd, CatalogUnion.cu_sp_fill(bt, ct, Nat.is_eq(ba, ca)), _, CU.fill(bf, cf, Nat.is_eq(ba, ca)), CU.fill(bh, ch, Nat.is_eq(ba, ca))} == CatalogUnion.cu_sp_merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(bf, cf, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bf, cf, Nat.is_eq(ba, ca)), cx.fill(bf, cf, Nat.is_eq(ba, ca))) : {CU.Ent{bk, ba, bd, CatalogUnion.cu_sp_fill(bt, ct, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bc, cc, Nat.is_eq(ba, ca)), _, CU.fill(bh, ch, Nat.is_eq(ba, ca))} == CatalogUnion.cu_sp_merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) : CU.Ent}
      %Equal.sym(Maybe<&2, Nat>, CU.fill(bh, ch, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bh, ch, Nat.is_eq(ba, ca)), cx.fill(bh, ch, Nat.is_eq(ba, ca))) : {CU.Ent{bk, ba, bd, CatalogUnion.cu_sp_fill(bt, ct, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bc, cc, Nat.is_eq(ba, ca)), CatalogUnion.cu_sp_fill(bf, cf, Nat.is_eq(ba, ca)), _} == CatalogUnion.cu_sp_merge(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CU.Ent{ck, ca, cd, ct, cc, cf, ch}) : CU.Ent}
      {==}

def cx.with(+b: CU.Ent, m: Maybe<&2, CU.Ent>) -> {CU.with(b, m) == CatalogUnion.cu_sp_with(b, m) : CU.Ent}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      cx.merge(b, c)

def cx.bundled(bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CU.bundled(bs, cs) == CatalogUnion.cu_sp_bundled(bs, cs) : List<&2, CU.Ent>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case CU.Ent{+bk, +ba, +bd, +bt, +bc, +bf, +bh}:
          %Equal.sym(Maybe<&2, CU.Ent>, CU.find(cs, bk), CatalogUnion.cu_sp_find(cs, bk), cx.find(cs, bk)) : {CU.with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, _) <> CU.bundled(rest, cs) == CatalogUnion.cu_sp_bundled(CU.Ent{bk, ba, bd, bt, bc, bf, bh} <> rest, cs) : List<&2, CU.Ent>}
          %Equal.sym(CU.Ent, CU.with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CatalogUnion.cu_sp_find(cs, bk)), CatalogUnion.cu_sp_with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CatalogUnion.cu_sp_find(cs, bk)), cx.with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CatalogUnion.cu_sp_find(cs, bk))) : {_ <> CU.bundled(rest, cs) == CatalogUnion.cu_sp_bundled(CU.Ent{bk, ba, bd, bt, bc, bf, bh} <> rest, cs) : List<&2, CU.Ent>}
          %Equal.sym(List<&2, CU.Ent>, CU.bundled(rest, cs), CatalogUnion.cu_sp_bundled(rest, cs), cx.bundled(rest, cs)) : {CatalogUnion.cu_sp_with(CU.Ent{bk, ba, bd, bt, bc, bf, bh}, CatalogUnion.cu_sp_find(cs, bk)) <> _ == CatalogUnion.cu_sp_bundled(CU.Ent{bk, ba, bd, bt, bc, bf, bh} <> rest, cs) : List<&2, CU.Ent>}
          {==}

def cx.keep(seen: Bool, +c: CU.Ent, -rest: List<&2, CU.Ent>, -bs: List<&2, CU.Ent>, ih: {CU.extra(rest, bs) == CatalogUnion.cu_sp_extra(rest, bs) : List<&2, CU.Ent>}) -> {CU.extra.go(c <> rest, bs, seen) == CatalogUnion.cu_sp_keep(seen, c, CatalogUnion.cu_sp_extra(rest, bs)) : List<&2, CU.Ent>}:
  match seen:
    case True{}:
      ih
    case False{}:
      %Equal.sym(List<&2, CU.Ent>, CU.extra(rest, bs), CatalogUnion.cu_sp_extra(rest, bs), ih) : {c <> _ == c <> CatalogUnion.cu_sp_extra(rest, bs) : List<&2, CU.Ent>}
      {==}

def cx.extra(cs: List<&2, CU.Ent>, +bs: List<&2, CU.Ent>) -> {CU.extra(cs, bs) == CatalogUnion.cu_sp_extra(cs, bs) : List<&2, CU.Ent>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +rest:
      match c:
        case CU.Ent{+ck, +ca, +cd, +ct, +cc, +cf, +ch}:
          %Equal.sym(Bool, CU.has(bs, ck), Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_sp_find(bs, ck)), cx.has(bs, ck)) : {CU.extra.go(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs, _) == CatalogUnion.cu_sp_extra(CU.Ent{ck, ca, cd, ct, cc, cf, ch} <> rest, bs) : List<&2, CU.Ent>}
          cx.keep(Maybe.is_some(&2, CU.Ent, CatalogUnion.cu_sp_find(bs, ck)), CU.Ent{ck, ca, cd, ct, cc, cf, ch}, rest, bs, cx.extra(rest, bs))

def cx.union(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> {CU.fast(bs, cs) == CatalogUnion.cu_sp_union(bs, cs) : List<&2, CU.Ent>}:
  %Equal.sym(List<&2, CU.Ent>, CU.fast(bs, cs), CU.union(bs, cs), CatalogUnion.union_fast(bs, cs)) : {_ == CatalogUnion.cu_sp_union(bs, cs) : List<&2, CU.Ent>}
  %Equal.sym(List<&2, CU.Ent>, CU.bundled(bs, cs), CatalogUnion.cu_sp_bundled(bs, cs), cx.bundled(bs, cs)) : {List.append(&2, CU.Ent, _, CU.extra(cs, bs)) == CatalogUnion.cu_sp_union(bs, cs) : List<&2, CU.Ent>}
  %Equal.sym(List<&2, CU.Ent>, CU.extra(cs, bs), CatalogUnion.cu_sp_extra(cs, bs), cx.extra(cs, bs)) : {List.append(&2, CU.Ent, CatalogUnion.cu_sp_bundled(bs, cs), _) == CatalogUnion.cu_sp_union(bs, cs) : List<&2, CU.Ent>}
  {==}

# The codec
# ---------

def cx.opt(m: Maybe<&2, Nat>) -> {FCu.opt(m) == CatalogUnion.cu_sp_opt(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def cx.opt_of(n: Nat) -> {FCu.opt.of(n) == CatalogUnion.cu_sp_opt_of(n) : Maybe<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+v:
      {==}

def cx.ents(es: List<&2, CU.Ent>) -> {FCu.ents(es) == CatalogUnion.cu_sp_ents(es) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case CU.Ent{k, a, d, +t, +c, +f, +h}:
          %Equal.sym(Nat, FCu.opt(t), CatalogUnion.cu_sp_opt(t), cx.opt(t)) : {k <> a <> d <> _ <> FCu.opt(c) <> FCu.opt(f) <> FCu.opt(h) <> FCu.ents(rest) == CatalogUnion.cu_sp_ents(CU.Ent{k, a, d, t, c, f, h} <> rest) : List<&2, Nat>}
          %Equal.sym(Nat, FCu.opt(c), CatalogUnion.cu_sp_opt(c), cx.opt(c)) : {k <> a <> d <> CatalogUnion.cu_sp_opt(t) <> _ <> FCu.opt(f) <> FCu.opt(h) <> FCu.ents(rest) == CatalogUnion.cu_sp_ents(CU.Ent{k, a, d, t, c, f, h} <> rest) : List<&2, Nat>}
          %Equal.sym(Nat, FCu.opt(f), CatalogUnion.cu_sp_opt(f), cx.opt(f)) : {k <> a <> d <> CatalogUnion.cu_sp_opt(t) <> CatalogUnion.cu_sp_opt(c) <> _ <> FCu.opt(h) <> FCu.ents(rest) == CatalogUnion.cu_sp_ents(CU.Ent{k, a, d, t, c, f, h} <> rest) : List<&2, Nat>}
          %Equal.sym(Nat, FCu.opt(h), CatalogUnion.cu_sp_opt(h), cx.opt(h)) : {k <> a <> d <> CatalogUnion.cu_sp_opt(t) <> CatalogUnion.cu_sp_opt(c) <> CatalogUnion.cu_sp_opt(f) <> _ <> FCu.ents(rest) == CatalogUnion.cu_sp_ents(CU.Ent{k, a, d, t, c, f, h} <> rest) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, FCu.ents(rest), CatalogUnion.cu_sp_ents(rest), cx.ents(rest)) : {k <> a <> d <> CatalogUnion.cu_sp_opt(t) <> CatalogUnion.cu_sp_opt(c) <> CatalogUnion.cu_sp_opt(f) <> CatalogUnion.cu_sp_opt(h) <> _ == CatalogUnion.cu_sp_ents(CU.Ent{k, a, d, t, c, f, h} <> rest) : List<&2, Nat>}
          {==}

def cx.cons(e: CU.Ent, m: Maybe<&2, List<&2, CU.Ent>>) -> {FCu.ents.cons(e, m) == CatalogUnion.cu_sp_ents_of.cons(e, m) : Maybe<&2, List<&2, CU.Ent>>}:
  match m:
    case None{}:
      {==}
    case Some{es}:
      {==}

def cx.ents_of(ns: List<&2, Nat>) -> {FCu.ents.of(ns) == CatalogUnion.cu_sp_ents_of(ns) : Maybe<&2, List<&2, CU.Ent>>}:
  match ns:
    case Nil{}:
      {==}
    case k <> n1:
      match n1:
        case Nil{}:
          {==}
        case a <> n2:
          match n2:
            case Nil{}:
              {==}
            case d <> n3:
              match n3:
                case Nil{}:
                  {==}
                case +t <> n4:
                  match n4:
                    case Nil{}:
                      {==}
                    case +c <> n5:
                      match n5:
                        case Nil{}:
                          {==}
                        case +f <> n6:
                          match n6:
                            case Nil{}:
                              {==}
                            case +h <> +rest:
                              %Equal.sym(Maybe<&2, Nat>, FCu.opt.of(t), CatalogUnion.cu_sp_opt_of(t), cx.opt_of(t)) : {FCu.ents.cons(CU.Ent{k, a, d, _, FCu.opt.of(c), FCu.opt.of(f), FCu.opt.of(h)}, FCu.ents.of(rest)) == CatalogUnion.cu_sp_ents_of(k <> a <> d <> t <> c <> f <> h <> rest) : Maybe<&2, List<&2, CU.Ent>>}
                              %Equal.sym(Maybe<&2, Nat>, FCu.opt.of(c), CatalogUnion.cu_sp_opt_of(c), cx.opt_of(c)) : {FCu.ents.cons(CU.Ent{k, a, d, CatalogUnion.cu_sp_opt_of(t), _, FCu.opt.of(f), FCu.opt.of(h)}, FCu.ents.of(rest)) == CatalogUnion.cu_sp_ents_of(k <> a <> d <> t <> c <> f <> h <> rest) : Maybe<&2, List<&2, CU.Ent>>}
                              %Equal.sym(Maybe<&2, Nat>, FCu.opt.of(f), CatalogUnion.cu_sp_opt_of(f), cx.opt_of(f)) : {FCu.ents.cons(CU.Ent{k, a, d, CatalogUnion.cu_sp_opt_of(t), CatalogUnion.cu_sp_opt_of(c), _, FCu.opt.of(h)}, FCu.ents.of(rest)) == CatalogUnion.cu_sp_ents_of(k <> a <> d <> t <> c <> f <> h <> rest) : Maybe<&2, List<&2, CU.Ent>>}
                              %Equal.sym(Maybe<&2, Nat>, FCu.opt.of(h), CatalogUnion.cu_sp_opt_of(h), cx.opt_of(h)) : {FCu.ents.cons(CU.Ent{k, a, d, CatalogUnion.cu_sp_opt_of(t), CatalogUnion.cu_sp_opt_of(c), CatalogUnion.cu_sp_opt_of(f), _}, FCu.ents.of(rest)) == CatalogUnion.cu_sp_ents_of(k <> a <> d <> t <> c <> f <> h <> rest) : Maybe<&2, List<&2, CU.Ent>>}
                              %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(rest), CatalogUnion.cu_sp_ents_of(rest), cx.ents_of(rest)) : {FCu.ents.cons(CU.Ent{k, a, d, CatalogUnion.cu_sp_opt_of(t), CatalogUnion.cu_sp_opt_of(c), CatalogUnion.cu_sp_opt_of(f), CatalogUnion.cu_sp_opt_of(h)}, _) == CatalogUnion.cu_sp_ents_of(k <> a <> d <> t <> c <> f <> h <> rest) : Maybe<&2, List<&2, CU.Ent>>}
                              cx.cons(CU.Ent{k, a, d, CatalogUnion.cu_sp_opt_of(t), CatalogUnion.cu_sp_opt_of(c), CatalogUnion.cu_sp_opt_of(f), CatalogUnion.cu_sp_opt_of(h)}, CatalogUnion.cu_sp_ents_of(rest))

def cx.both(mb: Maybe<&2, List<&2, CU.Ent>>, mc: Maybe<&2, List<&2, CU.Ent>>, s: String) -> {FCu.get_req.both(mb, mc, s) == CatalogUnion.cu_sp_read.both(mb, mc, s) : Wr.Dec<FCu.Req>}:
  match mb mc:
    case Some{b} Some{c}:
      {==}
    case Some{b} None{}:
      {==}
    case None{} Some{c}:
      {==}
    case None{} None{}:
      {==}

def cx.read_c(+b: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {FCu.get_req.c(b, r) == CatalogUnion.cu_sp_read.c(b, r) : Wr.Dec<FCu.Req>}:
  match r:
    case Wr.Got{+c, +s}:
      %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(b), CatalogUnion.cu_sp_ents_of(b), cx.ents_of(b)) : {FCu.get_req.both(_, FCu.ents.of(c), s) == CatalogUnion.cu_sp_read.c(b, Wr.Got{c, s}) : Wr.Dec<FCu.Req>}
      %Equal.sym(Maybe<&2, List<&2, CU.Ent>>, FCu.ents.of(c), CatalogUnion.cu_sp_ents_of(c), cx.ents_of(c)) : {FCu.get_req.both(CatalogUnion.cu_sp_ents_of(b), _, s) == CatalogUnion.cu_sp_read.c(b, Wr.Got{c, s}) : Wr.Dec<FCu.Req>}
      cx.both(CatalogUnion.cu_sp_ents_of(b), CatalogUnion.cu_sp_ents_of(c), s)
    case Wr.Bad{}:
      {==}

def cx.read_b(r: Wr.Dec<List<&2, Nat>>) -> {FCu.get_req.b(r) == CatalogUnion.cu_sp_read.b(r) : Wr.Dec<FCu.Req>}:
  match r:
    case Wr.Got{b, s}:
      cx.read_c(b, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

# The entry
# ---------

def cx.end(b: Bool, q: FCu.Req) -> {FCu.reply(b, q) == CatalogUnion.cu_sp.end(b, q) : String}:
  match b:
    case True{}:
      match q:
        case FCu.Req{+bs, +cs}:
          %Equal.sym(List<&2, CU.Ent>, CU.fast(bs, cs), CatalogUnion.cu_sp_union(bs, cs), cx.union(bs, cs)) : {FCu.put_ns(FCu.ents(_), "") == CatalogUnion.cu_sp.end(True{}, FCu.Req{bs, cs}) : String}
          %Equal.sym(List<&2, Nat>, FCu.ents(CatalogUnion.cu_sp_union(bs, cs)), CatalogUnion.cu_sp_ents(CatalogUnion.cu_sp_union(bs, cs)), cx.ents(CatalogUnion.cu_sp_union(bs, cs))) : {FCu.put_ns(_, "") == CatalogUnion.cu_sp.end(True{}, FCu.Req{bs, cs}) : String}
          {==}
    case False{}:
      {==}

def cx.run(r: Wr.Dec<FCu.Req>) -> {FCu.answer(r) == CatalogUnion.cu_sp.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      cx.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def CatalogUnion.catalog_union_ffi_exact(s):
  %Equal.sym(Wr.Dec<FCu.Req>, FCu.get_req.b(Wr.get_list(~Nat, ~Wr.get_nat, s)), CatalogUnion.cu_sp_read.b(Wr.get_list(~Nat, ~Wr.get_nat, s)), cx.read_b(Wr.get_list(~Nat, ~Wr.get_nat, s))) : {FCu.answer(_) == CatalogUnion.cu_spec(s) : String}
  cx.run(CatalogUnion.cu_sp_read(s))
