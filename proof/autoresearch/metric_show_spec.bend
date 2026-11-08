# eukhe: the proof of LAW metric_show_spec
#
# PROOF: the printer's digit chars are the grammar's (ms.ds), its split of
# the digits is the spec's take and drop (ms.split), its count and zeros
# are the spec's (ms.len, ms.zeros), so each branch of the printer spells
# what the spec's text spells (ms.mag, ms.scaled), with the same sign
# (ms.sign).

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/entry.bend as AutoresearchEntry

def ms.ds(ds: List<&2, Nat>, +rest: String) -> {ArD.put_ds(ds, rest) == SL.spell_ds(ds, rest) : String}:
  match ds:
    case Nil{}:
      {==}
    case +d <> t:
      Equal.cong(String, String, x => SCon{ArD.dchar(d), x}, ArD.put_ds(t, rest), SL.spell_ds(t, rest), ms.ds(t, rest))

def ms.len(ds: List<&2, Nat>) -> {ArD.len(ds) == SL.dlen(ds) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> t:
      Equal.cong(Nat, Nat, x => 1n+x, ArD.len(t), SL.dlen(t), ms.len(t))

def ms.zeros(n: Nat) -> {ArD.zeros(n) == SL.zeros(n) : List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => 0n <> x, ArD.zeros(k), SL.zeros(k), ms.zeros(k))

def ms.split(n: Nat, ds: List<&2, Nat>) -> {ArD.split(n, ds) == (SL.take(n, ds), SL.drop(n, ds)) : List<&2, Nat> & List<&2, Nat>}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      match ds:
        case Nil{}:
          {==}
        case +d <> +t:
          %Equal.sym(List<&2, Nat> & List<&2, Nat>, ArD.split(k, t), (SL.take(k, t), SL.drop(k, t)), ms.split(k, t)) : {ArD.split.on(d, _) == (d <> SL.take(k, t), SL.drop(k, t)) : List<&2, Nat> & List<&2, Nat>}
          {==}

def ms.sign(neg: Bool, s: String) -> {ArD.show.sign(neg, s) == SL.spell_sign(neg, s) : String}:
  match neg:
    case True{}:
      {==}
    case False{}:
      {==}

def ms.mag(more: Bool, +ds: List<&2, Nat>, +n: Nat, +sc: Nat) -> {ArD.show.mag(more, ds, n, sc) == SL.text.point(more, ds, n, sc) : String}:
  match more:
    case True{}:
      +k = Nat.sub(n, sc)
      %Equal.sym(List<&2, Nat> & List<&2, Nat>, ArD.split(k, ds), (SL.take(k, ds), SL.drop(k, ds)), ms.split(k, ds)) : {ArD.show.parts(_) == SL.spell_ds(SL.take(k, ds), SCon{'.', SL.spell_ds(SL.drop(k, ds), "")}) : String}
      %Equal.sym(String, ArD.put_ds(SL.drop(k, ds), ""), SL.spell_ds(SL.drop(k, ds), ""), ms.ds(SL.drop(k, ds), "")) : {ArD.put_ds(SL.take(k, ds), SCon{'.', _}) == SL.spell_ds(SL.take(k, ds), SCon{'.', SL.spell_ds(SL.drop(k, ds), "")}) : String}
      ms.ds(SL.take(k, ds), SCon{'.', SL.spell_ds(SL.drop(k, ds), "")})
    case False{}:
      +k = Nat.sub(sc, n)
      %Equal.sym(String, ArD.put_ds(ds, ""), SL.spell_ds(ds, ""), ms.ds(ds, "")) : {SCon{'0', SCon{'.', ArD.put_ds(ArD.zeros(k), _)}} == SCon{'0', SCon{'.', SL.spell_ds(SL.zeros(k), SL.spell_ds(ds, ""))}} : String}
      %Equal.sym(List<&2, Nat>, ArD.zeros(k), SL.zeros(k), ms.zeros(k)) : {SCon{'0', SCon{'.', ArD.put_ds(_, SL.spell_ds(ds, ""))}} == SCon{'0', SCon{'.', SL.spell_ds(SL.zeros(k), SL.spell_ds(ds, ""))}} : String}
      Equal.cong(String, String, x => SCon{'0', SCon{'.', x}}, ArD.put_ds(SL.zeros(k), SL.spell_ds(ds, "")), SL.spell_ds(SL.zeros(k), SL.spell_ds(ds, "")), ms.ds(SL.zeros(k), SL.spell_ds(ds, "")))

def ms.scaled(sc: Nat, +ds: List<&2, Nat>) -> {ArD.show.scaled(sc, ds) == SL.text.body(sc, ds) : String}:
  match sc:
    case 0n:
      ms.ds(ds, "")
    case 1n++p:
      %Equal.sym(Nat, ArD.len(ds), SL.dlen(ds), ms.len(ds)) : {ArD.show.mag(Nat.is_lt(1n+p, _), ds, _, 1n+p) == SL.text.point(Nat.is_lt(1n+p, SL.dlen(ds)), ds, SL.dlen(ds), 1n+p) : String}
      ms.mag(Nat.is_lt(1n+p, SL.dlen(ds)), ds, SL.dlen(ds), 1n+p)

def AutoresearchEntry.metric_show_spec(d):
  match d:
    case ArD.Dec{+neg, ds, +sc}:
      match ds:
        case Nil{}:
          {==}
        case +h <> +t:
          %Equal.sym(String, ArD.show.scaled(sc, h <> t), SL.text.body(sc, h <> t), ms.scaled(sc, h <> t)) : {ArD.show.sign(neg, _) == SL.spell_sign(neg, SL.text.body(sc, h <> t)) : String}
          ms.sign(neg, SL.text.body(sc, h <> t))
