# eukhe: the proof of LAW grep_run_pieces
#
# PROOF: by induction on es. An entry leaves rem less what it kept
# (kp.left) and meets as many matching files as its own class counts
# (grep_seen_counts); the matches taken off and the files added for the
# rest of es then sum with the entry's (ds.sub_sub, ds.add_swap,
# ds.add_assoc).

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA
import ./grep_keeps_pieces.bend as PKeeps
import ./grep_seen_counts.bend as PSeen

# the matching files of o <> r: o's, then r's
def rp.cons(o: Sr.Out, -r: List<&2, Sr.Out>) -> {DocSearch.ds_matched(o <> r) == Nat.add(DocSearch.ds_matched([o]), DocSearch.ds_matched(r)) : Nat}:
  match o:
    case Sr.Out{i, c, cut, pa}:
      %Equal.sym(Nat, Nat.add(DocSearch.ds_bit(DocSearch.ds_matching(c)), 0n), DocSearch.ds_bit(DocSearch.ds_matching(c)), LA.ds.add_zero(DocSearch.ds_bit(DocSearch.ds_matching(c)))) : {Nat.add(DocSearch.ds_bit(DocSearch.ds_matching(c)), DocSearch.ds_matched(r)) == Nat.add(_, DocSearch.ds_matched(r)) : Nat}
      {==}

def rp.go(es: List<&2, Sr.Ent>, +fs: List<&2, Sr.Ent>, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> {Sr.run(List.append(&2, Sr.Ent, es, fs), p, s, k, rem, n) == List.append(&2, Sr.Out, Sr.run(es, p, s, k, rem, n), Sr.run(fs, p, s, k, Nat.sub(rem, DocSearch.ds_sum(Sr.keeps(es, p, rem))), Nat.add(DocSearch.ds_matched(Sr.run(es, p, s, k, rem, n)), n))) : List<&2, Sr.Out>}:
  match es:
    case Nil{}:
      %Equal.sym(Nat, Nat.sub(rem, 0n), rem, LA.ds.sub_zero(rem)) : {Sr.run(fs, p, s, k, rem, n) == Sr.run(fs, p, s, k, _, n) : List<&2, Sr.Out>}
      {==}
    case +e <> +r:
      +l = Sr.left(e, p, rem)
      +m = Sr.seen(e, rem, n)
      +o = Sr.out(e, p, s, k, rem, n)
      +x = Sr.kept(e, p, rem)
      +a = Sr.run(r, p, s, k, l, m)
      +y = DocSearch.ds_sum(Sr.keeps(r, p, l))
      +z = DocSearch.ds_matched(a)
      +b = DocSearch.ds_matched([o])
      %Equal.sym(List<&2, Sr.Out>, Sr.run(List.append(&2, Sr.Ent, r, fs), p, s, k, l, m), List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, m))), rp.go(r, fs, p, s, k, l, m)) : {o <> _ == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(rem, Nat.add(x, y)), Nat.add(DocSearch.ds_matched(o <> a), n))) : List<&2, Sr.Out>}
      %LA.ds.sub_sub(rem, x, y) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, m))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, _, Nat.add(DocSearch.ds_matched(o <> a), n))) : List<&2, Sr.Out>}
      %PKeeps.kp.left(e, p, rem) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, m))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(_, y), Nat.add(DocSearch.ds_matched(o <> a), n))) : List<&2, Sr.Out>}
      %Equal.sym(Nat, DocSearch.ds_matched(o <> a), Nat.add(b, z), rp.cons(o, a)) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, m))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(_, n))) : List<&2, Sr.Out>}
      %Equal.sym(Nat, Nat.add(Nat.add(b, z), n), Nat.add(b, Nat.add(z, n)), LA.ds.add_assoc(b, z, n)) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, m))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), _)) : List<&2, Sr.Out>}
      %Equal.sym(Nat, m, Nat.add(b, n), DocSearch.grep_seen_counts(e, p, s, k, rem, n)) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, _))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(b, Nat.add(z, n)))) : List<&2, Sr.Out>}
      %LA.ds.add_swap(z, b, n) : {o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), Nat.add(z, Nat.add(b, n)))) == o <> List.append(&2, Sr.Out, a, Sr.run(fs, p, s, k, Nat.sub(l, y), _)) : List<&2, Sr.Out>}
      {==}

def DocSearch.grep_run_pieces(es, fs, e, p, s, k, rem, n):
  (rp.go(es, fs, p, s, k, rem, n), {==})
