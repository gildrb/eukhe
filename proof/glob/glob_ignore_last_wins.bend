# eukhe: the proof of LAW glob_ignore_last_wins
#
# PROOF: with as many codes as texts, the rule list of ps ++ [p] is the
# rule of (p, c) before the others (GI.ig.irs_snoc); each entry spelled as
# Rust spells it splits back to its path and kind (GI.ig.split), and the
# rule decides it as sp_ig_rule, else the rules after it (GI.ig.rule). No
# rule: every entry is answered not ignored.

import Base
import ../../bend/glob/queries.bend as GQuery
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL
import ./base/ignore.bend as GI

def ilw.cons(-x: Bool, -y: Bool, -xs: List<&2, Bool>, -ys: List<&2, Bool>, e: {x == y : Bool}, es: {xs == ys : List<&2, Bool>}) -> {x <> xs == y <> ys : List<&2, Bool>}:
  %e : {x <> xs == _ <> ys : List<&2, Bool>}
  %es : {x <> xs == x <> _ : List<&2, Bool>}
  {==}

def ilw.pair(-a: List<&2, Bool>, -b: List<&2, Bool>, -c: List<&2, Bool>, -d: List<&2, Bool>, ac: {a == c : List<&2, Bool>}, bd: {b == d : List<&2, Bool>}) -> {(a, b) == (c, d) : List<&2, Bool> & List<&2, Bool>}:
  %ac : {(a, b) == (_, d) : List<&2, Bool> & List<&2, Bool>}
  %bd : {(a, b) == (a, _) : List<&2, Bool> & List<&2, Bool>}
  {==}

def ilw.merge(+p: String, +c: Nat, es: List<&2, Glob.SpEnt>, +rs: List<&2, GQuery.IR>, +ok: {Glob.sp_entries_ok(es) == True{} : Bool}) -> {GQuery.ignored.go(Glob.sp_entries(es), GQuery.ir(p, c) <> rs) == Glob.sp_ig_merge(p, c, es, GQuery.ignored.go(Glob.sp_entries(es), rs)) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +r:
      match e:
        case Glob.SpEnt{+path, +dir}:
          +ok1 = GL.gl.and_l(Bool.or(dir, Bool.not(Glob.sp_ends_slash(path))), Glob.sp_entries_ok(r), ok)
          +ok2 = GL.gl.and_r(Bool.or(dir, Bool.not(Glob.sp_ends_slash(path))), Glob.sp_entries_ok(r), ok)
          sd = GQuery.split_dir(Glob.sp_entry(path, dir))
          +rs2 = {GQuery.ir(p, c) <> rs : List<&2, GQuery.IR>}
          %Equal.sym(String & Bool, sd, (path, dir), GI.ig.split(path, dir, ok1)) : {GQuery.ignored.e(rs2, _) <> GQuery.ignored.go(Glob.sp_entries(r), rs2) == Glob.sp_ig_merge(p, c, Glob.SpEnt{path, dir} <> r, GQuery.ignored.e(rs, _) <> GQuery.ignored.go(Glob.sp_entries(r), rs)) : List<&2, Bool>}
          ilw.cons(GQuery.decide(rs2, path, dir), Glob.sp_ig_pick(Glob.sp_ig_rule(p, c, path, dir), GQuery.decide(rs, path, dir)), GQuery.ignored.go(Glob.sp_entries(r), rs2), Glob.sp_ig_merge(p, c, r, GQuery.ignored.go(Glob.sp_entries(r), rs)), GI.ig.rule(p, c, path, dir, GQuery.decide(rs, path, dir)), ilw.merge(p, c, r, rs, ok2))

def ilw.e0(q: String & Bool) -> {GQuery.ignored.e(Nil{}, q) == False{} : Bool}:
  match q:
    case (a, b):
      {==}

def ilw.base(es: List<&2, String>) -> {GQuery.ignored.go(es, Nil{}) == Glob.sp_falses(es) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case e <> +r:
      ilw.cons(GQuery.ignored.e(Nil{}, GQuery.split_dir(e)), False{}, GQuery.ignored.go(r, Nil{}), Glob.sp_falses(r), ilw.e0(GQuery.split_dir(e)), ilw.base(r))

def ilw.go(+ps: List<&2, String>, +cs: List<&2, Nat>, +p: String, +c: Nat, +es: List<&2, Glob.SpEnt>, +h: {Bool.and(Nat.is_eq(List.length(&2, String, ps), List.length(&2, Nat, cs)), Glob.sp_entries_ok(es)) == True{} : Bool}) -> {(GQuery.ignored(List.append(&2, String, ps, [p]), List.append(&2, Nat, cs, [c]), Glob.sp_entries(es)), GQuery.ignored(Nil{}, Nil{}, Glob.sp_entries(es))) == (Glob.sp_ig_merge(p, c, es, GQuery.ignored(ps, cs, Glob.sp_entries(es))), Glob.sp_falses(Glob.sp_entries(es))) : List<&2, Bool> & List<&2, Bool>}:
  +h1 = GL.gl.and_l(Nat.is_eq(List.length(&2, String, ps), List.length(&2, Nat, cs)), Glob.sp_entries_ok(es), h)
  +h2 = GL.gl.and_r(Nat.is_eq(List.length(&2, String, ps), List.length(&2, Nat, cs)), Glob.sp_entries_ok(es), h)
  +ent = Glob.sp_entries(es)
  +rs = GQuery.irs(ps, cs, Nil{})
  +l1 = GQuery.ignored.go(ent, GQuery.irs(List.append(&2, String, ps, [p]), List.append(&2, Nat, cs, [c]), Nil{}))
  +m1 = GQuery.ignored.go(ent, GQuery.ir(p, c) <> rs)
  +r1 = Glob.sp_ig_merge(p, c, es, GQuery.ignored.go(ent, rs))
  ilw.pair(l1, GQuery.ignored.go(ent, Nil{}), r1, Glob.sp_falses(ent), Equal.trans(List<&2, Bool>, l1, m1, r1, Equal.cong(List<&2, GQuery.IR>, List<&2, Bool>, z => GQuery.ignored.go(ent, z), GQuery.irs(List.append(&2, String, ps, [p]), List.append(&2, Nat, cs, [c]), Nil{}), GQuery.ir(p, c) <> rs, GI.ig.irs_snoc(ps, cs, p, c, Nil{}, h1)), ilw.merge(p, c, es, rs, h2)), ilw.base(ent))

def Glob.glob_ignore_last_wins(ps, cs, p, c, es, h):
  ilw.go(ps, cs, p, c, es, h)
