# proof_sandbox: the S3 laws (docs/runtime.md) of the sandbox model in
# bend/sandbox.bend: the protocol and the copy-on-write hand-back.
#
# The protocol: one host step adds one reply and runs the frame iff it is
# accepted (`px.ids_add`, `px.ok_add`, `px.len_add`); each law follows by
# induction on the frames. The hand-back: the lookup of a path k in the new
# workspace is the merge of k when k is listed, else nothing
# (`px.read_back`), and k is a conflict iff it is listed and its merge
# clashes (`px.cl_back`). The merge of one path then decides each law
# (`px.keep_body`, `px.take_body`, `px.clash_one`, `px.real`).

import Base
import ./sandbox.bend as Sb

# Logic
# -----

def px.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def px.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : px.BD(_, A, Unit)
  Unit{}

def px.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      px.absurdF({b == True{} : Bool}, h)

def px.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def px.and_false(b: Bool) -> {False{} == Bool.and(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Numbers
# -------

def px.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      px.eq_refl(p)

def px.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      px.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      px.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, px.eq_true(p, q, h))

# b below a: a is not at most b
def px.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {False{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      px.absurdF({False{} == Nat.is_le(0n, 0n) : Bool}, h)
    case 0n 1n+q:
      px.absurdF({False{} == Nat.is_le(0n, 1n+q) : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      px.lt_nle(p, q, h)

def px.meq_refl(m: Maybe<&2, Nat>) -> {True{} == Sb.m.eq(m, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      px.eq_refl(x)

# 1. The protocol
# ---------------

def px.ids_add(g: Bool, +f: Sb.Frame, h: Sb.Host) -> {Sb.Frame.id(f) <> Sb.reply.ids(Sb.Host.replies(h)) == Sb.reply.ids(Sb.Host.replies(Sb.host.add(g, f, h))) : List<&2, Nat>}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}

def px.proto_one_reply_each(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {Sb.reply.ids(Sb.Host.replies(Sb.serve(fs, max, allowed))) == Sb.frame.ids(fs) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      %px.ids_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed)) : {_ == Sb.Frame.id(f) <> Sb.frame.ids(rest) : List<&2, Nat>}
      %px.proto_one_reply_each(rest, max, allowed) : {Sb.Frame.id(f) <> Sb.reply.ids(Sb.Host.replies(Sb.serve(rest, max, allowed))) == Sb.Frame.id(f) <> _ : List<&2, Nat>}
      {==}

# a step keeps every frame run accepted
def px.ok_add(g: Bool, +f: Sb.Frame, h: Sb.Host, +max: Nat, +allowed: List<&2, Nat>, e: {Sb.accepts(max, allowed, f) == g : Bool}, ih: {Sb.all_ok(Sb.Host.ran(h), max, allowed) == True{} : Bool}) -> {Sb.all_ok(Sb.Host.ran(Sb.host.add(g, f, h)), max, allowed) == True{} : Bool}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          px.and_t(Sb.accepts(max, allowed, f), Sb.all_ok(xs, max, allowed), e, ih)
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          ih

def px.proto_runs_only_accepted(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {Sb.all_ok(Sb.Host.ran(Sb.serve(fs, max, allowed)), max, allowed) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      px.ok_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed), max, allowed, {==}, px.proto_runs_only_accepted(rest, max, allowed))

def px.len_add(g: Bool, +f: Sb.Frame, h: Sb.Host) -> {Nat.add(Sb.one(g), List.length(&2, Sb.Frame, Sb.Host.ran(h))) == List.length(&2, Sb.Frame, Sb.Host.ran(Sb.host.add(g, f, h))) : Nat}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}

def px.proto_runs_every_accepted(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(fs, max, allowed))) == Sb.oks(fs, max, allowed) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      %px.len_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed)) : {_ == Nat.add(Sb.one(Sb.accepts(max, allowed, f)), Sb.oks(rest, max, allowed)) : Nat}
      %px.proto_runs_every_accepted(rest, max, allowed) : {Nat.add(Sb.one(Sb.accepts(max, allowed, f)), List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(rest, max, allowed)))) == Nat.add(Sb.one(Sb.accepts(max, allowed, f)), _) : Nat}
      {==}

def px.proto_rejects_oversize(+i: Nat, +l: Nat, +k: Nat, +max: Nat, +allowed: List<&2, Nat>, over: {Nat.is_lt(max, l) == True{} : Bool}) -> {Sb.serve([Sb.Frame{i, l, k}], max, allowed) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}:
  %px.lt_nle(l, max, over) : {Sb.host.add(Bool.and(_, Sb.elem(allowed, k)), Sb.Frame{i, l, k}, Sb.Host{Nil{}, Nil{}}) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}
  {==}

# 2. A copy-on-write workspace
# ----------------------------

# the merge of path k
def px.mk(+par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> Sb.One:
  Sb.merge1(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k))

def px.sel(b: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

def px.sel_none(b: Bool) -> {None{} == px.sel(b, None{}) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a file added at k is what k reads, else what follows
def px.read_hit(+k: Nat, m: Maybe<&2, Nat>, +W: List<&2, Sb.Doc>, +b: Bool, ih: {px.sel(b, m) == Sb.read(W, k) : Maybe<&2, Nat>}) -> {m == Sb.read(List.append(&2, Sb.Doc, Sb.back.file(k, m), W), k) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      %ih : {None{} == _ : Maybe<&2, Nat>}
      px.sel_none(b)
    case Some{v}:
      %px.eq_refl(k) : {Some{v} == Sb.read.go(Sb.Doc{k, v} <> W, k, _) : Maybe<&2, Nat>}
      {==}

# a file added at another path is not read
def px.read_miss(+j: Nat, m: Maybe<&2, Nat>, +W: List<&2, Sb.Doc>, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.read(W, k) == Sb.read(List.append(&2, Sb.Doc, Sb.back.file(j, m), W), k) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ne) : {Sb.read(W, k) == Sb.read.go(Sb.Doc{j, v} <> W, k, _) : Maybe<&2, Nat>}
      {==}

def px.read_hit2(+k: Nat, +o: Sb.One, x: Sb.Back, +b: Bool, ih: {px.sel(b, Sb.One.body(o)) == Sb.read(Sb.Back.ws(x), k) : Maybe<&2, Nat>}) -> {Sb.One.body(o) == Sb.read(Sb.Back.ws(Sb.back.add(k, o, x)), k) : Maybe<&2, Nat>}:
  match x:
    case Sb.Back{w, c}:
      px.read_hit(k, Sb.One.body(o), w, b, ih)

def px.read_miss2(+j: Nat, +o: Sb.One, x: Sb.Back, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.read(Sb.Back.ws(x), k) == Sb.read(Sb.Back.ws(Sb.back.add(j, o, x)), k) : Maybe<&2, Nat>}:
  match x:
    case Sb.Back{w, c}:
      px.read_miss(j, Sb.One.body(o), w, k, ne)

def px.rb_go(+j: Nat, +rest: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, c: Bool, ec: {Nat.is_eq(j, k) == c : Bool}, ih: {px.sel(Sb.elem(rest, k), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(rest, par, base, child)), k) : Maybe<&2, Nat>}) -> {px.sel(Bool.or(c, Sb.elem(rest, k)), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(j <> rest, par, base, child)), k) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      %Equal.sym(Nat, j, k, px.eq_true(j, k, ec)) : {Sb.One.body(px.mk(par, base, child, k)) == Sb.read(Sb.Back.ws(Sb.back(_ <> rest, par, base, child)), k) : Maybe<&2, Nat>}
      px.read_hit2(k, px.mk(par, base, child, k), Sb.back(rest, par, base, child), Sb.elem(rest, k), ih)
    case False{}:
      %px.read_miss2(j, px.mk(par, base, child, j), Sb.back(rest, par, base, child), k, ec) : {px.sel(Sb.elem(rest, k), Sb.One.body(px.mk(par, base, child, k))) == _ : Maybe<&2, Nat>}
      ih

# the new workspace holds at k the merge of k, if k is listed
def px.read_back(ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> {px.sel(Sb.elem(ks, k), Sb.One.body(px.mk(par, base, child, k))) == Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) : Maybe<&2, Nat>}:
  match ks:
    case Nil{}:
      {==}
    case +j <> +rest:
      px.rb_go(j, rest, par, base, child, k, Nat.is_eq(j, k), {==}, px.read_back(rest, par, base, child, k))

def px.cl_hit_go(+k: Nat, d: Bool, +cs: List<&2, Nat>, +b: Bool, ih: {Bool.and(b, d) == Sb.elem(cs, k) : Bool}) -> {d == Sb.elem(List.append(&2, Nat, Sb.back.clash(k, d), cs), k) : Bool}:
  match d:
    case True{}:
      %px.eq_refl(k) : {True{} == Bool.or(_, Sb.elem(cs, k)) : Bool}
      {==}
    case False{}:
      %ih : {False{} == _ : Bool}
      px.and_false(b)

def px.cl_miss_go(+j: Nat, d: Bool, +cs: List<&2, Nat>, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.elem(cs, k) == Sb.elem(List.append(&2, Nat, Sb.back.clash(j, d), cs), k) : Bool}:
  match d:
    case True{}:
      %Equal.sym(Bool, Nat.is_eq(j, k), False{}, ne) : {Sb.elem(cs, k) == Bool.or(_, Sb.elem(cs, k)) : Bool}
      {==}
    case False{}:
      {==}

def px.cl_hit(+k: Nat, +o: Sb.One, x: Sb.Back, +b: Bool, ih: {Bool.and(b, Sb.One.clash(o)) == Sb.elem(Sb.Back.clashes(x), k) : Bool}) -> {Sb.One.clash(o) == Sb.elem(Sb.Back.clashes(Sb.back.add(k, o, x)), k) : Bool}:
  match x:
    case Sb.Back{w, cs}:
      px.cl_hit_go(k, Sb.One.clash(o), cs, b, ih)

def px.cl_miss(+j: Nat, +o: Sb.One, x: Sb.Back, +k: Nat, ne: {Nat.is_eq(j, k) == False{} : Bool}) -> {Sb.elem(Sb.Back.clashes(x), k) == Sb.elem(Sb.Back.clashes(Sb.back.add(j, o, x)), k) : Bool}:
  match x:
    case Sb.Back{w, cs}:
      px.cl_miss_go(j, Sb.One.clash(o), cs, k, ne)

def px.cb_go(+j: Nat, +rest: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, c: Bool, ec: {Nat.is_eq(j, k) == c : Bool}, ih: {Bool.and(Sb.elem(rest, k), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(rest, par, base, child)), k) : Bool}) -> {Bool.and(Bool.or(c, Sb.elem(rest, k)), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(j <> rest, par, base, child)), k) : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, j, k, px.eq_true(j, k, ec)) : {Sb.One.clash(px.mk(par, base, child, k)) == Sb.elem(Sb.Back.clashes(Sb.back(_ <> rest, par, base, child)), k) : Bool}
      px.cl_hit(k, px.mk(par, base, child, k), Sb.back(rest, par, base, child), Sb.elem(rest, k), ih)
    case False{}:
      %px.cl_miss(j, px.mk(par, base, child, j), Sb.back(rest, par, base, child), k, ec) : {Bool.and(Sb.elem(rest, k), Sb.One.clash(px.mk(par, base, child, k))) == _ : Bool}
      ih

# k is a conflict iff it is listed and its merge clashes
def px.cl_back(ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat) -> {Bool.and(Sb.elem(ks, k), Sb.One.clash(px.mk(par, base, child, k))) == Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) : Bool}:
  match ks:
    case Nil{}:
      {==}
    case +j <> +rest:
      px.cb_go(j, rest, par, base, child, k, Nat.is_eq(j, k), {==}, px.cl_back(rest, par, base, child, k))

# The merge of one path
# ---------------------

def px.keep_body(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, calm: {Sb.m.eq(c, b) == True{} : Bool}) -> {p == Sb.One.body(Sb.merge1(p, b, c)) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Sb.m.eq(c, b), True{}, calm) : {p == Sb.One.body(Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  {==}

def px.take_body(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, moved: {Sb.m.eq(c, b) == False{} : Bool}, still: {Sb.m.eq(p, b) == True{} : Bool}) -> {c == Sb.One.body(Sb.merge1(p, b, c)) : Maybe<&2, Nat>}:
  %Equal.sym(Bool, Sb.m.eq(c, b), False{}, moved) : {c == Sb.One.body(Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.m.eq(p, b), True{}, still) : {c == Sb.One.body(Sb.merge.at(True{}, Bool.not(_), Sb.m.eq(p, c), p, c)) : Maybe<&2, Nat>}
  {==}

def px.clash_one(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, moved: {Sb.m.eq(c, b) == False{} : Bool}, also: {Sb.m.eq(p, b) == False{} : Bool}, apart: {Sb.m.eq(p, c) == False{} : Bool}) -> {Sb.One{p, True{}} == Sb.merge1(p, b, c) : Sb.One}:
  %Equal.sym(Bool, Sb.m.eq(c, b), False{}, moved) : {Sb.One{p, True{}} == Sb.merge.at(Bool.not(_), Bool.not(Sb.m.eq(p, b)), Sb.m.eq(p, c), p, c) : Sb.One}
  %Equal.sym(Bool, Sb.m.eq(p, b), False{}, also) : {Sb.One{p, True{}} == Sb.merge.at(True{}, Bool.not(_), Sb.m.eq(p, c), p, c) : Sb.One}
  %Equal.sym(Bool, Sb.m.eq(p, c), False{}, apart) : {Sb.One{p, True{}} == Sb.merge.at(True{}, True{}, _, p, c) : Sb.One}
  {==}

def px.real_go(x: Bool, y: Bool, z: Bool, +p: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, h: {Sb.One.clash(Sb.merge.at(Bool.not(x), Bool.not(y), z, p, c)) == True{} : Bool}) -> {Bool.or(Bool.or(x, y), z) == False{} : Bool}:
  match x y z:
    case True{} _ _:
      px.absurdF({Bool.or(Bool.or(True{}, y), z) == False{} : Bool}, h)
    case False{} True{} _:
      px.absurdF({Bool.or(Bool.or(False{}, True{}), z) == False{} : Bool}, h)
    case False{} False{} True{}:
      px.absurdF({Bool.or(Bool.or(False{}, False{}), True{}) == False{} : Bool}, h)
    case False{} False{} False{}:
      {==}

# a merge that clashes saw both sides change, apart
def px.real(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, h: {Sb.One.clash(Sb.merge1(p, b, c)) == True{} : Bool}) -> {Bool.or(Bool.or(Sb.m.eq(c, b), Sb.m.eq(p, b)), Sb.m.eq(p, c)) == False{} : Bool}:
  px.real_go(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), p, c, h)

# The laws
# --------

def px.cow_keeps_parent(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, calm: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == True{} : Bool}) -> {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(par, k) : Maybe<&2, Nat>}:
  %px.read_back(ks, par, base, child, k) : {_ == Sb.read(par, k) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {px.sel(_, Sb.One.body(px.mk(par, base, child, k))) == Sb.read(par, k) : Maybe<&2, Nat>}
  %px.keep_body(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), calm) : {_ == Sb.read(par, k) : Maybe<&2, Nat>}
  {==}

def px.cow_takes_child(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}, still: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == True{} : Bool}) -> {Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k) == Sb.read(child, k) : Maybe<&2, Nat>}:
  %px.read_back(ks, par, base, child, k) : {_ == Sb.read(child, k) : Maybe<&2, Nat>}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {px.sel(_, Sb.One.body(px.mk(par, base, child, k))) == Sb.read(child, k) : Maybe<&2, Nat>}
  %px.take_body(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), moved, still) : {_ == Sb.read(child, k) : Maybe<&2, Nat>}
  {==}

def px.cow_conflict_reported(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, listed: {Sb.elem(ks, k) == True{} : Bool}, moved: {Sb.m.eq(Sb.read(child, k), Sb.read(base, k)) == False{} : Bool}, also: {Sb.m.eq(Sb.read(par, k), Sb.read(base, k)) == False{} : Bool}, apart: {Sb.m.eq(Sb.read(par, k), Sb.read(child, k)) == False{} : Bool}) -> {Bool.and(Sb.m.eq(Sb.read(Sb.Back.ws(Sb.back(ks, par, base, child)), k), Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}:
  %px.read_back(ks, par, base, child, k) : {Bool.and(Sb.m.eq(_, Sb.read(par, k)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k)) == True{} : Bool}
  %px.cl_back(ks, par, base, child, k) : {Bool.and(Sb.m.eq(px.sel(Sb.elem(ks, k), Sb.One.body(px.mk(par, base, child, k))), Sb.read(par, k)), _) == True{} : Bool}
  %Equal.sym(Bool, Sb.elem(ks, k), True{}, listed) : {Bool.and(Sb.m.eq(px.sel(_, Sb.One.body(px.mk(par, base, child, k))), Sb.read(par, k)), Bool.and(_, Sb.One.clash(px.mk(par, base, child, k)))) == True{} : Bool}
  %px.clash_one(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), moved, also, apart) : {Bool.and(Sb.m.eq(Sb.One.body(_), Sb.read(par, k)), Sb.One.clash(_)) == True{} : Bool}
  %px.meq_refl(Sb.read(par, k)) : {Bool.and(_, True{}) == True{} : Bool}
  {==}

def px.cow_conflict_is_real(+ks: List<&2, Nat>, +par: List<&2, Sb.Doc>, +base: List<&2, Sb.Doc>, +child: List<&2, Sb.Doc>, +k: Nat, clash: {Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k) == True{} : Bool}) -> {Bool.or(Bool.or(Sb.m.eq(Sb.read(child, k), Sb.read(base, k)), Sb.m.eq(Sb.read(par, k), Sb.read(base, k))), Sb.m.eq(Sb.read(par, k), Sb.read(child, k))) == False{} : Bool}:
  +M = px.mk(par, base, child, k)
  +both = Equal.trans(Bool, Bool.and(Sb.elem(ks, k), Sb.One.clash(M)), Sb.elem(Sb.Back.clashes(Sb.back(ks, par, base, child)), k), True{}, px.cl_back(ks, par, base, child, k), clash)
  px.real(Sb.read(par, k), Sb.read(base, k), Sb.read(child, k), px.and_r(Sb.elem(ks, k), Sb.One.clash(M), both))
