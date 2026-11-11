# eukhe: the proof of LAW work_entry_history
# The spec's ledger, mapped onto the model's state (its acts to their
# distinct acts, its blocks to the calls that wait after them), moves as
# the model moves at every event, with the same reply (wh.next); the
# entry runs the model on every spelled event (work_entry_answers). The
# spec reads a view's entries as one stream of blocks and marks the last
# entry after (wh.reads); its page keeps the entries newer than the last
# entry read before the page and every entry before them, which is the
# model's running last entry, the largest of those (wh.fresh, wh.newer_mx).

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LWork
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat

# The spec's ledger as the model's: the distinct acts of its acts, the
# calls that wait after its blocks
# ----------------------------------------------------------------------

def wh.canon(past: List<&2, Pr.Blk>) -> List<&2, Pr.Pend>:
  match past:
    case Nil{}:
      Nil{}
    case b <> t:
      match b:
        case Pr.Call{+k, f}:
          Pr.Pend{k, f} <> Pr.pend.del(wh.canon(t), k)
        case Pr.Res{k, x}:
          Pr.pend.del(wh.canon(t), k)
        case Pr.Txt{}:
          wh.canon(t)
        case Pr.Think{}:
          wh.canon(t)
        case Pr.User{}:
          wh.canon(t)
        case Pr.Sys{}:
          wh.canon(t)

# the distinct acts after reading xs, on top of s, as the model keeps them
def wh.led(xs: List<&2, Pr.Act>, +s: List<&2, Pr.Act>) -> List<&2, Pr.Act>:
  match xs:
    case Nil{}:
      s
    case +h <> t:
      wh.led(t, Pr.put(s, h))

def wh.abs(st: Work.wk.S) -> Pr.Led:
  match st:
    case Work.wk.S{a, p, r, z}:
      Pr.Led{wh.led(a, Nil{}), wh.canon(p), r, z}

def wh.lift(x: Work.wk.S & String) -> FW.St & String:
  (s, o) = x
  (FW.Live{wh.abs(s)}, o)

# Lists
# -----

def wh.app_nil(a: List<&2, Pr.Act>) -> {List.append(&2, Pr.Act, a, Nil{}) == a : List<&2, Pr.Act>}:
  match a:
    case Nil{}:
      {==}
    case h <> t:
      Equal.cong(List<&2, Pr.Act>, List<&2, Pr.Act>, y => h <> y, List.append(&2, Pr.Act, t, Nil{}), t, wh.app_nil(t))

# reading one more act adds it to the distinct acts
def wh.snoc(a: List<&2, Pr.Act>, +y: Pr.Act, +s: List<&2, Pr.Act>) -> {wh.led(List.append(&2, Pr.Act, a, [y]), s) == Pr.put(wh.led(a, s), y) : List<&2, Pr.Act>}:
  match a:
    case Nil{}:
      {==}
    case +h <> t:
      wh.snoc(t, y, Pr.put(s, h))

# The count: the model's distinct acts are the distinct numbers of the
# spec's acts (an act's number is the act: LWork.wt.num)
# ----------------------------------------------------------------------

def wh.or2(+a1: Bool, +a2: Bool, +b1: Bool, +b2: Bool, e1: {a1 == a2 : Bool}, e2: {b1 == b2 : Bool}) -> {Bool.or(a1, b1) == Bool.or(a2, b2) : Bool}:
  Equal.trans(Bool, Bool.or(a1, b1), Bool.or(a2, b1), Bool.or(a2, b2), Equal.cong(Bool, Bool, v => Bool.or(v, b1), a1, a2, e1), Equal.cong(Bool, Bool, v => Bool.or(a2, v), b1, b2, e2))

# an act is held exactly when its number is
def wh.mem(+x: Pr.Act, s: List<&2, Pr.Act>) -> {Pr.mem(Work.wk_num(x), Work.wk_nums(s)) == Pr.has(x, s) : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +t:
      wh.or2(Nat.is_eq(Work.wk_num(h), Work.wk_num(x)), Pr.Act.same(h, x), Pr.mem(Work.wk_num(x), Work.wk_nums(t)), Pr.has(x, t), LWork.wt.num(h, x), wh.mem(x, t))

def wh.put_at(b: Bool, +x: Pr.Act, +s: List<&2, Pr.Act>) -> {Work.wk_nums(Pr.put.at(b, x, s)) == Pr.add.put(b, Work.wk_num(x), Work.wk_nums(s)) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# adding an act adds its number
def wh.put(+s: List<&2, Pr.Act>, +x: Pr.Act) -> {Work.wk_nums(Pr.put(s, x)) == Pr.add(Work.wk_nums(s), Work.wk_num(x)) : List<&2, Nat>}:
  +ns = Work.wk_nums(s)
  +nx = Work.wk_num(x)
  Equal.trans(List<&2, Nat>, Work.wk_nums(Pr.put.at(Pr.has(x, s), x, s)), Pr.add.put(Pr.has(x, s), nx, ns), Pr.add.put(Pr.mem(nx, ns), nx, ns), wh.put_at(Pr.has(x, s), x, s), Equal.cong(Bool, List<&2, Nat>, v => Pr.add.put(v, nx, ns), Pr.has(x, s), Pr.mem(nx, ns), Equal.sym(Bool, Pr.mem(nx, ns), Pr.has(x, s), wh.mem(x, s))))

# the model's distinct acts, numbered, are the distinct numbers
def wh.ledn(xs: List<&2, Pr.Act>, +s: List<&2, Pr.Act>) -> {Work.wk_nums(wh.led(xs, s)) == Pr.ledger(Work.wk_nums(xs), Work.wk_nums(s)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      +ps = Pr.put(s, h)
      Equal.trans(List<&2, Nat>, Work.wk_nums(wh.led(t, ps)), Pr.ledger(Work.wk_nums(t), Work.wk_nums(ps)), Pr.ledger(Work.wk_nums(t), Pr.add(Work.wk_nums(s), Work.wk_num(h))), wh.ledn(t, ps), Equal.cong(List<&2, Nat>, List<&2, Nat>, v => Pr.ledger(Work.wk_nums(t), v), Work.wk_nums(ps), Pr.add(Work.wk_nums(s), Work.wk_num(h)), wh.put(s, h)))

def wh.len(xs: List<&2, Pr.Act>) -> {List.length(&2, Nat, Work.wk_nums(xs)) == List.length(&2, Pr.Act, xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> +t:
      Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Nat, Work.wk_nums(t)), List.length(&2, Pr.Act, t), wh.len(t))

# the spec's work is the model's count
def wh.count(+a: List<&2, Pr.Act>) -> {Pr.work(Work.wk_nums(a)) == List.length(&2, Pr.Act, wh.led(a, Nil{})) : Nat}:
  +l = wh.led(a, Nil{})
  Equal.trans(Nat, List.length(&2, Nat, Pr.ledger(Work.wk_nums(a), Nil{})), List.length(&2, Nat, Work.wk_nums(l)), List.length(&2, Pr.Act, l), Equal.cong(List<&2, Nat>, Nat, v => List.length(&2, Nat, v), Pr.ledger(Work.wk_nums(a), Nil{}), Work.wk_nums(l), Equal.sym(List<&2, Nat>, Work.wk_nums(l), Pr.ledger(Work.wk_nums(a), Nil{}), wh.ledn(a, Nil{}))), wh.len(l))

# Waiting calls
# -------------

def wh.pick_none(c: Bool) -> {Work.wk_pick(c, None{}, None{}) == None{} : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def wh.pick_hit(c: Bool, f: Nat, y: Maybe<&2, Nat>) -> {Work.wk_pick(c, None{}, Pr.pend.hit(c, f, y)) == Work.wk_pick(c, None{}, y) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def wh.pick_call(c: Bool, f: Nat, y: Maybe<&2, Nat>) -> {Work.wk_pick(c, Some{f}, y) == Pr.pend.hit(c, f, Work.wk_pick(c, None{}, y)) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a waiting call of key i, i not j, stays after the calls of key j go
def wh.del_miss(d: Bool, +i: Nat, +j: Nat, +k: Nat, g: Nat, y: Maybe<&2, Nat>, eij: {Nat.is_eq(i, j) == False{} : Bool}, ejk: {Nat.is_eq(j, k) == d : Bool}) -> {Work.wk_pick(d, None{}, Pr.pend.hit(Nat.is_eq(i, k), g, y)) == Pr.pend.hit(Nat.is_eq(i, k), g, Work.wk_pick(d, None{}, y)) : Maybe<&2, Nat>}:
  match d:
    case True{}:
      %LLogicNat.cb_nat_eq(j, k, ejk) : {None{} == Pr.pend.hit(Nat.is_eq(i, _), g, None{}) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_eq(i, j), False{}, eij) : {None{} == Pr.pend.hit(_, g, None{}) : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

def wh.del_at(c: Bool, +i: Nat, +j: Nat, +k: Nat, +g: Nat, +t: List<&2, Pr.Pend>, eij: {Nat.is_eq(i, j) == c : Bool}, ih: {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.get(t, k)) == Pr.pend.get(Pr.pend.del(t, j), k) : Maybe<&2, Nat>}) -> {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.hit(Nat.is_eq(i, k), g, Pr.pend.get(t, k))) == Pr.pend.get(Pr.pend.del.at(c, i, g, Pr.pend.del(t, j)), k) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      %ih : {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.hit(Nat.is_eq(i, k), g, Pr.pend.get(t, k))) == _ : Maybe<&2, Nat>}
      %Equal.sym(Nat, i, j, LLogicNat.cb_nat_eq(i, j, eij)) : {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.hit(Nat.is_eq(_, k), g, Pr.pend.get(t, k))) == Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.get(t, k)) : Maybe<&2, Nat>}
      wh.pick_hit(Nat.is_eq(j, k), g, Pr.pend.get(t, k))
    case False{}:
      %ih : {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.hit(Nat.is_eq(i, k), g, Pr.pend.get(t, k))) == Pr.pend.hit(Nat.is_eq(i, k), g, _) : Maybe<&2, Nat>}
      wh.del_miss(Nat.is_eq(j, k), i, j, k, g, Pr.pend.get(t, k), eij, {==})

# after the calls of key j go, a call of key k waits when k is not j and
# it waited before
def wh.del_get(cs: List<&2, Pr.Pend>, +j: Nat, +k: Nat) -> {Work.wk_pick(Nat.is_eq(j, k), None{}, Pr.pend.get(cs, k)) == Pr.pend.get(Pr.pend.del(cs, j), k) : Maybe<&2, Nat>}:
  match cs:
    case Nil{}:
      wh.pick_none(Nat.is_eq(j, k))
    case c <> +t:
      match c:
        case Pr.Pend{+i, g}:
          wh.del_at(Nat.is_eq(i, j), i, j, k, g, t, {==}, wh.del_get(t, j, k))

# the spec's waiting call of key k is the model's
def wh.look(p: List<&2, Pr.Blk>, +k: Nat) -> {Work.wk_look(p, k) == Pr.pend.get(wh.canon(p), k) : Maybe<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case b <> +t:
      match b:
        case Pr.Call{+j, f}:
          %wh.del_get(wh.canon(t), j, k) : {Work.wk_pick(Nat.is_eq(j, k), Some{f}, Work.wk_look(t, k)) == Pr.pend.hit(Nat.is_eq(j, k), f, _) : Maybe<&2, Nat>}
          %wh.look(t, k) : {Work.wk_pick(Nat.is_eq(j, k), Some{f}, Work.wk_look(t, k)) == Pr.pend.hit(Nat.is_eq(j, k), f, Work.wk_pick(Nat.is_eq(j, k), None{}, _)) : Maybe<&2, Nat>}
          wh.pick_call(Nat.is_eq(j, k), f, Work.wk_look(t, k))
        case Pr.Res{+j, x}:
          %wh.del_get(wh.canon(t), j, k) : {Work.wk_pick(Nat.is_eq(j, k), None{}, Work.wk_look(t, k)) == _ : Maybe<&2, Nat>}
          %wh.look(t, k) : {Work.wk_pick(Nat.is_eq(j, k), None{}, Work.wk_look(t, k)) == Work.wk_pick(Nat.is_eq(j, k), None{}, _) : Maybe<&2, Nat>}
          {==}
        case Pr.Txt{}:
          wh.look(t, k)
        case Pr.Think{}:
          wh.look(t, k)
        case Pr.User{}:
          wh.look(t, k)
        case Pr.Sys{}:
          wh.look(t, k)

# Blocks, entries, pages
# ----------------------

def wh.nil_led(a: List<&2, Pr.Act>, c: List<&2, Pr.Pend>, r: Nat, z: Maybe<&2, Nat>) -> {Pr.Led{wh.led(List.append(&2, Pr.Act, a, Nil{}), Nil{}), c, r, z} == Pr.Led{wh.led(a, Nil{}), c, r, z} : Pr.Led}:
  Equal.cong(List<&2, Pr.Act>, Pr.Led, y => Pr.Led{wh.led(y, Nil{}), c, r, z}, List.append(&2, Pr.Act, a, Nil{}), a, wh.app_nil(a))

def wh.blk(st: Work.wk.S, b: Pr.Blk) -> {wh.abs(Work.wk_blk(st, b)) == Pr.Led.blk(wh.abs(st), b) : Pr.Led}:
  match st:
    case Work.wk.S{+a, +p, +r, +z}:
      match b:
        case Pr.Call{+k, +f}:
          wh.nil_led(a, Pr.Pend{k, f} <> Pr.pend.del(wh.canon(p), k), r, z)
        case Pr.Res{+k, +x}:
          %wh.look(p, k) : {Pr.Led{wh.led(List.append(&2, Pr.Act, a, [Pr.ARes{Work.wk_look(p, k), x}]), Nil{}), Pr.pend.del(wh.canon(p), k), r, z} == Pr.Led{Pr.put(wh.led(a, Nil{}), Pr.ARes{_, x}), Pr.pend.del(wh.canon(p), k), r, z} : Pr.Led}
          %wh.snoc(a, Pr.ARes{Work.wk_look(p, k), x}, Nil{}) : {Pr.Led{wh.led(List.append(&2, Pr.Act, a, [Pr.ARes{Work.wk_look(p, k), x}]), Nil{}), Pr.pend.del(wh.canon(p), k), r, z} == Pr.Led{_, Pr.pend.del(wh.canon(p), k), r, z} : Pr.Led}
          {==}
        case Pr.Txt{}:
          wh.nil_led(a, wh.canon(p), r, z)
        case Pr.Think{}:
          wh.nil_led(a, wh.canon(p), r, z)
        case Pr.User{}:
          wh.nil_led(a, wh.canon(p), r, z)
        case Pr.Sys{}:
          wh.nil_led(a, wh.canon(p), r, z)

def wh.blks(bs: List<&2, Pr.Blk>, +st: Work.wk.S) -> {wh.abs(Work.wk_blks(bs, st)) == Pr.Led.blks(bs, wh.abs(st)) : Pr.Led}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      %wh.blk(st, b) : {wh.abs(Work.wk_blks(t, Work.wk_blk(st, b))) == Pr.Led.blks(t, _) : Pr.Led}
      wh.blks(t, Work.wk_blk(st, b))

# Reading entries: one stream of blocks, then the last entry
# ----------------------------------------------------------

def wh.mark_blk(st: Work.wk.S, +b: Pr.Blk, z: Maybe<&2, Nat>) -> {Work.wk_blk(Work.wk_mark(st, z), b) == Work.wk_mark(Work.wk_blk(st, b), z) : Work.wk.S}:
  match st:
    case Work.wk.S{a, p, r, y}:
      {==}

# blocks never move the last entry read
def wh.mark_blks(bs: List<&2, Pr.Blk>, +st: Work.wk.S, +z: Maybe<&2, Nat>) -> {Work.wk_blks(bs, Work.wk_mark(st, z)) == Work.wk_mark(Work.wk_blks(bs, st), z) : Work.wk.S}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      %Equal.sym(Work.wk.S, Work.wk_blk(Work.wk_mark(st, z), b), Work.wk_mark(Work.wk_blk(st, b), z), wh.mark_blk(st, b, z)) : {Work.wk_blks(t, _) == Work.wk_mark(Work.wk_blks(t, Work.wk_blk(st, b)), z) : Work.wk.S}
      wh.mark_blks(t, Work.wk_blk(st, b), z)

def wh.blks_app(xs: List<&2, Pr.Blk>, ys: List<&2, Pr.Blk>, st: Work.wk.S) -> {Work.wk_blks(List.append(&2, Pr.Blk, xs, ys), st) == Work.wk_blks(ys, Work.wk_blks(xs, st)) : Work.wk.S}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      wh.blks_app(t, ys, Work.wk_blk(st, x))

def wh.last_blk(st: Work.wk.S, b: Pr.Blk) -> {Work.wk_last(Work.wk_blk(st, b)) == Work.wk_last(st) : Maybe<&2, Nat>}:
  match st:
    case Work.wk.S{a, p, r, z}:
      {==}

def wh.last_blks(bs: List<&2, Pr.Blk>, +st: Work.wk.S) -> {Work.wk_last(Work.wk_blks(bs, st)) == Work.wk_last(st) : Maybe<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      Equal.trans(Maybe<&2, Nat>, Work.wk_last(Work.wk_blks(t, Work.wk_blk(st, b))), Work.wk_last(Work.wk_blk(st, b)), Work.wk_last(st), wh.last_blks(t, Work.wk_blk(st, b)), wh.last_blk(st, b))

def wh.last_mark(st: Work.wk.S, z: Maybe<&2, Nat>) -> {Work.wk_last(Work.wk_mark(st, z)) == z : Maybe<&2, Nat>}:
  match st:
    case Work.wk.S{a, p, r, y}:
      {==}

def wh.mark_mark(st: Work.wk.S, y: Maybe<&2, Nat>, z: Maybe<&2, Nat>) -> {Work.wk_mark(Work.wk_mark(st, y), z) == Work.wk_mark(st, z) : Work.wk.S}:
  match st:
    case Work.wk.S{a, p, r, x}:
      {==}

def wh.reads_nil(st: Work.wk.S) -> {wh.abs(Work.wk_reads(Nil{}, st)) == wh.abs(st) : Pr.Led}:
  match st:
    case Work.wk.S{a, p, r, z}:
      {==}

# an entry first: its blocks, it the last entry read, then the rest
def wh.reads_cons(+i: Nat, +bs: List<&2, Pr.Blk>, +t: List<&2, Pr.Ent>, +st: Work.wk.S) -> {Work.wk_reads(Pr.Ent{i, bs} <> t, st) == Work.wk_reads(t, Work.wk_blks(bs, Work.wk_mark(st, Some{i}))) : Work.wk.S}:
  +x = Work.wk_blks(bs, Work.wk_mark(st, Some{i}))
  +ab = List.append(&2, Pr.Blk, bs, Work.wk_flat(t))
  +y = Work.wk_blks(ab, st)
  +f = Work.wk_final(t, Some{i})
  +e1 = Equal.trans(Maybe<&2, Nat>, Work.wk_last(x), Work.wk_last(Work.wk_mark(st, Some{i})), Some{i}, wh.last_blks(bs, Work.wk_mark(st, Some{i})), wh.last_mark(st, Some{i}))
  +e2 = Equal.trans(Work.wk.S, Work.wk_blks(Work.wk_flat(t), x), Work.wk_blks(ab, Work.wk_mark(st, Some{i})), Work.wk_mark(y, Some{i}),
    Equal.sym(Work.wk.S, Work.wk_blks(ab, Work.wk_mark(st, Some{i})), Work.wk_blks(Work.wk_flat(t), x), wh.blks_app(bs, Work.wk_flat(t), Work.wk_mark(st, Some{i}))),
    wh.mark_blks(ab, st, Some{i}))
  +c1 = Equal.cong(Work.wk.S, Work.wk.S, v => Work.wk_mark(v, Work.wk_final(t, Work.wk_last(x))), Work.wk_blks(Work.wk_flat(t), x), Work.wk_mark(y, Some{i}), e2)
  +c2 = Equal.cong(Maybe<&2, Nat>, Work.wk.S, v => Work.wk_mark(Work.wk_mark(y, Some{i}), Work.wk_final(t, v)), Work.wk_last(x), Some{i}, e1)
  +c3 = wh.mark_mark(y, Some{i}, f)
  Equal.sym(Work.wk.S, Work.wk_reads(t, x), Work.wk_mark(y, f),
    Equal.trans(Work.wk.S, Work.wk_reads(t, x), Work.wk_mark(Work.wk_mark(y, Some{i}), Work.wk_final(t, Work.wk_last(x))), Work.wk_mark(y, f), c1,
      Equal.trans(Work.wk.S, Work.wk_mark(Work.wk_mark(y, Some{i}), Work.wk_final(t, Work.wk_last(x))), Work.wk_mark(Work.wk_mark(y, Some{i}), f), Work.wk_mark(y, f), c2, c3)))

def wh.reads_ent(+i: Nat, +bs: List<&2, Pr.Blk>, +t: List<&2, Pr.Ent>, st: Work.wk.S, ih: {wh.abs(Work.wk_reads(t, Work.wk_blks(bs, Work.wk_mark(st, Some{i})))) == Pr.Led.ents(t, wh.abs(Work.wk_blks(bs, Work.wk_mark(st, Some{i})))) : Pr.Led}) -> {wh.abs(Work.wk_reads(Pr.Ent{i, bs} <> t, st)) == Pr.Led.ents(Pr.Ent{i, bs} <> t, wh.abs(st)) : Pr.Led}:
  match st:
    case Work.wk.S{+a, +p, +r, +z}:
      +s0 = {Work.wk.S{a, p, r, z} : Work.wk.S}
      +s1 = {Work.wk.S{a, p, r, Some{i}} : Work.wk.S}
      +x = Work.wk_blks(bs, s1)
      +eab = Equal.cong(Work.wk.S, Pr.Led, v => wh.abs(v), Work.wk_reads(Pr.Ent{i, bs} <> t, s0), Work.wk_reads(t, x), wh.reads_cons(i, bs, t, s0))
      +ecd = Equal.cong(Pr.Led, Pr.Led, v => Pr.Led.ents(t, v), wh.abs(x), Pr.Led.blks(bs, wh.abs(s1)), wh.blks(bs, s1))
      Equal.trans(Pr.Led, wh.abs(Work.wk_reads(Pr.Ent{i, bs} <> t, s0)), wh.abs(Work.wk_reads(t, x)), Pr.Led.ents(t, Pr.Led.blks(bs, wh.abs(s1))), eab,
        Equal.trans(Pr.Led, wh.abs(Work.wk_reads(t, x)), Pr.Led.ents(t, wh.abs(x)), Pr.Led.ents(t, Pr.Led.blks(bs, wh.abs(s1))), ih, ecd))

# reading entries moves the model as the spec reads their blocks as one
# stream
def wh.reads(es: List<&2, Pr.Ent>, +st: Work.wk.S) -> {wh.abs(Work.wk_reads(es, st)) == Pr.Led.ents(es, wh.abs(st)) : Pr.Led}:
  match es:
    case Nil{}:
      wh.reads_nil(st)
    case e <> +t:
      match e:
        case Pr.Ent{+i, +bs}:
          wh.reads_ent(i, bs, t, st, wh.reads(t, Work.wk_blks(bs, Work.wk_mark(st, Some{i}))))

# Pages: the newest of the last entry read and the entries before
# ---------------------------------------------------------------

def wh.mx1.pick(b: Bool, x: Nat, y: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      Some{y}

# the larger of the id m (when there is one) and x
def wh.mx1(m: Maybe<&2, Nat>, +x: Nat) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      Some{x}
    case Some{+y}:
      wh.mx1.pick(Nat.is_lt(y, x), x, y)

# the largest of z and the ids
def wh.mx(ids: List<&2, Nat>, z: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match ids:
    case Nil{}:
      z
    case x <> t:
      wh.mx1(wh.mx(t, z), x)

def wh.and_f(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wh.and3(a: Bool, b: Bool, x: Bool) -> {Bool.and(Bool.and(a, b), x) == Bool.and(a, Bool.and(x, b)) : Bool}:
  match a b x:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

# not a < b: b <= a
def wh.nlt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.pt.absurd({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      wh.nlt_le(p, q, h)

# y < x: x < i exactly when y < i and x < i
def wh.n1t(+y: Nat, +x: Nat, +i: Nat, d: Bool, ed: {Nat.is_lt(x, i) == d : Bool}, yx: {Nat.is_lt(y, x) == True{} : Bool}) -> {d == Bool.and(Nat.is_lt(y, i), d) : Bool}:
  match d:
    case True{}:
      +yi = LNat.tc.lt_le(y, x, i, yx, LNat.tc.lt_asym(x, i, ed))
      %Equal.sym(Bool, Nat.is_lt(y, i), True{}, yi) : {True{} == Bool.and(_, True{}) : Bool}
      {==}
    case False{}:
      Equal.sym(Bool, Bool.and(Nat.is_lt(y, i), False{}), False{}, wh.and_f(Nat.is_lt(y, i)))

# x <= y: y < i exactly when y < i and x < i
def wh.n1f(+y: Nat, +x: Nat, +i: Nat, e: Bool, ee: {Nat.is_lt(y, i) == e : Bool}, yx: {Nat.is_lt(y, x) == False{} : Bool}) -> {e == Bool.and(e, Nat.is_lt(x, i)) : Bool}:
  match e:
    case True{}:
      +xi = LNat.pc.le_lt_trans(x, y, i, wh.nlt_le(y, x, yx), ee)
      %Equal.sym(Bool, Nat.is_lt(x, i), True{}, xi) : {True{} == Bool.and(True{}, _) : Bool}
      {==}
    case False{}:
      {==}

def wh.n1(c: Bool, +y: Nat, +x: Nat, +i: Nat, ec: {Nat.is_lt(y, x) == c : Bool}) -> {Pr.newer(wh.mx1.pick(c, x, y), i) == Bool.and(Nat.is_lt(y, i), Nat.is_lt(x, i)) : Bool}:
  match c:
    case True{}:
      wh.n1t(y, x, i, Nat.is_lt(x, i), {==}, ec)
    case False{}:
      wh.n1f(y, x, i, Nat.is_lt(y, i), {==}, ec)

# an id is newer than the larger of m and x exactly when newer than both
def wh.newer_mx1(m: Maybe<&2, Nat>, +x: Nat, +i: Nat) -> {Pr.newer(wh.mx1(m, x), i) == Bool.and(Pr.newer(m, i), Nat.is_lt(x, i)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+y}:
      wh.n1(Nat.is_lt(y, x), y, x, i, {==})

def wh.newer_after(+z0: Maybe<&2, Nat>, +i: Nat) -> {Pr.newer(z0, i) == Bool.and(Work.wk_after(z0, i), True{}) : Bool}:
  match z0:
    case None{}:
      {==}
    case Some{+x}:
      Equal.sym(Bool, Bool.and(Nat.is_lt(x, i), True{}), Nat.is_lt(x, i), LWork.wt.and_true(Nat.is_lt(x, i)))

# an id is newer than the largest of z0 and the ids exactly when it is
# newer than z0 and above every id: the spec's page test is the model's
def wh.newer_mx(ids: List<&2, Nat>, +z0: Maybe<&2, Nat>, +i: Nat) -> {Pr.newer(wh.mx(ids, z0), i) == Bool.and(Work.wk_after(z0, i), Work.wk_below(ids, i)) : Bool}:
  match ids:
    case Nil{}:
      wh.newer_after(z0, i)
    case +x <> +t:
      +m = wh.mx(t, z0)
      +A = Work.wk_after(z0, i)
      +B = Work.wk_below(t, i)
      +X = Nat.is_lt(x, i)
      Equal.trans(Bool, Pr.newer(wh.mx1(m, x), i), Bool.and(Pr.newer(m, i), X), Bool.and(A, Bool.and(X, B)),
        wh.newer_mx1(m, x, i),
        Equal.trans(Bool, Bool.and(Pr.newer(m, i), X), Bool.and(Bool.and(A, B), X), Bool.and(A, Bool.and(X, B)),
          Equal.cong(Bool, Bool, v => Bool.and(v, X), Pr.newer(m, i), Bool.and(A, B), wh.newer_mx(t, z0, i)),
          wh.and3(A, B, X)))

def wh.mx1_new(m: Maybe<&2, Nat>, +i: Nat, h: {Pr.newer(m, i) == True{} : Bool}) -> {wh.mx1(m, i) == Some{i} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+y}:
      %Equal.sym(Bool, Nat.is_lt(y, i), True{}, h) : {wh.mx1.pick(_, i, y) == Some{i} : Maybe<&2, Nat>}
      {==}

def wh.mx1_old(m: Maybe<&2, Nat>, +i: Nat, h: {Pr.newer(m, i) == False{} : Bool}) -> {wh.mx1(m, i) == m : Maybe<&2, Nat>}:
  match m:
    case None{}:
      LLogicLogic.pt.absurd({wh.mx1(None{}, i) == None{} : Maybe<&2, Nat>}, h)
    case Some{+y}:
      %Equal.sym(Bool, Nat.is_lt(y, i), False{}, h) : {wh.mx1.pick(_, i, y) == Some{y} : Maybe<&2, Nat>}
      {==}

def wh.blk_lastL(l: Pr.Led, b: Pr.Blk) -> {Pr.Led.last(Pr.Led.blk(l, b)) == Pr.Led.last(l) : Maybe<&2, Nat>}:
  match l:
    case Pr.Led{s, +cs, r, z}:
      match b:
        case Pr.Call{+k, f}:
          {==}
        case Pr.Res{+k, x}:
          {==}
        case Pr.Txt{}:
          {==}
        case Pr.Think{}:
          {==}
        case Pr.User{}:
          {==}
        case Pr.Sys{}:
          {==}

def wh.blks_lastL(bs: List<&2, Pr.Blk>, +l: Pr.Led) -> {Pr.Led.last(Pr.Led.blks(bs, l)) == Pr.Led.last(l) : Maybe<&2, Nat>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> +t:
      Equal.trans(Maybe<&2, Nat>, Pr.Led.last(Pr.Led.blks(t, Pr.Led.blk(l, b))), Pr.Led.last(Pr.Led.blk(l, b)), Pr.Led.last(l), wh.blks_lastL(t, Pr.Led.blk(l, b)), wh.blk_lastL(l, b))

# an entry read is the last entry read
def wh.ent_last(l: Pr.Led, +i: Nat, +bs: List<&2, Pr.Blk>) -> {Pr.Led.last(Pr.Led.ent(l, Pr.Ent{i, bs})) == Some{i} : Maybe<&2, Nat>}:
  match l:
    case Pr.Led{s, c, r, z}:
      wh.blks_lastL(bs, Pr.Led{s, c, r, Some{i}})

# the spec's entries of a page from one entry whose test is b: that entry,
# then F, read from l, as the model reads F after its step at that entry
def wh.fresh.s2(b: Bool, e: Pr.Ent, F: List<&2, Pr.Ent>, l: Pr.Led) -> {Pr.Led.ents(Work.wk_fresh.at(b, e, F), l) == Pr.Led.ents(F, Pr.Led.page.at(b, l, e)) : Pr.Led}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# after that step, the model's last entry read is the largest of z0, the
# ids and the entry's id
def wh.fresh.s3(b: Bool, +i: Nat, +bs: List<&2, Pr.Blk>, +l: Pr.Led, +z0: Maybe<&2, Nat>, +ids: List<&2, Nat>,
  +inv: {Pr.Led.last(l) == wh.mx(ids, z0) : Maybe<&2, Nat>}, en: {Pr.newer(Pr.Led.last(l), i) == b : Bool}) ->
  {Pr.Led.last(Pr.Led.page.at(b, l, Pr.Ent{i, bs})) == wh.mx(i <> ids, z0) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      +m = wh.mx(ids, z0)
      +hn = Equal.trans(Bool, Pr.newer(m, i), Pr.newer(Pr.Led.last(l), i), True{}, Equal.cong(Maybe<&2, Nat>, Bool, v => Pr.newer(v, i), m, Pr.Led.last(l), Equal.sym(Maybe<&2, Nat>, Pr.Led.last(l), m, inv)), en)
      Equal.trans(Maybe<&2, Nat>, Pr.Led.last(Pr.Led.ent(l, Pr.Ent{i, bs})), Some{i}, wh.mx1(m, i), wh.ent_last(l, i, bs), Equal.sym(Maybe<&2, Nat>, wh.mx1(m, i), Some{i}, wh.mx1_new(m, i, hn)))
    case False{}:
      +m = wh.mx(ids, z0)
      +hf = Equal.trans(Bool, Pr.newer(m, i), Pr.newer(Pr.Led.last(l), i), False{}, Equal.cong(Maybe<&2, Nat>, Bool, v => Pr.newer(v, i), m, Pr.Led.last(l), Equal.sym(Maybe<&2, Nat>, Pr.Led.last(l), m, inv)), en)
      Equal.trans(Maybe<&2, Nat>, Pr.Led.last(l), m, wh.mx1(m, i), inv, Equal.sym(Maybe<&2, Nat>, wh.mx1(m, i), m, wh.mx1_old(m, i, hf)))

# the model's page, from a ledger whose last entry read is the largest of
# z0 and the ids, reads the entries the spec keeps
def wh.fresh(es: List<&2, Pr.Ent>, +l: Pr.Led, +z0: Maybe<&2, Nat>, +ids: List<&2, Nat>, +inv: {Pr.Led.last(l) == wh.mx(ids, z0) : Maybe<&2, Nat>}) -> {Pr.Led.page(es, l) == Pr.Led.ents(Work.wk_fresh(es, z0, ids), l) : Pr.Led}:
  match es:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Pr.Ent{+i, +bs}:
          +E = {Pr.Ent{i, bs} : Pr.Ent}
          +c = Bool.and(Work.wk_after(z0, i), Work.wk_below(ids, i))
          +F = Work.wk_fresh(t, z0, i <> ids)
          +en = Equal.trans(Bool, Pr.newer(Pr.Led.last(l), i), Pr.newer(wh.mx(ids, z0), i), c, Equal.cong(Maybe<&2, Nat>, Bool, v => Pr.newer(v, i), Pr.Led.last(l), wh.mx(ids, z0), inv), wh.newer_mx(ids, z0, i))
          +L2 = Pr.Led.page.at(c, l, E)
          +s1 = Equal.cong(Bool, Pr.Led, v => Pr.Led.page.at(v, l, E), Pr.newer(Pr.Led.last(l), i), c, en)
          +s3 = wh.fresh.s3(c, i, bs, l, z0, ids, inv, en)
          Equal.trans(Pr.Led, Pr.Led.page(t, Pr.Led.page.at(Pr.newer(Pr.Led.last(l), i), l, E)), Pr.Led.page(t, L2), Pr.Led.ents(Work.wk_fresh.at(c, E, F), l),
            Equal.cong(Pr.Led, Pr.Led, v => Pr.Led.page(t, v), Pr.Led.page.at(Pr.newer(Pr.Led.last(l), i), l, E), L2, s1),
            Equal.trans(Pr.Led, Pr.Led.page(t, L2), Pr.Led.ents(F, L2), Pr.Led.ents(Work.wk_fresh.at(c, E, F), l), wh.fresh(t, L2, z0, i <> ids, s3),
              Equal.sym(Pr.Led, Pr.Led.ents(Work.wk_fresh.at(c, E, F), l), Pr.Led.ents(F, L2), wh.fresh.s2(c, E, F, l))))

# Events
# ------

def wh.done(s: Work.wk.S) -> {wh.lift(Work.wk_done(s)) == Work.wk_spell_step(Pr.Led.done(wh.abs(s))) : FW.St & String}:
  match s:
    case Work.wk.S{+a, +p, +r, +z}:
      +l = {Pr.Led{wh.led(a, Nil{}), wh.canon(p), r, z} : Pr.Led}
      Equal.cong(Nat, FW.St & String, n => (FW.Live{l}, Work.wk_spell_out(Pr.Read{n, r, z})), Pr.work(Work.wk_nums(a)), List.length(&2, Pr.Act, wh.led(a, Nil{})), wh.count(a))

def wh.seen(s: Work.wk.S, n: Nat) -> {wh.abs(Work.wk_seen(s, n)) == Pr.Led.seen(wh.abs(s), n) : Pr.Led}:
  match s:
    case Work.wk.S{a, p, r, z}:
      {==}

def wh.holds(r: Nat, at: Maybe<&2, Nat>, z: Maybe<&2, Nat>) -> {Work.wk_holds(r, at, z) == Pr.kept(r, at, z) : Bool}:
  match r:
    case 0n:
      {==}
    case 1n+q:
      match at:
        case None{}:
          match z:
            case None{}:
              {==}
            case Some{y}:
              {==}
        case Some{x}:
          match z:
            case None{}:
              {==}
            case Some{y}:
              {==}

def wh.view(b: Bool, +es: List<&2, Pr.Ent>, +st: Work.wk.S) -> {wh.lift(Work.wk_view(b, es, st)) == Work.wk_spell_step(Pr.Led.view.at(b, es, wh.abs(st))) : FW.St & String}:
  match b:
    case True{}:
      +n = List.length(&2, Pr.Ent, es)
      %wh.reads(es, st) : {wh.lift(Work.wk_done(Work.wk_seen(Work.wk_reads(es, st), n))) == Work.wk_spell_step(Pr.Led.done(Pr.Led.seen(_, n))) : FW.St & String}
      %wh.seen(Work.wk_reads(es, st), n) : {wh.lift(Work.wk_done(Work.wk_seen(Work.wk_reads(es, st), n))) == Work.wk_spell_step(Pr.Led.done(_)) : FW.St & String}
      wh.done(Work.wk_seen(Work.wk_reads(es, st), n))
    case False{}:
      {==}

# one event moves the spec's ledger as it moves the model's, with the
# same reply
def wh.next(st: Work.wk.S, e: Pr.Ev) -> {wh.lift(Work.wk_next(st, e)) == Work.wk_spell_step(Pr.next(wh.abs(st), e)) : FW.St & String}:
  match st:
    case Work.wk.S{+a, +p, +r, +z}:
      match e:
        case Pr.View{+at, +es}:
          %wh.holds(r, at, z) : {wh.lift(Work.wk_view(Work.wk_holds(r, at, z), es, Work.wk.S{a, p, r, z})) == Work.wk_spell_step(Pr.Led.view.at(_, es, wh.abs(Work.wk.S{a, p, r, z}))) : FW.St & String}
          wh.view(Work.wk_holds(r, at, z), es, Work.wk.S{a, p, r, z})
        case Pr.Page{+es}:
          +s0 = {Work.wk.S{a, p, r, z} : Work.wk.S}
          +F = Work.wk_fresh(es, z, Nil{})
          +e1 = Equal.trans(Pr.Led, wh.abs(Work.wk_reads(F, s0)), Pr.Led.ents(F, wh.abs(s0)), Pr.Led.page(es, wh.abs(s0)), wh.reads(F, s0),
            Equal.sym(Pr.Led, Pr.Led.page(es, wh.abs(s0)), Pr.Led.ents(F, wh.abs(s0)), wh.fresh(es, wh.abs(s0), z, Nil{}, {==})))
          %e1 : {wh.lift(Work.wk_done(Work.wk_reads(F, s0))) == Work.wk_spell_step(Pr.Led.done(_)) : FW.St & String}
          wh.done(Work.wk_reads(F, s0))
        case Pr.Note{+x}:
          %wh.snoc(a, Pr.ANote{x}, Nil{}) : {wh.lift(Work.wk_done(Work.wk.S{List.append(&2, Pr.Act, a, [Pr.ANote{x}]), p, r, z})) == Work.wk_spell_step(Pr.Led.done(Pr.Led{_, wh.canon(p), r, z})) : FW.St & String}
          wh.done(Work.wk.S{List.append(&2, Pr.Act, a, [Pr.ANote{x}]), p, r, z})

# The history
# -----------

def wh.run(evs: List<&2, Pr.Ev>, r: Work.wk.S & String, h: {Work.wk_evs_fit(evs) == True{} : Bool}) -> {Work.wk_run(evs, wh.lift(r)) == Work.wk_spec(evs, r) : List<&2, String>}:
  match evs:
    case Nil{}:
      match r:
        case (s, o):
          {==}
    case +e <> +t:
      match r:
        case (+s, +o):
          +hh = h
          %Equal.sym(FW.St & String, FW.step(FW.Live{wh.abs(s)}, Work.wk_spell_ev(e, "")), Work.wk_spell_step(Pr.next(wh.abs(s), e)), LWork.wk.step(wh.abs(s), e, LLogicBool.wr_and_l(Work.wk_ev_fits(e), Work.wk_evs_fit(t), hh))) : {o <> Work.wk_run(t, _) == o <> Work.wk_spec(t, Work.wk_next(s, e)) : List<&2, String>}
          %wh.next(s, e) : {o <> Work.wk_run(t, _) == o <> Work.wk_spec(t, Work.wk_next(s, e)) : List<&2, String>}
          Equal.cong(List<&2, String>, List<&2, String>, y => o <> y, Work.wk_run(t, wh.lift(Work.wk_next(s, e))), Work.wk_spec(t, Work.wk_next(s, e)), wh.run(t, Work.wk_next(s, e), LLogicBool.wr_and_r(Work.wk_ev_fits(e), Work.wk_evs_fit(t), hh)))

def Work.work_entry_history(evs, h):
  wh.run(evs, (Work.wk_start(), ""), h)
