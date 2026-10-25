# eukhe: the proof of LAW work_entry_history
# The spec's ledger, mapped onto the model's state (its acts to their
# distinct acts, its blocks to the calls that wait after them), moves as
# the model moves at every event, with the same reply (wh.next); the
# entry runs the model on every spelled event (work_entry_answers).

import Base
import ../../laws/work.bend as Work
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LWork

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

def wh.ent(st: Work.wk.S, e: Pr.Ent) -> {wh.abs(Work.wk_ent(st, e)) == Pr.Led.ent(wh.abs(st), e) : Pr.Led}:
  match st:
    case Work.wk.S{a, p, r, z}:
      match e:
        case Pr.Ent{i, bs}:
          wh.blks(bs, Work.wk.S{a, p, r, Some{i}})

def wh.ents(es: List<&2, Pr.Ent>, +st: Work.wk.S) -> {wh.abs(Work.wk_ents(es, st)) == Pr.Led.ents(es, wh.abs(st)) : Pr.Led}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      %wh.ent(st, e) : {wh.abs(Work.wk_ents(t, Work.wk_ent(st, e))) == Pr.Led.ents(t, _) : Pr.Led}
      wh.ents(t, Work.wk_ent(st, e))

def wh.after(z: Maybe<&2, Nat>, e: Pr.Ent) -> {Work.wk_after(z, Work.wk_id(e)) == Pr.newer(z, Pr.Ent.id(e)) : Bool}:
  match z:
    case None{}:
      {==}
    case Some{x}:
      match e:
        case Pr.Ent{i, bs}:
          {==}

def wh.page_at(b: Bool, st: Work.wk.S, e: Pr.Ent) -> {wh.abs(Work.wk_page.at(b, st, e)) == Pr.Led.page.at(b, wh.abs(st), e) : Pr.Led}:
  match b:
    case True{}:
      wh.ent(st, e)
    case False{}:
      {==}

def wh.page(es: List<&2, Pr.Ent>, st: Work.wk.S) -> {wh.abs(Work.wk_page(es, st)) == Pr.Led.page(es, wh.abs(st)) : Pr.Led}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      match st:
        case Work.wk.S{+a, +p, +r, +z}:
          %wh.after(z, e) : {wh.abs(Work.wk_page(t, Work.wk_page.at(Work.wk_after(z, Work.wk_id(e)), Work.wk.S{a, p, r, z}, e))) == Pr.Led.page(t, Pr.Led.page.at(_, wh.abs(Work.wk.S{a, p, r, z}), e)) : Pr.Led}
          %wh.page_at(Work.wk_after(z, Work.wk_id(e)), Work.wk.S{a, p, r, z}, e) : {wh.abs(Work.wk_page(t, Work.wk_page.at(Work.wk_after(z, Work.wk_id(e)), Work.wk.S{a, p, r, z}, e))) == Pr.Led.page(t, _) : Pr.Led}
          wh.page(t, Work.wk_page.at(Work.wk_after(z, Work.wk_id(e)), Work.wk.S{a, p, r, z}, e))

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
      %wh.ents(es, st) : {wh.lift(Work.wk_done(Work.wk_seen(Work.wk_ents(es, st), n))) == Work.wk_spell_step(Pr.Led.done(Pr.Led.seen(_, n))) : FW.St & String}
      %wh.seen(Work.wk_ents(es, st), n) : {wh.lift(Work.wk_done(Work.wk_seen(Work.wk_ents(es, st), n))) == Work.wk_spell_step(Pr.Led.done(_)) : FW.St & String}
      wh.done(Work.wk_seen(Work.wk_ents(es, st), n))
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
          %wh.page(es, Work.wk.S{a, p, r, z}) : {wh.lift(Work.wk_done(Work.wk_page(es, Work.wk.S{a, p, r, z}))) == Work.wk_spell_step(Pr.Led.done(_)) : FW.St & String}
          wh.done(Work.wk_page(es, Work.wk.S{a, p, r, z}))
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
