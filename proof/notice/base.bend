# eukhe: lemmas the proofs of area notice share

import Base
import ../../bend/notice.bend as No
import ../../bend/ffi_notice.bend as FNo
import ../../bend/wire.bend as Wr
import ../../laws/notice.bend as Notice
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase
import ../base/wire.bend as LWire

# ---- notice ----

# proof_notice: the restore notice laws of LAWS.bend section supervisor (D1).
#
# - notice_shown_once: each stored notice is in one of two states: not
#   in the record and never shown, or in the record and shown once
#   (`pn.ok`). A restore adds a notice in the first state, and an offer
#   (`No.show`) moves a notice to the second state (`pn.show_shown`).
#   So no notice shows more than once.
# - notice_per_restore: an attach offers every stored notice, so after
#   it each one showed exactly once (`pn.full`), and the view stores one
#   notice for each restore (`pn.len_go`).

# Logic
# -----

def notice.pn.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def notice.pn.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : notice.pn.BD(_, A, Unit)
  Unit{}

def notice.pn.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      notice.pn.absurdF({False{} == True{} : Bool}, h)

def notice.pn.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      notice.pn.absurdF({b == True{} : Bool}, h)

def notice.pn.and_t(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      notice.pn.absurdF({Bool.and(False{}, b) == True{} : Bool}, ea)

# The two states of a notice
# --------------------------

def pn.zero(c: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+p:
      False{}

def pn.one(c: Nat) -> Bool:
  match c:
    case 0n:
      False{}
    case 1n+p:
      pn.zero(p)

# not in the record and never shown, or in the record and shown once
def pn.ok(n: No.N) -> Bool:
  match n:
    case No.N{s, c}:
      match s:
        case True{}:
          pn.one(c)
        case False{}:
          pn.zero(c)

def pn.all_ok(ns: List<&2, No.N>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> t:
      Bool.and(pn.ok(n), pn.all_ok(t))

# an offer leaves a notice in the record, shown once
def pn.show_shown(n: No.N, h: {pn.ok(n) == True{} : Bool}) -> {No.show(n) == No.N{True{}, 1n} : No.N}:
  match n:
    case No.N{s, c}:
      match s:
        case True{}:
          match c:
            case 0n:
              notice.pn.absurdF({No.show(No.N{True{}, 0n}) == No.N{True{}, 1n} : No.N}, h)
            case 1n+p:
              match p:
                case 0n:
                  {==}
                case 1n+q:
                  notice.pn.absurdF({No.show(No.N{True{}, 2n+q}) == No.N{True{}, 1n} : No.N}, h)
        case False{}:
          match c:
            case 0n:
              {==}
            case 1n+p:
              notice.pn.absurdF({No.show(No.N{False{}, 1n+p}) == No.N{True{}, 1n} : No.N}, h)

def pn.ok_show(+n: No.N, h: {pn.ok(n) == True{} : Bool}) -> {pn.ok(No.show(n)) == True{} : Bool}:
  %Equal.sym(No.N, No.show(n), No.N{True{}, 1n}, pn.show_shown(n, h)) : {pn.ok(_) == True{} : Bool}
  {==}

# Every event keeps the two states
# --------------------------------

def pn.ok_rebuild(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.rebuild(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      notice.pn.and_t(pn.ok(No.show(n)), pn.all_ok(No.rebuild(t)), pn.ok_show(n, notice.pn.and_l(pn.ok(n), pn.all_ok(t), h)), pn.ok_rebuild(t, notice.pn.and_r(pn.ok(n), pn.all_ok(t), h)))

def pn.ok_live_at(t: List<&2, No.N>, +n: No.N, hn: {pn.ok(n) == True{} : Bool}, +ht: {pn.all_ok(t) == True{} : Bool}) -> {pn.all_ok(No.live.at(t, n)) == True{} : Bool}:
  match t:
    case Nil{}:
      notice.pn.and_t(pn.ok(No.show(n)), True{}, pn.ok_show(n, hn), {==})
    case +m <> +u:
      notice.pn.and_t(pn.ok(n), pn.all_ok(No.live.at(u, m)), hn, pn.ok_live_at(u, m, notice.pn.and_l(pn.ok(m), pn.all_ok(u), ht), notice.pn.and_r(pn.ok(m), pn.all_ok(u), ht)))

def pn.ok_live(ns: List<&2, No.N>, +h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.live(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case +n <> +t:
      pn.ok_live_at(t, n, notice.pn.and_l(pn.ok(n), pn.all_ok(t), h), notice.pn.and_r(pn.ok(n), pn.all_ok(t), h))

def pn.ok_append(ns: List<&2, No.N>, +x: No.N, +h: {pn.all_ok(ns) == True{} : Bool}, hx: {pn.ok(x) == True{} : Bool}) -> {pn.all_ok(List.append(&2, No.N, ns, [x])) == True{} : Bool}:
  match ns:
    case Nil{}:
      notice.pn.and_t(pn.ok(x), True{}, hx, {==})
    case +n <> +t:
      notice.pn.and_t(pn.ok(n), pn.all_ok(List.append(&2, No.N, t, [x])), notice.pn.and_l(pn.ok(n), pn.all_ok(t), h), pn.ok_append(t, x, notice.pn.and_r(pn.ok(n), pn.all_ok(t), h), hx))

def pn.ok_step(+ns: List<&2, No.N>, e: No.Ev, h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.step(ns, e)) == True{} : Bool}:
  match e:
    case No.Restore{}:
      pn.ok_append(ns, No.N{False{}, 0n}, h, {==})
    case No.Live{}:
      pn.ok_live(ns, h)
    case No.Reconnect{}:
      pn.ok_rebuild(ns, h)

def pn.ok_go(evs: List<&2, No.Ev>, +ns: List<&2, No.N>, h: {pn.all_ok(ns) == True{} : Bool}) -> {pn.all_ok(No.go(evs, ns)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case +e <> +rest:
      pn.ok_go(rest, No.step(ns, e), pn.ok_step(ns, e, h))

# ---- the rule ----

# The proofs of the laws of laws/notice.bend on the rule (bend/notice.bend
# `visible`, `record`, `answer`) and its entry (bend/ffi_notice.bend).
#
# - The rule's equality `No.same` is the spec's `nt_eq` (`nt.same_eq`), and
#   it is reflexive (`nt.same_refl`, through `Word.cmp` on the char codes).
# - A record adds, for its session, the stamps of the restore notices
#   among its messages (`nt.held_rec`): the record holds a notice after it
#   exactly when it held it before, or the record is of that session and
#   holds a restore notice of that stamp (the spec's `nt_has`).
# - An ask spelled by the spec reads back whole (`nt.ask_rt`), so the
#   entry's step is the rule's answer, spelled (`nt.step`).

# Logic
# -----

def nt.and_false(b: Bool) -> {Bool.and(b, False{}) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nt.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# b is True when its negation is False
def nt.not_false(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      notice.pn.absurdF({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, h))

# and over or: the record of one message before the rest
def nt.mix(e: Bool, a: Bool, b: Bool, -h: Bool) -> {Bool.or(Bool.and(e, b), Bool.or(Bool.and(e, a), h)) == Bool.or(Bool.and(e, Bool.or(a, b)), h) : Bool}:
  match e:
    case False{}:
      {==}
    case True{}:
      match a:
        case True{}:
          nt.or_true(b)
        case False{}:
          {==}

# String equality
# ---------------

# the rule's equality is the spec's
def nt.same_eq(a: String, b: String) -> {No.same(a, b) == Notice.nt_eq(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{d, u}:
      {==}
    case SCon{c, t} SNil{}:
      {==}
    case SCon{c, t} SCon{d, u}:
      %nt.same_eq(t, u) : {Bool.and(Char.is_eq(c, d), No.same(t, u)) == Bool.and(Char.is_eq(c, d), _) : Bool}
      {==}

def nt.fin_refl(b: Bool) -> {Word.cmp.fin(b, b, EQ{}) == EQ{} : Cmp}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nt.word_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          %Equal.sym(Cmp, Word.cmp(p, t, t), EQ{}, nt.word_refl(p, t)) : {Word.cmp.fin(b, b, _) == EQ{} : Cmp}
          nt.fin_refl(b)

def nt.char_refl(c: Char) -> {Char.is_eq(c, c) == True{} : Bool}:
  match c:
    case Chr{x}:
      match x:
        case U32{w}:
          %Equal.sym(Cmp, Word.cmp(32n, w, w), EQ{}, nt.word_refl(32n, w)) : {Cmp.is_eq(_) == True{} : Bool}
          {==}

# every text is the same as itself
def nt.same_refl(a: String) -> {No.same(a, a) == True{} : Bool}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(Bool, Char.is_eq(c, c), True{}, nt.char_refl(c)) : {Bool.and(_, No.same(t, t)) == True{} : Bool}
      nt.same_refl(t)

# The record
# ----------

# the stamp of a restore notice is s
def nt.hit(n: Maybe<&2, String>, +s: String) -> Bool:
  match n:
    case None{}:
      False{}
    case Some{t}:
      No.same(t, s)

def nt.hit_of(b: Bool, +t: String, +s: String) -> {nt.hit(No.notice.of(b, t), s) == Bool.and(b, No.same(t, s)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the rule's restore notice of stamp s is the spec's
def nt.hit_is(m: No.Msg, +s: String) -> {nt.hit(No.notice(m), s) == Notice.nt_is(m, s) : Bool}:
  match m:
    case No.Other{}:
      {==}
    case No.Custom{+k, +t}:
      %Equal.sym(Bool, nt.hit(No.notice.of(No.same(k, No.restore_kind()), t), s), Bool.and(No.same(k, No.restore_kind()), No.same(t, s)), nt.hit_of(No.same(k, No.restore_kind()), t, s)) : {_ == Notice.nt_is(No.Custom{k, t}, s) : Bool}
      %nt.same_eq(k, No.restore_kind()) : {Bool.and(No.same(k, No.restore_kind()), No.same(t, s)) == Bool.and(_, Notice.nt_eq(t, s)) : Bool}
      %nt.same_eq(t, s) : {Bool.and(No.same(k, No.restore_kind()), No.same(t, s)) == Bool.and(No.same(k, No.restore_kind()), _) : Bool}
      {==}

# one message of a record
def nt.held_one(n: Maybe<&2, String>, +sid: String, +rs: List<&2, No.Seen>, +q: String, +s: String) -> {No.held(No.record.one(n, sid, rs), q, s) == Bool.or(Bool.and(No.same(sid, q), nt.hit(n, s)), No.held(rs, q, s)) : Bool}:
  match n:
    case None{}:
      %Equal.sym(Bool, Bool.and(No.same(sid, q), False{}), False{}, nt.and_false(No.same(sid, q))) : {No.held(rs, q, s) == Bool.or(_, No.held(rs, q, s)) : Bool}
      {==}
    case Some{t}:
      {==}

# a record holds, after it, what it held before, and the restore notices
# of its session among its messages
def nt.held_rec(ms: List<&2, No.Msg>, +sid: String, +rs: List<&2, No.Seen>, +q: String, +s: String) -> {No.held(No.record.go(ms, sid, rs), q, s) == Bool.or(Bool.and(No.same(sid, q), Notice.nt_has(ms, s)), No.held(rs, q, s)) : Bool}:
  match ms:
    case Nil{}:
      %Equal.sym(Bool, Bool.and(No.same(sid, q), False{}), False{}, nt.and_false(No.same(sid, q))) : {No.held(rs, q, s) == Bool.or(_, No.held(rs, q, s)) : Bool}
      {==}
    case +m <> +t:
      +r1 = No.record.one(No.notice(m), sid, rs)
      +e = No.same(sid, q)
      +h = No.held(rs, q, s)
      +b = Notice.nt_has(t, s)
      %Equal.sym(Bool, No.held(No.record.go(t, sid, r1), q, s), Bool.or(Bool.and(e, b), No.held(r1, q, s)), nt.held_rec(t, sid, r1, q, s)) : {_ == Bool.or(Bool.and(e, Notice.nt_has(m <> t, s)), h) : Bool}
      %Equal.sym(Bool, No.held(r1, q, s), Bool.or(Bool.and(e, nt.hit(No.notice(m), s)), h), nt.held_one(No.notice(m), sid, rs, q, s)) : {Bool.or(Bool.and(e, b), _) == Bool.or(Bool.and(e, Notice.nt_has(m <> t, s)), h) : Bool}
      %Equal.sym(Bool, nt.hit(No.notice(m), s), Notice.nt_is(m, s), nt.hit_is(m, s)) : {Bool.or(Bool.and(e, b), Bool.or(Bool.and(e, _), h)) == Bool.or(Bool.and(e, Notice.nt_has(m <> t, s)), h) : Bool}
      nt.mix(e, Notice.nt_is(m, s), b, h)

# the decision on a message whose notice test answered b
def nt.vis_of(b: Bool, +rs: List<&2, No.Seen>, +sid: String, +s: String) -> {No.visible.at(rs, sid, No.notice.of(b, s)) == Bool.not(Bool.and(b, No.held(rs, sid, s))) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the record after the asks qs holds what the spec says they recorded
def nt.book_held(qs: List<&2, No.Ask>, +sid: String, +s: String) -> {No.held(Notice.nt_book(qs), sid, s) == Notice.nt_noted(qs, sid, s) : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +t:
      match q:
        case No.Shows{a, m}:
          nt.book_held(t, sid, s)
        case No.Notes{+a, +ms}:
          +bk = Notice.nt_book(t)
          %Equal.sym(Bool, No.held(No.record.go(ms, a, bk), sid, s), Bool.or(Bool.and(No.same(a, sid), Notice.nt_has(ms, s)), No.held(bk, sid, s)), nt.held_rec(ms, a, bk, sid, s)) : {_ == Notice.nt_noted(No.Notes{a, ms} <> t, sid, s) : Bool}
          %nt.same_eq(a, sid) : {Bool.or(Bool.and(No.same(a, sid), Notice.nt_has(ms, s)), No.held(bk, sid, s)) == Bool.or(Bool.and(_, Notice.nt_has(ms, s)), Notice.nt_noted(t, sid, s)) : Bool}
          %nt.book_held(t, sid, s) : {Bool.or(Bool.and(No.same(a, sid), Notice.nt_has(ms, s)), No.held(bk, sid, s)) == Bool.or(Bool.and(No.same(a, sid), Notice.nt_has(ms, s)), _) : Bool}
          {==}

# after the asks qs, the rule decides what the spec decides
def nt.rule(+qs: List<&2, No.Ask>, +sid: String, m: No.Msg) -> {No.visible(Notice.nt_book(qs), sid, m) == Notice.nt_shows(qs, sid, m) : Bool}:
  match m:
    case No.Other{}:
      {==}
    case No.Custom{+k, +s}:
      +bk = Notice.nt_book(qs)
      %Equal.sym(Bool, No.visible.at(bk, sid, No.notice.of(No.same(k, No.restore_kind()), s)), Bool.not(Bool.and(No.same(k, No.restore_kind()), No.held(bk, sid, s))), nt.vis_of(No.same(k, No.restore_kind()), bk, sid, s)) : {_ == Notice.nt_shows(qs, sid, No.Custom{k, s}) : Bool}
      %nt.same_eq(k, No.restore_kind()) : {Bool.not(Bool.and(No.same(k, No.restore_kind()), No.held(bk, sid, s))) == Bool.not(Bool.and(_, Notice.nt_noted(qs, sid, s))) : Bool}
      %nt.book_held(qs, sid, s) : {Bool.not(Bool.and(No.same(k, No.restore_kind()), No.held(bk, sid, s))) == Bool.not(Bool.and(No.same(k, No.restore_kind()), _)) : Bool}
      {==}

# The wire
# --------

# a message the spec spells reads back
def nt.msg_rt(m: No.Msg, +rest: String, +h: {Notice.nt_msg_fits(m) == True{} : Bool}) -> {FNo.get_msg(Notice.nt_spell_msg(m, rest)) == Wr.Got{m, rest} : Wr.Dec<No.Msg>}:
  match m:
    case No.Other{}:
      {==}
    case No.Custom{+k, +s}:
      +x = Wr.put_str(s, rest)
      +hk = notice.pn.and_l(Notice.nt_str_fits(k), Notice.nt_str_fits(s), h)
      +hs = notice.pn.and_r(Notice.nt_str_fits(k), Notice.nt_str_fits(s), h)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(k, x)), Wr.Got{k, x}, Wire.wire_str_round_trip(k, x, hk)) : {FNo.get_msg.kind(_) == Wr.Got{No.Custom{k, s}, rest} : Wr.Dec<No.Msg>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(x), Wr.Got{s, rest}, Wire.wire_str_round_trip(s, rest, hs)) : {FNo.get_msg.custom(k, _) == Wr.Got{No.Custom{k, s}, rest} : Wr.Dec<No.Msg>}
      {==}

# the items of a list of messages, then rest
def nt.items(ms: List<&2, No.Msg>, rest: String) -> String:
  match ms:
    case Nil{}:
      rest
    case m <> t:
      Notice.nt_spell_msg(m, nt.items(t, rest))

def nt.put_go(ms: List<&2, No.Msg>, +rest: String) -> {Wr.put_list.go(~No.Msg, ~Notice.nt_spell_msg, ms, rest) == (List.length(&2, No.Msg, ms), nt.items(ms, rest)) : Nat & String}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~No.Msg, ~Notice.nt_spell_msg, t, rest), (List.length(&2, No.Msg, t), nt.items(t, rest)), nt.put_go(t, rest)) : {Wr.put_list.step(~No.Msg, ~Notice.nt_spell_msg, m, _) == (1n+List.length(&2, No.Msg, t), Notice.nt_spell_msg(m, nt.items(t, rest))) : Nat & String}
      {==}

# a list of messages is its count, then its items
def nt.put_list(+ms: List<&2, No.Msg>, +rest: String) -> {Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, rest) == Wr.put_nat(List.length(&2, No.Msg, ms), nt.items(ms, rest)) : String}:
  Equal.cong(Nat & String, String, x => Wr.put_list.fin(x), Wr.put_list.go(~No.Msg, ~Notice.nt_spell_msg, ms, rest), (List.length(&2, No.Msg, ms), nt.items(ms, rest)), nt.put_go(ms, rest))

def nt.fit_l(m: No.Msg, -ms: List<&2, No.Msg>, h: {Notice.nt_msgs_fit(m <> ms) == True{} : Bool}) -> {Notice.nt_msg_fits(m) == True{} : Bool}:
  notice.pn.and_l(Notice.nt_msg_fits(m), Notice.nt_msgs_fit(ms), h)

def nt.fit_r(m: No.Msg, -ms: List<&2, No.Msg>, h: {Notice.nt_msgs_fit(m <> ms) == True{} : Bool}) -> {Notice.nt_msgs_fit(ms) == True{} : Bool}:
  notice.pn.and_r(Notice.nt_msg_fits(m), Notice.nt_msgs_fit(ms), h)

def nt.list_go(ms: List<&2, No.Msg>, +m: No.Msg, +rest: String, +hf: {Notice.nt_msgs_fit(m <> ms) == True{} : Bool}) -> {Wr.get_list.go(~No.Msg, ~FNo.get_msg, List.length(&2, No.Msg, ms), FNo.get_msg(Notice.nt_spell_msg(m, nt.items(ms, rest)))) == Wr.Got{m <> ms, rest} : Wr.Dec<List<&2, No.Msg>>}:
  match ms:
    case Nil{}:
      %Equal.sym(Wr.Dec<No.Msg>, FNo.get_msg(Notice.nt_spell_msg(m, rest)), Wr.Got{m, rest}, nt.msg_rt(m, rest, nt.fit_l(m, Nil{}, hf))) : {Wr.get_list.go(~No.Msg, ~FNo.get_msg, 0n, _) == Wr.Got{[m], rest} : Wr.Dec<List<&2, No.Msg>>}
      {==}
    case +m2 <> +ms2:
      %Equal.sym(Wr.Dec<No.Msg>, FNo.get_msg(Notice.nt_spell_msg(m, nt.items(m2 <> ms2, rest))), Wr.Got{m, nt.items(m2 <> ms2, rest)}, nt.msg_rt(m, nt.items(m2 <> ms2, rest), nt.fit_l(m, m2 <> ms2, hf))) : {Wr.get_list.go(~No.Msg, ~FNo.get_msg, 1n+List.length(&2, No.Msg, ms2), _) == Wr.Got{m <> m2 <> ms2, rest} : Wr.Dec<List<&2, No.Msg>>}
      %Equal.sym(Wr.Dec<List<&2, No.Msg>>, Wr.get_list.go(~No.Msg, ~FNo.get_msg, List.length(&2, No.Msg, ms2), FNo.get_msg(Notice.nt_spell_msg(m2, nt.items(ms2, rest)))), Wr.Got{m2 <> ms2, rest}, nt.list_go(ms2, m2, rest, nt.fit_r(m, m2 <> ms2, hf))) : {Wr.get_list.cons(No.Msg, m, _) == Wr.Got{m <> m2 <> ms2, rest} : Wr.Dec<List<&2, No.Msg>>}
      {==}

def nt.list_start(ms: List<&2, No.Msg>, +rest: String, +hf: {Notice.nt_msgs_fit(ms) == True{} : Bool}) -> {Wr.get_list.start(~No.Msg, ~FNo.get_msg, Wr.Got{List.length(&2, No.Msg, ms), nt.items(ms, rest)}) == Wr.Got{ms, rest} : Wr.Dec<List<&2, No.Msg>>}:
  match ms:
    case Nil{}:
      {==}
    case +m <> +t:
      nt.list_go(t, m, rest, hf)

# a list of messages that fits reads back
def nt.list_rt(+ms: List<&2, No.Msg>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, No.Msg, ms)) == True{} : Bool}, +hf: {Notice.nt_msgs_fit(ms) == True{} : Bool}) -> {Wr.get_list(~No.Msg, ~FNo.get_msg, Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, rest)) == Wr.Got{ms, rest} : Wr.Dec<List<&2, No.Msg>>}:
  %Equal.sym(String, Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, rest), Wr.put_nat(List.length(&2, No.Msg, ms), nt.items(ms, rest)), nt.put_list(ms, rest)) : {Wr.get_list(~No.Msg, ~FNo.get_msg, _) == Wr.Got{ms, rest} : Wr.Dec<List<&2, No.Msg>>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, No.Msg, ms), nt.items(ms, rest))), Wr.Got{List.length(&2, No.Msg, ms), nt.items(ms, rest)}, Wire.wire_nat_round_trip(List.length(&2, No.Msg, ms), nt.items(ms, rest), hl)) : {Wr.get_list.start(~No.Msg, ~FNo.get_msg, _) == Wr.Got{ms, rest} : Wr.Dec<List<&2, No.Msg>>}
  nt.list_start(ms, rest, hf)

# an ask the spec spells reads back
def nt.ask_rt(q: No.Ask, +rest: String, +h: {Notice.nt_ask_fits(q) == True{} : Bool}) -> {FNo.get_ask(Notice.nt_spell_ask(q, rest)) == Wr.Got{q, rest} : Wr.Dec<No.Ask>}:
  match q:
    case No.Shows{+sid, +m}:
      +x = Notice.nt_spell_msg(m, rest)
      +hs = notice.pn.and_l(Notice.nt_str_fits(sid), Notice.nt_msg_fits(m), h)
      +hm = notice.pn.and_r(Notice.nt_str_fits(sid), Notice.nt_msg_fits(m), h)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(sid, x)), Wr.Got{sid, x}, Wire.wire_str_round_trip(sid, x, hs)) : {FNo.get_ask.shows.sid(_) == Wr.Got{No.Shows{sid, m}, rest} : Wr.Dec<No.Ask>}
      %Equal.sym(Wr.Dec<No.Msg>, FNo.get_msg(x), Wr.Got{m, rest}, nt.msg_rt(m, rest, hm)) : {FNo.get_ask.shows(sid, _) == Wr.Got{No.Shows{sid, m}, rest} : Wr.Dec<No.Ask>}
      {==}
    case No.Notes{+sid, +ms}:
      +x = Wr.put_list(~No.Msg, ~Notice.nt_spell_msg, ms, rest)
      +hlf = Bool.and(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms))
      +hs = notice.pn.and_l(Notice.nt_str_fits(sid), hlf, h)
      +hr = notice.pn.and_r(Notice.nt_str_fits(sid), hlf, h)
      +hl = notice.pn.and_l(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms), hr)
      +hf = notice.pn.and_r(LawsBase.wire_fits(List.length(&2, No.Msg, ms)), Notice.nt_msgs_fit(ms), hr)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(sid, x)), Wr.Got{sid, x}, Wire.wire_str_round_trip(sid, x, hs)) : {FNo.get_ask.notes.sid(_) == Wr.Got{No.Notes{sid, ms}, rest} : Wr.Dec<No.Ask>}
      %Equal.sym(Wr.Dec<List<&2, No.Msg>>, Wr.get_list(~No.Msg, ~FNo.get_msg, x), Wr.Got{ms, rest}, nt.list_rt(ms, rest, hl, hf)) : {FNo.get_ask.notes(sid, _) == Wr.Got{No.Notes{sid, ms}, rest} : Wr.Dec<No.Ask>}
      {==}

def nt.ans(+rs: List<&2, No.Seen>, a: No.Ans) -> {FNo.step.ans((rs, a)) == Notice.nt_spell_step((rs, a)) : FNo.St & String}:
  match a:
    case No.Shown{b}:
      {==}
    case No.Noted{}:
      {==}

def nt.step.at(+rs: List<&2, No.Seen>, q: No.Ask) -> {FNo.step.ask(rs, Wr.Got{q, ""}) == Notice.nt_spell_step(No.answer(rs, q)) : FNo.St & String}:
  match q:
    case No.Shows{+sid, +m}:
      nt.ans(rs, No.Shown{No.visible(rs, sid, m)})
    case No.Notes{+sid, +ms}:
      nt.ans(No.record(rs, sid, ms), No.Noted{})

# an ask the spec spells steps the entry as the rule answers it
def nt.step(+rs: List<&2, No.Seen>, +q: No.Ask, h: {Notice.nt_ask_fits(q) == True{} : Bool}) -> {FNo.step(FNo.Live{rs}, Notice.nt_spell_ask(q, "")) == Notice.nt_spell_step(No.answer(rs, q)) : FNo.St & String}:
  %Equal.sym(Wr.Dec<No.Ask>, FNo.get_ask(Notice.nt_spell_ask(q, "")), Wr.Got{q, ""}, nt.ask_rt(q, "", h)) : {FNo.step.ask(rs, _) == Notice.nt_spell_step(No.answer(rs, q)) : FNo.St & String}
  nt.step.at(rs, q)
