# eukhe.com's Neovim: every editor the events reach is settled
# ============================================================
#
# Vim.step ends with Vim.final (vim/vim.bend), on the files and the screen
# size of the editor before it (Vim.keep). So the editor after any events
# is Vim.final of something (Reach.replay), holds the files the start
# made of fs (Reach.files_run) and the screen the last size event asked
# for (Reach.rows_run, Reach.cols_run). After an Esc it is in normal mode
# (Reach.normal_mode).

import Base
import ../../vim/types.bend as T
import ../../vim/buf.bend as B
import ../../vim/st.bend as S
import ../../vim/keys.bend as K
import ../../vim/vim.bend as Vim
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./final.bend as Fi

# One step
# --------

# the editor the step from s settles on: e's editor, on s's files and
# screen (a size event's screen for one)
def Reach.env(+s: T.St, e: T.Ev) -> T.St:
  match e:
    case T.EvKey{name}:
      s
    case T.EvClick{row, col}:
      s
    case T.EvWheel{down, notches}:
      s
    case T.EvSize{rows, cols}:
      Vim.Vim.size(s, rows, cols)

def Reach.raw(+s: T.St, e: T.Ev) -> T.Step:
  match e:
    case T.EvKey{name}:
      K.Key.in(s, S.St.mode(s), name)
    case T.EvClick{row, col}:
      K.Key.ok(Vim.Vim.click(s, S.St.mode(s), row, col))
    case T.EvWheel{down, notches}:
      K.Key.ok(Vim.Vim.wheel(s, S.St.mode(s), down, notches))
    case T.EvSize{rows, cols}:
      K.Key.ok(Vim.Vim.size(s, rows, cols))

def Reach.next(+s: T.St, +e: T.Ev) -> T.St:
  Vim.Vim.keep(Reach.env(s, e), Laws.Spec.after(Reach.raw(s, e)))

def Reach.done(+s: T.St, r: T.Step) -> {Laws.Spec.after(Vim.Vim.done(s, r)) == Vim.Vim.final(Vim.Vim.keep(s, Laws.Spec.after(r))) : T.St}:
  match r:
    case T.Step{st, act}:
      {==}

# the editor after a step is Vim.final of the next one
def Reach.step(+s: T.St, e: T.Ev) -> {Laws.Spec.after(Vim.Vim.step(s, e)) == Vim.Vim.final(Reach.next(s, e)) : T.St}:
  match e:
    case T.EvKey{+name}:
      Reach.done(s, K.Key.in(s, S.St.mode(s), name))
    case T.EvClick{+row, +col}:
      Reach.done(s, K.Key.ok(Vim.Vim.click(s, S.St.mode(s), row, col)))
    case T.EvWheel{+down, +notches}:
      Reach.done(s, K.Key.ok(Vim.Vim.wheel(s, S.St.mode(s), down, notches)))
    case T.EvSize{+rows, +cols}:
      Reach.done(Vim.Vim.size(s, rows, cols), K.Key.ok(Vim.Vim.size(s, rows, cols)))

# Many steps
# ----------

# what the editor after evs from Vim.final(x) is Vim.final of
def Reach.pre(evs: List<&2, T.Ev>, +x: T.St) -> T.St:
  match evs:
    case Nil{}:
      x
    case Con{+e, t}:
      Reach.pre(t, Reach.next(Vim.Vim.final(x), e))

def Reach.replay(evs: List<&2, T.Ev>, +x: T.St) -> {Laws.Spec.replay(evs, Vim.Vim.final(x)) == Vim.Vim.final(Reach.pre(evs, x)) : T.St}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +n = Reach.next(Vim.Vim.final(x), e)
      %Equal.sym(T.St, Laws.Spec.after(Vim.Vim.step(Vim.Vim.final(x), e)), Vim.Vim.final(n), Reach.step(Vim.Vim.final(x), e)) : {Laws.Spec.replay(t, _) == Vim.Vim.final(Reach.pre(t, n)) : T.St}
      Reach.replay(t, n)

# the editor after evs from the start
def Reach.run(fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, evs: List<&2, T.Ev>) -> {Laws.Spec.run(fs, rows, cols, evs) == Vim.Vim.final(Reach.pre(evs, Vim.Vim.start(fs, rows, cols))) : T.St}:
  Reach.replay(evs, Vim.Vim.start(fs, rows, cols))

def Reach.final(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> Fi.Final(Laws.Spec.run(fs, rows, cols, evs)):
  +x = Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Reach.run(fs, rows, cols, evs)) : Fi.Final(_)
  Fi.Final.of(x)

# Fields
# ------

def Field.files_final(+x: T.St) -> {S.St.files(Vim.Vim.final(x)) == S.St.files(x) : List<&2, T.Buf>}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Field.rows_final(+x: T.St) -> {S.St.rows(Vim.Vim.final(x)) == Nat.max(S.St.rows(x), 3n) : Nat}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Field.cols_final(+x: T.St) -> {S.St.cols(Vim.Vim.final(x)) == Nat.max(S.St.cols(x), 12n) : Nat}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Field.mode_final(+x: T.St) -> {S.St.mode(Vim.Vim.final(x)) == S.St.mode(x) : T.Mode}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.files(+s: T.St, st: T.St) -> {S.St.files(Vim.Vim.keep(s, st)) == S.St.files(s) : List<&2, T.Buf>}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.rows(+s: T.St, st: T.St) -> {S.St.rows(Vim.Vim.keep(s, st)) == S.St.rows(s) : Nat}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.cols(+s: T.St, st: T.St) -> {S.St.cols(Vim.Vim.keep(s, st)) == S.St.cols(s) : Nat}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.mode(+s: T.St, st: T.St) -> {S.St.mode(Vim.Vim.keep(s, st)) == S.St.mode(st) : T.Mode}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Size.files(+s: T.St, +r: Nat, +c: Nat) -> {S.St.files(Vim.Vim.size(s, r, c)) == S.St.files(s) : List<&2, T.Buf>}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Size.rows(+s: T.St, +r: Nat, +c: Nat) -> {S.St.rows(Vim.Vim.size(s, r, c)) == r : Nat}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Size.cols(+s: T.St, +r: Nat, +c: Nat) -> {S.St.cols(Vim.Vim.size(s, r, c)) == c : Nat}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# Files
# -----

def Env.files(+s: T.St, e: T.Ev) -> {S.St.files(Reach.env(s, e)) == S.St.files(s) : List<&2, T.Buf>}:
  match e:
    case T.EvKey{name}:
      {==}
    case T.EvClick{row, col}:
      {==}
    case T.EvWheel{down, notches}:
      {==}
    case T.EvSize{+rows, +cols}:
      Size.files(s, rows, cols)

def Reach.files(evs: List<&2, T.Ev>, +x: T.St) -> {S.St.files(Reach.pre(evs, x)) == S.St.files(x) : List<&2, T.Buf>}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, t}:
      +fx = Vim.Vim.final(x)
      +env = Reach.env(fx, e)
      +n = Reach.next(fx, e)
      Equal.trans(List<&2, T.Buf>, S.St.files(Reach.pre(t, n)), S.St.files(n), S.St.files(x), Reach.files(t, n), Equal.trans(List<&2, T.Buf>, S.St.files(n), S.St.files(env), S.St.files(x), Keep.files(env, Laws.Spec.after(Reach.raw(fx, e))), Equal.trans(List<&2, T.Buf>, S.St.files(env), S.St.files(fx), S.St.files(x), Env.files(fx, e), Field.files_final(x))))

def Reach.files_run(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.files(Laws.Spec.run(fs, rows, cols, evs)) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}:
  +x = Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Reach.run(fs, rows, cols, evs)) : {S.St.files(_) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}
  Equal.trans(List<&2, T.Buf>, S.St.files(Vim.Vim.final(x)), S.St.files(x), B.Files.some(fs, Nil{}), Field.files_final(x), Reach.files(evs, Vim.Vim.start(fs, rows, cols)))

# The screen's size
# -----------------

def Nat.max_self(a: Nat) -> {Nat.max(a, a) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(p, p), p, Nat.max_self(p))

def Nat.max_idem(a: Nat, +b: Nat) -> {Nat.max(Nat.max(a, b), b) == Nat.max(a, b) : Nat}:
  match a b:
    case 0n _:
      Nat.max_self(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(Nat.max(p, q), q), Nat.max(p, q), Nat.max_idem(p, q))

def Pick.succ(c: Bool, -a: Nat, -b: Nat) -> {Bool.pick(Nat, c, 1n+a, 1n+b) == 1n+Bool.pick(Nat, c, a, b) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's max is Nat.max
def Spec.max_eq(a: Nat, +b: Nat) -> {Laws.Spec.max(a, b) == Nat.max(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.trans(Nat, Bool.pick(Nat, Nat.is_le(p, q), 1n+q, 1n+p), 1n+Bool.pick(Nat, Nat.is_le(p, q), q, p), 1n+Nat.max(p, q), Pick.succ(Nat.is_le(p, q), q, p), Equal.cong(Nat, Nat, x => 1n+x, Laws.Spec.max(p, q), Nat.max(p, q), Spec.max_eq(p, q)))

def RowsGo.max(t: List<&2, T.Ev>, +a: Nat) -> {Nat.max(Laws.Spec.rows.go(t, Nat.max(a, 3n)), 3n) == Nat.max(Laws.Spec.rows.go(t, a), 3n) : Nat}:
  match t:
    case Nil{}:
      Nat.max_idem(a, 3n)
    case Con{T.EvSize{rows, cols}, u}:
      {==}
    case Con{T.EvKey{name}, u}:
      RowsGo.max(u, a)
    case Con{T.EvClick{row, col}, u}:
      RowsGo.max(u, a)
    case Con{T.EvWheel{down, notches}, u}:
      RowsGo.max(u, a)

def ColsGo.max(t: List<&2, T.Ev>, +a: Nat) -> {Nat.max(Laws.Spec.cols.go(t, Nat.max(a, 12n)), 12n) == Nat.max(Laws.Spec.cols.go(t, a), 12n) : Nat}:
  match t:
    case Nil{}:
      Nat.max_idem(a, 12n)
    case Con{T.EvSize{rows, cols}, u}:
      {==}
    case Con{T.EvKey{name}, u}:
      ColsGo.max(u, a)
    case Con{T.EvClick{row, col}, u}:
      ColsGo.max(u, a)
    case Con{T.EvWheel{down, notches}, u}:
      ColsGo.max(u, a)

# a step that is not a size event keeps the screen: rows(n) is max(rows(x), 3)
def Step.rows_keep(+x: T.St, +t: List<&2, T.Ev>, -n: T.St, e1: {S.St.rows(n) == Nat.max(S.St.rows(x), 3n) : Nat})
  -> {Nat.max(Laws.Spec.rows.go(t, S.St.rows(n)), 3n) == Nat.max(Laws.Spec.rows.go(t, S.St.rows(x)), 3n) : Nat}:
  %Equal.sym(Nat, S.St.rows(n), Nat.max(S.St.rows(x), 3n), e1) : {Nat.max(Laws.Spec.rows.go(t, _), 3n) == Nat.max(Laws.Spec.rows.go(t, S.St.rows(x)), 3n) : Nat}
  RowsGo.max(t, S.St.rows(x))

def Step.cols_keep(+x: T.St, +t: List<&2, T.Ev>, -n: T.St, e1: {S.St.cols(n) == Nat.max(S.St.cols(x), 12n) : Nat})
  -> {Nat.max(Laws.Spec.cols.go(t, S.St.cols(n)), 12n) == Nat.max(Laws.Spec.cols.go(t, S.St.cols(x)), 12n) : Nat}:
  %Equal.sym(Nat, S.St.cols(n), Nat.max(S.St.cols(x), 12n), e1) : {Nat.max(Laws.Spec.cols.go(t, _), 12n) == Nat.max(Laws.Spec.cols.go(t, S.St.cols(x)), 12n) : Nat}
  ColsGo.max(t, S.St.cols(x))

# an event that is no size event keeps the screen (e0: e is one of those)
def Step.rows_ev(+x: T.St, +e: T.Ev, +t: List<&2, T.Ev>, e0: {S.St.rows(Reach.env(Vim.Vim.final(x), e)) == S.St.rows(Vim.Vim.final(x)) : Nat}) -> {Nat.max(Laws.Spec.rows.go(t, S.St.rows(Reach.next(Vim.Vim.final(x), e))), 3n) == Nat.max(Laws.Spec.rows.go(t, S.St.rows(x)), 3n) : Nat}:
  +fx = Vim.Vim.final(x)
  Step.rows_keep(x, t, Reach.next(fx, e), Equal.trans(Nat, S.St.rows(Reach.next(fx, e)), S.St.rows(Reach.env(fx, e)), Nat.max(S.St.rows(x), 3n), Keep.rows(Reach.env(fx, e), Laws.Spec.after(Reach.raw(fx, e))), Equal.trans(Nat, S.St.rows(Reach.env(fx, e)), S.St.rows(fx), Nat.max(S.St.rows(x), 3n), e0, Field.rows_final(x))))

def Step.cols_ev(+x: T.St, +e: T.Ev, +t: List<&2, T.Ev>, e0: {S.St.cols(Reach.env(Vim.Vim.final(x), e)) == S.St.cols(Vim.Vim.final(x)) : Nat}) -> {Nat.max(Laws.Spec.cols.go(t, S.St.cols(Reach.next(Vim.Vim.final(x), e))), 12n) == Nat.max(Laws.Spec.cols.go(t, S.St.cols(x)), 12n) : Nat}:
  +fx = Vim.Vim.final(x)
  Step.cols_keep(x, t, Reach.next(fx, e), Equal.trans(Nat, S.St.cols(Reach.next(fx, e)), S.St.cols(Reach.env(fx, e)), Nat.max(S.St.cols(x), 12n), Keep.cols(Reach.env(fx, e), Laws.Spec.after(Reach.raw(fx, e))), Equal.trans(Nat, S.St.cols(Reach.env(fx, e)), S.St.cols(fx), Nat.max(S.St.cols(x), 12n), e0, Field.cols_final(x))))

def Step.rows_size(+fx: T.St, +rows: Nat, +cols: Nat, +t: List<&2, T.Ev>) -> {Nat.max(Laws.Spec.rows.go(t, S.St.rows(Reach.next(fx, T.EvSize{rows, cols}))), 3n) == Nat.max(Laws.Spec.rows.go(t, rows), 3n) : Nat}:
  +sz = Vim.Vim.size(fx, rows, cols)
  +e1 = Equal.trans(Nat, S.St.rows(Vim.Vim.keep(sz, sz)), S.St.rows(sz), rows, Keep.rows(sz, sz), Size.rows(fx, rows, cols))
  %Equal.sym(Nat, S.St.rows(Vim.Vim.keep(sz, sz)), rows, e1) : {Nat.max(Laws.Spec.rows.go(t, _), 3n) == Nat.max(Laws.Spec.rows.go(t, rows), 3n) : Nat}
  {==}

def Step.cols_size(+fx: T.St, +rows: Nat, +cols: Nat, +t: List<&2, T.Ev>) -> {Nat.max(Laws.Spec.cols.go(t, S.St.cols(Reach.next(fx, T.EvSize{rows, cols}))), 12n) == Nat.max(Laws.Spec.cols.go(t, cols), 12n) : Nat}:
  +sz = Vim.Vim.size(fx, rows, cols)
  +e1 = Equal.trans(Nat, S.St.cols(Vim.Vim.keep(sz, sz)), S.St.cols(sz), cols, Keep.cols(sz, sz), Size.cols(fx, rows, cols))
  %Equal.sym(Nat, S.St.cols(Vim.Vim.keep(sz, sz)), cols, e1) : {Nat.max(Laws.Spec.cols.go(t, _), 12n) == Nat.max(Laws.Spec.cols.go(t, cols), 12n) : Nat}
  {==}

def Step.rows(+x: T.St, e: T.Ev, +t: List<&2, T.Ev>) -> {Nat.max(Laws.Spec.rows.go(t, S.St.rows(Reach.next(Vim.Vim.final(x), e))), 3n) == Nat.max(Laws.Spec.rows.go(Con{e, t}, S.St.rows(x)), 3n) : Nat}:
  match e:
    case T.EvKey{+name}:
      Step.rows_ev(x, T.EvKey{name}, t, {==})
    case T.EvClick{+row, +col}:
      Step.rows_ev(x, T.EvClick{row, col}, t, {==})
    case T.EvWheel{+down, +notches}:
      Step.rows_ev(x, T.EvWheel{down, notches}, t, {==})
    case T.EvSize{+rows, +cols}:
      Step.rows_size(Vim.Vim.final(x), rows, cols, t)

def Step.cols(+x: T.St, e: T.Ev, +t: List<&2, T.Ev>) -> {Nat.max(Laws.Spec.cols.go(t, S.St.cols(Reach.next(Vim.Vim.final(x), e))), 12n) == Nat.max(Laws.Spec.cols.go(Con{e, t}, S.St.cols(x)), 12n) : Nat}:
  match e:
    case T.EvKey{+name}:
      Step.cols_ev(x, T.EvKey{name}, t, {==})
    case T.EvClick{+row, +col}:
      Step.cols_ev(x, T.EvClick{row, col}, t, {==})
    case T.EvWheel{+down, +notches}:
      Step.cols_ev(x, T.EvWheel{down, notches}, t, {==})
    case T.EvSize{+rows, +cols}:
      Step.cols_size(Vim.Vim.final(x), rows, cols, t)

def Reach.rows(evs: List<&2, T.Ev>, +x: T.St) -> {Nat.max(S.St.rows(Reach.pre(evs, x)), 3n) == Nat.max(Laws.Spec.rows.go(evs, S.St.rows(x)), 3n) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +n = Reach.next(Vim.Vim.final(x), e)
      Equal.trans(Nat, Nat.max(S.St.rows(Reach.pre(t, n)), 3n), Nat.max(Laws.Spec.rows.go(t, S.St.rows(n)), 3n), Nat.max(Laws.Spec.rows.go(Con{e, t}, S.St.rows(x)), 3n), Reach.rows(t, n), Step.rows(x, e, t))

def Reach.cols(evs: List<&2, T.Ev>, +x: T.St) -> {Nat.max(S.St.cols(Reach.pre(evs, x)), 12n) == Nat.max(Laws.Spec.cols.go(evs, S.St.cols(x)), 12n) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      +n = Reach.next(Vim.Vim.final(x), e)
      Equal.trans(Nat, Nat.max(S.St.cols(Reach.pre(t, n)), 12n), Nat.max(Laws.Spec.cols.go(t, S.St.cols(n)), 12n), Nat.max(Laws.Spec.cols.go(Con{e, t}, S.St.cols(x)), 12n), Reach.cols(t, n), Step.cols(x, e, t))

# the screen after evs is the last size asked for (at least 3 x 12)
def Reach.rows_run(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.rows(Laws.Spec.run(fs, rows, cols, evs)) == Laws.Spec.rows(rows, evs) : Nat}:
  +x = Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Reach.run(fs, rows, cols, evs)) : {S.St.rows(_) == Laws.Spec.rows(rows, evs) : Nat}
  %Equal.sym(Nat, Laws.Spec.max(Laws.Spec.rows.go(evs, rows), 3n), Nat.max(Laws.Spec.rows.go(evs, rows), 3n), Spec.max_eq(Laws.Spec.rows.go(evs, rows), 3n)) : {S.St.rows(Vim.Vim.final(x)) == _ : Nat}
  Equal.trans(Nat, S.St.rows(Vim.Vim.final(x)), Nat.max(S.St.rows(x), 3n), Nat.max(Laws.Spec.rows.go(evs, rows), 3n), Field.rows_final(x), Reach.rows(evs, Vim.Vim.start(fs, rows, cols)))

def Reach.cols_run(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.cols(Laws.Spec.run(fs, rows, cols, evs)) == Laws.Spec.cols(cols, evs) : Nat}:
  +x = Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Reach.run(fs, rows, cols, evs)) : {S.St.cols(_) == Laws.Spec.cols(cols, evs) : Nat}
  %Equal.sym(Nat, Laws.Spec.max(Laws.Spec.cols.go(evs, cols), 12n), Nat.max(Laws.Spec.cols.go(evs, cols), 12n), Spec.max_eq(Laws.Spec.cols.go(evs, cols), 12n)) : {S.St.cols(Vim.Vim.final(x)) == _ : Nat}
  Equal.trans(Nat, S.St.cols(Vim.Vim.final(x)), Nat.max(S.St.cols(x), 12n), Nat.max(Laws.Spec.cols.go(evs, cols), 12n), Field.cols_final(x), Reach.cols(evs, Vim.Vim.start(fs, rows, cols)))

# a key at the end changes no size
def RowsGo.snoc(evs: List<&2, T.Ev>, -name: String, +a: Nat) -> {Laws.Spec.rows.go(Laws.Spec.snoc(evs, T.EvKey{name}), a) == Laws.Spec.rows.go(evs, a) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case Con{T.EvSize{rows, cols}, u}:
      RowsGo.snoc(u, name, rows)
    case Con{T.EvKey{k}, u}:
      RowsGo.snoc(u, name, a)
    case Con{T.EvClick{row, col}, u}:
      RowsGo.snoc(u, name, a)
    case Con{T.EvWheel{down, notches}, u}:
      RowsGo.snoc(u, name, a)

def ColsGo.snoc(evs: List<&2, T.Ev>, -name: String, +a: Nat) -> {Laws.Spec.cols.go(Laws.Spec.snoc(evs, T.EvKey{name}), a) == Laws.Spec.cols.go(evs, a) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case Con{T.EvSize{rows, cols}, u}:
      ColsGo.snoc(u, name, cols)
    case Con{T.EvKey{k}, u}:
      ColsGo.snoc(u, name, a)
    case Con{T.EvClick{row, col}, u}:
      ColsGo.snoc(u, name, a)
    case Con{T.EvWheel{down, notches}, u}:
      ColsGo.snoc(u, name, a)

# Esc
# ---

def Reach.snoc(evs: List<&2, T.Ev>, +e: T.Ev, +s: T.St) -> {Laws.Spec.replay(Laws.Spec.snoc(evs, e), s) == Laws.Spec.after(Vim.Vim.step(Laws.Spec.replay(evs, s), e)) : T.St}:
  match evs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      Reach.snoc(t, e, Laws.Spec.after(Vim.Vim.step(s, h)))

# Esc from any mode, waiting key or count leaves normal mode
def Esc.mode(s: T.St) -> {S.St.mode(Laws.Spec.after(K.Key.in(s, S.St.mode(s), "<Esc>"))) == T.Normal{} : T.Mode}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match mode:
        case T.Normal{}:
          match pend:
            case T.NoPend{}:
              {==}
            case T.PendG{}:
              {==}
            case T.PendZ{}:
              {==}
            case T.PendLead{}:
              {==}
            case T.PendLeadF{}:
              {==}
            case T.PendY{}:
              {==}
        case T.Typing{kind, text}:
          {==}
        case T.Picking{kind, q, its, n, sel, top, pv, levels}:
          {==}

# the editor in normal mode after evs and an Esc
def Reach.normal_mode(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.mode(Laws.Spec.normal(fs, rows, cols, evs)) == T.Normal{} : T.Mode}:
  +esc = {T.EvKey{"<Esc>"} : T.Ev}
  +r = Laws.Spec.run(fs, rows, cols, evs)
  +n = Reach.next(r, esc)
  %Equal.sym(T.St, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.after(Vim.Vim.step(r, esc)), Reach.snoc(evs, esc, Vim.Vim.init(fs, rows, cols))) : {S.St.mode(_) == T.Normal{} : T.Mode}
  %Equal.sym(T.St, Laws.Spec.after(Vim.Vim.step(r, esc)), Vim.Vim.final(n), Reach.step(r, esc)) : {S.St.mode(_) == T.Normal{} : T.Mode}
  Equal.trans(T.Mode, S.St.mode(Vim.Vim.final(n)), S.St.mode(n), T.Normal{}, Field.mode_final(n), Equal.trans(T.Mode, S.St.mode(n), S.St.mode(Laws.Spec.after(K.Key.in(r, S.St.mode(r), "<Esc>"))), T.Normal{}, Keep.mode(r, Laws.Spec.after(K.Key.in(r, S.St.mode(r), "<Esc>"))), Esc.mode(r)))

# the screen after evs and an Esc is the one after evs
def Reach.rows_normal(fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.rows(Laws.Spec.normal(fs, rows, cols, evs)) == Laws.Spec.rows(rows, evs) : Nat}:
  +evs2 = Laws.Spec.snoc(evs, {T.EvKey{"<Esc>"} : T.Ev})
  %RowsGo.snoc(evs, "<Esc>", rows) : {S.St.rows(Laws.Spec.run(fs, rows, cols, evs2)) == Laws.Spec.max(_, 3n) : Nat}
  Reach.rows_run(fs, rows, cols, evs2)

def Reach.cols_normal(fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.cols(Laws.Spec.normal(fs, rows, cols, evs)) == Laws.Spec.cols(cols, evs) : Nat}:
  +evs2 = Laws.Spec.snoc(evs, {T.EvKey{"<Esc>"} : T.Ev})
  %ColsGo.snoc(evs, "<Esc>", cols) : {S.St.cols(Laws.Spec.run(fs, rows, cols, evs2)) == Laws.Spec.max(_, 12n) : Nat}
  Reach.cols_run(fs, rows, cols, evs2)
