# eukhe.com's Neovim: keys
# ========================
#
# What each key does in normal mode, after a waiting key (g, z, the
# leader), on the command line and in a picker. Keys are in Vim's
# notation ("j", "<C-d>", "<Space>").

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./move.bend as M
import ./find.bend as F
import ./view.bend as V
import ./st.bend as S
import ./core.bend as C
import ./ex.bend as E
import ./pick.bend as P

# the largest count: a bound on the work of one key
def Key.max_count() -> Nat:
  99999n

def Key.names() -> List<&2, String>:
  ["h", "<Left>", "<BS>", "l", "<Right>", "j", "<Down>", "<C-n>", "<C-j>", "k",
   "<Up>", "<C-p>", "+", "<CR>", "0", "<Home>", "^", "$", "<End>", "w",
   "W", "b", "B", "e", "E", "G", "H", "M", "L", "<C-d>",
   "<C-u>", "<C-f>", "<PageDown>", "<C-b>", "<PageUp>", "<C-e>", "<C-y>", "{", "}", "/",
   "?", ":", "n", "N", "*", "#", "<Esc>", "<C-o>", "<C-i>", "<Tab>",
   "-", "g", "z", "<Space>", "y", "Y", "i", "a", "o", "O",
   "I", "A", "x", "X", "d", "D", "c", "C", "s", "S",
   "r", "R", "p", "P", "J", "~", ".", "<Del>", ">", "<",
   "u", "<C-r>", "<C-^>", "<C-c>", "_"]

# one motion: 0 w, 1 W, 2 b, 3 B, 4 e, 5 E, 6 }, 7 {
def Rep.one(+ls: List<&2, String>, which: Nat, +p: T.Pos) -> T.Pos:
  match which:
    case 0n:
      M.Word.w(ls, p, False{})
    case 1n:
      M.Word.w(ls, p, True{})
    case 2n:
      M.Word.b(ls, p, False{})
    case 3n:
      M.Word.b(ls, p, True{})
    case 4n:
      M.Word.e(ls, p, False{})
    case 5n:
      M.Word.e(ls, p, True{})
    case 6n:
      M.Para.down(ls, S.Pos.line(p))
    case 7n+k:
      M.Para.up(ls, S.Pos.line(p))

# a motion applied n times; it stops early once the cursor stays put
def Rep.go(n: Nat, +ls: List<&2, String>, +which: Nat, +p: T.Pos) -> T.Pos:
  match n:
    case 0n:
      p
    case 1n+k:
      +q = Rep.one(ls, which, p)
      X.Bool.when(T.Pos, S.Pos.eq(q, p), u => Rep.go(k, ls, which, q), u => q)

# the cursor after motion which, n times
def Key.rep(+s: T.St, +n: Nat, +which: Nat, +jump: Bool) -> T.St:
  +p = Rep.go(n, C.St.lines(s), which, S.Win.cur(S.St.win(s)))
  C.Win.go(Bool.pick(T.St, jump, C.Win.jump(s), s), p, False{})

# H M L: a line on screen, within 'scrolloff'
def Key.screen(+s: T.St, +which: Nat, +n: Nat) -> T.St:
  +ls = C.St.lines(s)
  +h = C.St.h(s)
  +last = M.Move.last_line(ls)
  +top = S.Win.top(S.St.win(s))
  +bottom = Nat.min(Nat.add(top, Nat.sub(h, 1n)), last)
  +want = Bool.pick(Nat, Nat.is_eq(which, 0n), Nat.add(top, Nat.sub(n, 1n)), Bool.pick(Nat, Nat.is_eq(which, 2n), Nat.sub(bottom, Nat.sub(n, 1n)), Nat.add(top, Nat.div(Nat.sub(bottom, top), 2n))))
  C.Win.go_line(C.Win.jump(s), V.View.drag(want, top, h, last))

# a key that scrolls: the screen moves first, the cursor stays on screen
def Key.scroll_by(+s: T.St, +down: Bool, +n: Nat, +move: Bool) -> T.St:
  +top = S.Win.top(S.St.win(s))
  +l = C.St.line(s)
  C.Win.scroll(s, Bool.pick(Nat, down, Nat.add(top, n), Nat.sub(top, n)), Bool.pick(Nat, move, Bool.pick(Nat, down, Nat.add(l, n), Nat.sub(l, n)), l))

# zz zt zb: the cursor's line in the middle, at the top, at the bottom
def Key.z(+s: T.St, +which: Nat) -> T.St:
  +ls = C.St.lines(s)
  +h = C.St.h(s)
  +last = M.Move.last_line(ls)
  +l = C.St.line(s)
  +so = V.View.so_in(h)
  +top = Bool.pick(Nat, Nat.is_eq(which, 0n), Nat.sub(l, Nat.div(Nat.sub(h, 1n), 2n)), Bool.pick(Nat, Nat.is_eq(which, 1n), Nat.sub(l, Nat.min(so, l)), Nat.sub(Nat.add(l, Nat.min(so, Nat.sub(last, l))), Nat.sub(h, 1n))))
  C.Win.scroll(s, top, l)

# line k the cursor can be on with the window's first line at top (inside
# 'scrolloff'), its last column at col or past it
def Key.side.fits(+ls: List<&2, String>, +k: Nat, +col: Nat, +top: Nat, +h: Nat, +last: Nat) -> Bool:
  Bool.and(Nat.is_le(k, last), Bool.and(Nat.is_eq(V.View.fit(top, k, h, last), top), Nat.is_ge(M.Move.last_col(ls, k), col)))

# the last column of the longest of the r lines from k that fit
def Key.side.widest(r: Nat, +ls: List<&2, String>, +k: Nat, +top: Nat, +h: Nat, +last: Nat, +acc: Nat) -> Nat:
  match r:
    case 0n:
      acc
    case 1n+p:
      Key.side.widest(p, ls, 1n+k, top, h, last, Bool.pick(Nat, Key.side.fits(ls, k, 0n, top, h, last), Nat.max(acc, M.Move.last_col(ls, k)), acc))

# the line nearest l, d lines away or more, that fits and reaches column
# col (below first on a tie); l when none does within r more steps
def Key.side.line(r: Nat, +ls: List<&2, String>, +l: Nat, +d: Nat, +col: Nat, +top: Nat, +h: Nat, +last: Nat) -> Nat:
  match r:
    case 0n:
      l
    case 1n+p:
      +down = Nat.add(l, d)
      +up = Nat.sub(l, d)
      Bool.pick(Nat, Key.side.fits(ls, down, col, top, h, last), down, Bool.pick(Nat, Bool.and(Nat.is_le(d, l), Key.side.fits(ls, up, col, top, h, last)), up, Key.side.line(p, ls, l, 1n+d, col, top, h, last)))

# zl zh: the view n columns right or left ('nowrap'); the cursor is dragged
# to stay 'sidescrolloff' columns inside, onto the nearest line on screen
# that reaches that far when its own line is short (a finger pans the page,
# as in a terminal); a view never starts past the longest line on screen
def Key.side(+s: T.St, +right: Bool, +n: Nat) -> T.St:
  +ls = C.St.lines(s)
  +w = S.St.win(s)
  +l = C.St.line(s)
  +c = C.St.col(s)
  +top = S.Win.top(w)
  +h = C.St.h(s)
  +last = M.Move.last_line(ls)
  +width = C.St.w(s)
  +so = V.View.so_in(width)
  +widest = Key.side.widest(h, ls, top, top, h, last, 0n)
  +left = Bool.pick(Nat, right, Nat.max(S.Win.left(w), Nat.min(Nat.add(S.Win.left(w), n), Nat.sub(widest, Nat.min(so, widest)))), Nat.sub(S.Win.left(w), n))
  +need = Nat.add(left, so)
  +l2 = Bool.pick(Nat, right, Key.side.line(h, ls, l, 0n, need, top, h, last), l)
  +c2 = Bool.pick(Nat, right, Nat.min(Nat.max(c, need), M.Move.last_col(ls, l2)), Nat.min(c, Nat.sub(Nat.add(left, width), Nat.add(so, 1n))))
  C.Win.settle(S.St.set_win(s, T.Win{S.Win.tgt(w), T.Pos{l2, c2}, T.Col{c2}, top, left}))

def Key.back.to(+s: T.St, +fwd: Bool, ws: List<&2, T.Win>) -> T.St:
  match ws:
    case Nil{}:
      s
    case Con{+w, +rest}:
      +here = S.St.win(s)
      +s2 = C.Win.leave(s)
      +s3 = Bool.pick(T.St, fwd, S.St.set_back(S.St.set_fwd(s2, rest), here <> S.St.back(s2)), S.St.set_fwd(S.St.set_back(s2, rest), here <> S.St.fwd(s2)))
      C.Win.settle(S.St.set_opened(S.St.set_win(s3, w), C.Opened.put(S.St.opened(s3), S.Win.tgt(w))))

# Ctrl-o and Ctrl-i: back and forward through the jumps
def Key.back(+s: T.St, +fwd: Bool) -> T.St:
  Key.back.to(s, fwd, Bool.pick(List<&2, T.Win>, fwd, S.St.fwd(s), S.St.back(s)))

# yy: only the install command copies, on a line that starts with it (the
# README's install line goes on with a `# comment`)
def Key.yank(+s: T.St) -> T.Step:
  +install = E.Vim.install()
  T.Step{s, Bool.pick(T.Act, X.Text.prefix(install, C.St.text(s)), T.CopyText{install}, T.Nothing{})}

def Key.ok(s: T.St) -> T.Step:
  T.Step{s, T.Nothing{}}

# $: the end of line l, and every line after it (want: the end)
def Key.dollar(+s: T.St, +l: Nat) -> T.St:
  +w = S.St.win(s)
  +ls = C.St.lines(s)
  +l2 = Nat.min(l, M.Move.last_line(ls))
  C.Win.settle(S.St.set_win(s, T.Win{S.Win.tgt(w), T.Pos{l2, M.Move.last_col(ls, l2)}, T.End{}, S.Win.top(w), S.Win.left(w)}))

# Ctrl-f and Ctrl-b: n screens down or up
def Key.page(+s: T.St, +down: Bool, +n: Nat) -> T.St:
  +h = C.St.h(s)
  +ls = C.St.lines(s)
  +last = M.Move.last_line(ls)
  +top = S.Win.top(S.St.win(s))
  +by = Nat.mul(n, Nat.max(1n, Nat.sub(h, 2n)))
  +t = Bool.pick(Nat, down, Nat.min(Nat.add(top, by), V.View.max_top(h, last)), Nat.sub(top, by))
  +l = Bool.pick(Nat, down, Nat.max(C.St.line(s), V.View.band_lo(t, h)), Nat.min(C.St.line(s), V.View.band_hi(t, h, last)))
  C.Win.scroll(s, t, l)

# the first non-blank of the line n - 1 below (_, +)
def Key.first(+s: T.St, +l: Nat) -> T.St:
  C.Win.go(s, T.Pos{l, X.Text.first(B.Lines.at(C.St.lines(s), l))}, False{})

# keys 56 on: changes (the editor is read-only), u, Ctrl-r, Ctrl-^,
# Ctrl-c (Oil: back to the file), _ (Oil: the root)
def Key.normal.hi(+s: T.St, k: Nat, +n: Nat) -> T.Step:
  match k:
    case 24n:
      Key.ok(E.Msg.say(s, "Already at oldest change"))
    case 25n:
      Key.ok(E.Msg.say(s, "Already at newest change"))
    case 26n:
      Key.ok(C.Win.alt(s))
    case 27n:
      Key.ok(Bool.pick(T.St, C.St.on_file(s), s, C.Win.alt(s)))
    case 28n:
      Key.ok(X.Bool.when(T.St, C.St.on_file(s), u => C.Oil.root(s), u => Key.first(s, Nat.add(C.St.line(s), Nat.sub(n, 1n)))))
    case 29n+p:
      Key.ok(s)
    case _:
      Key.ok(E.Msg.say(s, E.Msg.e21()))

def Key.normal.at(+s: T.St, k: Nat, +n: Nat, +n0: Nat) -> T.Step:
  match k:
    case 0n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), Nat.sub(C.St.col(s), n)}, False{}))
    case 1n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), Nat.sub(C.St.col(s), n)}, False{}))
    case 2n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), Nat.sub(C.St.col(s), n)}, False{}))
    case 3n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), Nat.add(C.St.col(s), n)}, False{}))
    case 4n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), Nat.add(C.St.col(s), n)}, False{}))
    case 5n:
      Key.ok(C.Win.go_line(s, Nat.add(C.St.line(s), n)))
    case 6n:
      Key.ok(C.Win.go_line(s, Nat.add(C.St.line(s), n)))
    case 7n:
      Key.ok(C.Win.go_line(s, Nat.add(C.St.line(s), n)))
    case 8n:
      Key.ok(C.Win.go_line(s, Nat.add(C.St.line(s), n)))
    case 9n:
      Key.ok(C.Win.go_line(s, Nat.sub(C.St.line(s), n)))
    case 10n:
      Key.ok(C.Win.go_line(s, Nat.sub(C.St.line(s), n)))
    case 11n:
      Key.ok(C.Win.go_line(s, Nat.sub(C.St.line(s), n)))
    case 12n:
      Key.ok(Key.first(s, Nat.add(C.St.line(s), n)))
    case 13n:
      Key.ok(E.Oil.enter(s, n))
    case 14n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), 0n}, False{}))
    case 15n:
      Key.ok(C.Win.go(s, T.Pos{C.St.line(s), 0n}, False{}))
    case 16n:
      Key.ok(Key.first(s, C.St.line(s)))
    case 17n:
      Key.ok(Key.dollar(s, Nat.add(C.St.line(s), Nat.sub(n, 1n))))
    case 18n:
      Key.ok(Key.dollar(s, Nat.add(C.St.line(s), Nat.sub(n, 1n))))
    case 19n:
      Key.ok(Key.rep(s, n, 0n, False{}))
    case 20n:
      Key.ok(Key.rep(s, n, 1n, False{}))
    case 21n:
      Key.ok(Key.rep(s, n, 2n, False{}))
    case 22n:
      Key.ok(Key.rep(s, n, 3n, False{}))
    case 23n:
      Key.ok(Key.rep(s, n, 4n, False{}))
    case 24n:
      Key.ok(Key.rep(s, n, 5n, False{}))
    case 25n:
      Key.ok(C.Win.go_line(C.Win.jump(s), Bool.pick(Nat, Nat.is_eq(n0, 0n), M.Move.last_line(C.St.lines(s)), Nat.sub(n0, 1n))))
    case 26n:
      Key.ok(Key.screen(s, 0n, n))
    case 27n:
      Key.ok(Key.screen(s, 1n, n))
    case 28n:
      Key.ok(Key.screen(s, 2n, n))
    case 29n:
      Key.ok(Key.scroll_by(s, True{}, Bool.pick(Nat, Nat.is_eq(n0, 0n), Nat.div(C.St.h(s), 2n), n0), True{}))
    case 30n:
      Key.ok(Key.scroll_by(s, False{}, Bool.pick(Nat, Nat.is_eq(n0, 0n), Nat.div(C.St.h(s), 2n), n0), True{}))
    case 31n:
      Key.ok(Key.page(s, True{}, n))
    case 32n:
      Key.ok(Key.page(s, True{}, n))
    case 33n:
      Key.ok(Key.page(s, False{}, n))
    case 34n:
      Key.ok(Key.page(s, False{}, n))
    case 35n:
      Key.ok(Key.scroll_by(s, True{}, n, False{}))
    case 36n:
      Key.ok(Key.scroll_by(s, False{}, n, False{}))
    case 37n:
      Key.ok(Key.rep(s, n, 7n, True{}))
    case 38n:
      Key.ok(Key.rep(s, n, 6n, True{}))
    case 39n:
      Key.ok(S.St.set_mode(s, T.Typing{T.Slash{}, ""}))
    case 40n:
      Key.ok(S.St.set_mode(s, T.Typing{T.Quest{}, ""}))
    case 41n:
      Key.ok(S.St.set_mode(s, T.Typing{T.Colon{}, ""}))
    case 42n:
      Key.ok(E.Search.again(s, False{}))
    case 43n:
      Key.ok(E.Search.again(s, True{}))
    case 44n:
      Key.ok(E.Search.star(s, False{}))
    case 45n:
      Key.ok(E.Search.star(s, True{}))
    case 46n:
      Key.ok(S.St.set_hl(s, False{}))
    case 47n:
      Key.ok(Key.back(s, False{}))
    case 48n:
      Key.ok(Key.back(s, True{}))
    case 49n:
      Key.ok(Key.back(s, True{}))
    case 50n:
      Key.ok(C.Oil.here(s))
    case 51n:
      Key.ok(S.St.set_count(S.St.set_pend(s, T.PendG{}), n0))
    case 52n:
      Key.ok(S.St.set_count(S.St.set_pend(s, T.PendZ{}), n0))
    case 53n:
      Key.ok(S.St.set_pend(s, T.PendLead{}))
    case 54n:
      Key.ok(S.St.set_pend(s, T.PendY{}))
    case 55n:
      Key.yank(s)
    case 56n+p:
      Key.normal.hi(s, p, n)

# key number k of Key.names() in normal mode, count n0 (0: none)
def Key.normal(+s: T.St, k: Nat, +n0: Nat) -> T.Step:
  Key.normal.at(s, k, Nat.max(n0, 1n), n0)

# A key after another
# -------------------

def Key.g.at(+s: T.St, k: Nat, +n0: Nat) -> T.Step:
  match k:
    case 0n:
      Key.ok(C.Win.go_line(C.Win.jump(s), Nat.sub(n0, 1n)))
    case 1n:
      E.Link.gx(s)
    case 2n:
      Key.ok(E.Link.gf(s))
    case 3n:
      Key.normal(s, 5n, n0)
    case 4n:
      Key.normal(s, 9n, n0)
    case 5n:
      Key.normal(s, 14n, n0)
    case 6n:
      Key.normal(s, 16n, n0)
    case 7n:
      Key.normal(s, 17n, n0)
    case 8n:
      Key.normal(s, 16n, n0)
    case 9n+p:
      Key.ok(s)

# g then key
def Key.g(+s: T.St, +key: String, +n0: Nat) -> T.Step:
  Key.g.at(s, E.Ex.find(["g", "x", "f", "j", "k", "0", "^", "$", "_"], key, 0n), n0)

# z then key (zz zt zb, z. z<CR> z-, zl zh with a count)
def Key.zkey(+s: T.St, +key: String, +n0: Nat) -> T.St:
  +k = E.Ex.find(["z", ".", "t", "<CR>", "b", "-", "l", "<Right>", "h", "<Left>"], key, 0n)
  +n = Nat.max(n0, 1n)
  Bool.pick(T.St, Nat.is_lt(k, 2n), Key.z(s, 0n), Bool.pick(T.St, Nat.is_lt(k, 4n), Key.z(s, 1n), Bool.pick(T.St, Nat.is_lt(k, 6n), Key.z(s, 2n), Bool.pick(T.St, Nat.is_lt(k, 8n), Key.side(s, True{}, n), Bool.pick(T.St, Nat.is_lt(k, 10n), Key.side(s, False{}, n), s)))))

def Key.lead.at(+s: T.St, k: Nat) -> T.St:
  match k:
    case 0n:
      C.Oil.here(s)
    case 1n:
      P.Pick.open(s, T.FFiles{}, "")
    case 2n:
      S.St.set_pend(s, T.PendLeadF{})
    case 3n:
      P.Pick.open(s, T.ZLines{}, "")
    case 4n:
      E.Msg.say(s, E.Msg.e444())
    case 5n:
      E.Msg.say(s, E.Msg.e444())
    case 6n:
      E.Msg.say(s, E.Msg.e45())
    case 7n+p:
      s

# the leader (Space) then key
def Key.lead(+s: T.St, +key: String) -> T.St:
  Key.lead.at(s, E.Ex.find(["e", "<Space>", "f", "/", "q", "Q", "w"], key, 0n))

def Key.leadf.at(+s: T.St, k: Nat) -> T.St:
  match k:
    case 0n:
      P.Pick.open(s, T.FFiles{}, "")
    case 1n:
      P.Pick.open(s, T.FGrep{}, "")
    case 2n:
      P.Pick.open(s, T.FGrep{}, F.Word.at(C.St.text(s), C.St.col(s)))
    case 3n:
      P.Pick.open(s, T.ZBufs{}, "")
    case 4n+p:
      s

# leader f then key
def Key.leadf(+s: T.St, +key: String) -> T.St:
  Key.leadf.at(s, E.Ex.find(["f", "g", "w", "b"], key, 0n))

# A key in each mode
# ------------------

def Count.add(+n: Nat, d: Nat) -> Nat:
  Nat.min(Nat.add(Nat.mul(n, 10n), d), Key.max_count())

def Key.idle(p: T.Pend) -> Bool:
  match p:
    case T.NoPend{}:
      True{}
    case T.PendG{}:
      False{}
    case T.PendZ{}:
      False{}
    case T.PendLead{}:
      False{}
    case T.PendLeadF{}:
      False{}
    case T.PendY{}:
      False{}

def Key.pend(+s: T.St, p: T.Pend, +key: String, +n0: Nat) -> T.Step:
  match p:
    case T.NoPend{}:
      Key.normal(s, E.Ex.find(Key.names(), key, 0n), n0)
    case T.PendG{}:
      Key.g(s, key, n0)
    case T.PendZ{}:
      Key.ok(Key.zkey(s, key, n0))
    case T.PendLead{}:
      Key.ok(Key.lead(s, key))
    case T.PendLeadF{}:
      Key.ok(Key.leadf(s, key))
    case T.PendY{}:
      Bool.pick(T.Step, String.eq(key, "y"), Key.yank(s), Key.ok(s))

# a key in normal mode: a count's digit, the key after a waiting one, or a
# key of its own; the command line keeps its message (as Neovim does)
def Key.in_normal(+s: T.St, +key: String) -> T.Step:
  +n0 = S.St.count(s)
  +d = E.Ex.find(["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"], key, 0n)
  +digit = Bool.and(Nat.is_lt(d, 10n), Bool.or(Nat.is_gt(d, 0n), Nat.is_gt(n0, 0n)))
  X.Bool.when(T.Step, Bool.and(digit, Key.idle(S.St.pend(s))), u => Key.pend(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), S.St.pend(s), key, n0), u => Key.ok(S.St.set_count(s, Count.add(n0, d))))

def Key.special(+s: T.St, +kind: T.Line, +text: String, k: Nat) -> T.Step:
  match k:
    case 0n:
      Key.ok(Bool.pick(T.St, String.is_empty(text), S.St.set_mode(s, T.Normal{}), S.St.set_mode(s, T.Typing{kind, String.reverse(P.Pick.drop1(String.reverse(text)))})))
    case 1n:
      Key.ok(E.Line.run(S.St.set_mode(s, T.Normal{}), kind, text))
    case 2n:
      Key.ok(S.St.set_mode(s, T.Normal{}))
    case 3n:
      Key.ok(S.St.set_mode(s, T.Normal{}))
    case 4n+p:
      Key.ok(s)

# the command line takes a key: a character, Backspace (on an empty line,
# it closes), Enter (it runs), Esc (it closes)
def Key.typing(+s: T.St, +kind: T.Line, +text: String, +key: String) -> T.Step:
  +ch = Bool.pick(String, String.eq(key, "<Space>"), " ", key)
  X.Bool.when(T.Step, P.Pick.char(ch), u => Key.special(s, kind, text, E.Ex.find(["<BS>", "<CR>", "<Esc>", "<C-c>"], key, 0n)), u => Key.ok(S.St.set_mode(s, T.Typing{kind, String.append(text, ch)})))

def Key.in(+s: T.St, m: T.Mode, +key: String) -> T.Step:
  match m:
    case T.Normal{}:
      Key.in_normal(s, key)
    case T.Typing{kind, text}:
      Key.typing(s, kind, text, key)
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      Key.ok(P.Pick.key(s, kind, q, its, n, sel, pv, levels, key))
