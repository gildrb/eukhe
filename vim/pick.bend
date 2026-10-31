# eukhe.com's Neovim: pickers
# ===========================
#
# Opening a picker, its keys, and its float: fff (files, live grep) and
# fzf-lua (buffers, buffer lines). The items are found when the query
# changes and kept in the mode; the float is drawn from them.

import Base
import ./types.bend as T
import ./text.bend as X
import ./buf.bend as B
import ./st.bend as S
import ./core.bend as C
import ./fff.bend as FF
import ./fzf.bend as Z

# the file the window shows, from 1 (0: a folder's listing)
def Pick.cur(t: T.Tgt) -> Nat:
  match t:
    case T.File{i}:
      1n+i
    case T.Dir{path}:
      0n

# every buffer, the current one first (fzf-lua's header)
def Pick.buffers(+s: T.St) -> List<&2, T.Item>:
  +w = S.St.win(s)
  Z.Fzf.buffers(S.St.opened(s), S.St.files(s), S.St.bufs(s), S.St.marks(s), Pick.cur(S.Win.tgt(w)), S.Win.cur(w))

# the lines of file c (from 1) and in lower case
def Pick.lines(+s: T.St, +c: Nat, +q: String) -> List<&2, T.Item>:
  +i = Nat.sub(c, 1n)
  +ls = B.Buf.lines(B.Files.at(S.St.files(s), i))
  +fl = Maybe.default(&2, List<&2, String>, List.get(&2, List<&2, String>, S.St.folded(s), i), Nil{})
  Bool.pick(List<&2, T.Item>, Nat.is_eq(c, 0n), Nil{}, Z.Fzf.lines(ls, fl, i, q))

# what picker k lists for query q
def Pick.items(+s: T.St, k: T.Pick, +q: String) -> List<&2, T.Item>:
  match k:
    case T.FFiles{}:
      FF.Fff.files(S.St.files(s), q)
    case T.FGrep{}:
      FF.Fff.grep(S.St.files(s), S.St.folded(s), q)
    case T.ZBufs{}:
      Z.Fzf.filter(List.drop(&2, T.Item, Pick.buffers(s), 1n), q)
    case T.ZLines{}:
      Pick.lines(s, Pick.cur(S.Win.tgt(S.St.win(s))), q)

# picker k open with query q, its first item selected
def Pick.open(+s: T.St, +k: T.Pick, +q: String) -> T.St:
  +its = Pick.items(s, k, q)
  S.St.set_pend(S.St.set_mode(s, T.Picking{k, q, its, List.length(&2, T.Item, its), 0n, 0n, 0n}), T.NoPend{})

def Pick.is_fff(k: T.Pick) -> Bool:
  match k:
    case T.FFiles{}:
      True{}
    case T.FGrep{}:
      True{}
    case T.ZBufs{}:
      False{}
    case T.ZLines{}:
      False{}

def Pick.is_files(k: T.Pick) -> Bool:
  match k:
    case T.FFiles{}:
      True{}
    case T.FGrep{}:
      False{}
    case T.ZBufs{}:
      False{}
    case T.ZLines{}:
      False{}

def Pick.is_lines(k: T.Pick) -> Bool:
  match k:
    case T.FFiles{}:
      False{}
    case T.FGrep{}:
      False{}
    case T.ZBufs{}:
      False{}
    case T.ZLines{}:
      True{}

def Pick.go.item(+s: T.St, k: T.Pick, m: Maybe<&2, T.Item>) -> T.St:
  match k m:
    case _ None{}:
      s
    case T.FFiles{} Some{T.Item{tgt, pos, text, hits}}:
      C.Win.to(s, Some{Nat.sub(Pick.cur(tgt), 1n)})
    case T.ZBufs{} Some{T.Item{tgt, pos, text, hits}}:
      C.Win.to(s, Some{Nat.sub(Pick.cur(tgt), 1n)})
    case T.FGrep{} Some{T.Item{tgt, pos, text, hits}}:
      C.Win.open(s, tgt, pos)
    case T.ZLines{} Some{T.Item{tgt, pos, text, hits}}:
      C.Win.go(C.Win.jump(s), pos, False{})

# Enter: the selected item opens, the picker closes
def Pick.enter(+s: T.St, +k: T.Pick, its: List<&2, T.Item>, +sel: Nat) -> T.St:
  Pick.go.item(S.St.set_mode(s, T.Normal{}), k, List.get(&2, T.Item, its, sel))

# the selection one down or up: fff wraps around (wrap_around), fzf stops
def Pick.move(+k: T.Pick, +n: Nat, +sel: Nat, +down: Bool) -> Nat:
  +last = Nat.sub(n, 1n)
  +wrap = Pick.is_fff(k)
  Bool.pick(Nat, down, Bool.pick(Nat, Nat.is_ge(sel, last), Bool.pick(Nat, wrap, 0n, last), 1n+sel), Bool.pick(Nat, Nat.is_eq(sel, 0n), Bool.pick(Nat, wrap, last, 0n), Nat.sub(sel, 1n)))

def Pick.geo.pw(g: FF.Geo) -> Nat:
  match g:
    case FF.Geo{row, col, w, h, side, pre, lw, lh, pw, ph}:
      pw

def Pick.geo.ph(g: FF.Geo) -> Nat:
  match g:
    case FF.Geo{row, col, w, h, side, pre, lw, lh, pw, ph}:
      ph

# <C-d> and <C-u> in fff: the preview half its rows down or up
def Pick.scroll(+s: T.St, +k: T.Pick, +its: List<&2, T.Item>, +sel: Nat, +pv: Nat, +down: Bool) -> Nat:
  +g = FF.Fff.geo(S.St.rows(s), S.St.cols(s))
  +half = Nat.div(Pick.geo.ph(g), 2n)
  +top = FF.Fff.ptop(Pick.is_fff(k) && Bool.not(Pick.is_files(k)), S.St.files(s), List.get(&2, T.Item, its, sel), Pick.geo.pw(g), pv)
  1n+Bool.pick(Nat, down, Nat.add(top, half), Nat.sub(top, half))


def Pick.keys() -> List<&2, String>:
  ["<BS>", "<CR>", "<Esc>", "<C-c>", "<Down>", "<C-n>", "<C-j>", "<Up>", "<C-p>", "<C-k>", "<C-d>", "<C-u>"]

def Pick.find(xs: List<&2, String>, +s: String, +n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{x, rest}:
      X.Bool.when(Nat, String.eq(x, s), u => Pick.find(rest, s, 1n+n), u => n)

def Pick.drop1(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{h, t}:
      t

def Pick.char(s: String) -> Bool:
  match s:
    case SCon{h, SNil{}}:
      True{}
    case t:
      False{}

def Pick.special(+s: T.St, +k: T.Pick, +q: String, +its: List<&2, T.Item>, +n: Nat, +sel: Nat, +pv: Nat, key: Nat) -> T.St:
  match key:
    case 0n:
      Pick.open(s, k, String.reverse(Pick.drop1(String.reverse(q))))
    case 1n:
      Pick.enter(s, k, its, sel)
    case 2n:
      S.St.set_mode(s, T.Normal{})
    case 3n:
      S.St.set_mode(s, T.Normal{})
    case 4n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, True{}), 0n, 0n})
    case 5n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, True{}), 0n, 0n})
    case 6n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, True{}), 0n, 0n})
    case 7n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, False{}), 0n, 0n})
    case 8n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, False{}), 0n, 0n})
    case 9n:
      S.St.set_mode(s, T.Picking{k, q, its, n, Pick.move(k, n, sel, False{}), 0n, 0n})
    case 10n:
      Bool.pick(T.St, Pick.is_fff(k), S.St.set_mode(s, T.Picking{k, q, its, n, sel, 0n, Pick.scroll(s, k, its, sel, pv, True{})}), s)
    case 11n:
      Bool.pick(T.St, Pick.is_fff(k), S.St.set_mode(s, T.Picking{k, q, its, n, sel, 0n, Pick.scroll(s, k, its, sel, pv, False{})}), s)
    case 12n+p:
      s



# a key in a picker: a character narrows the list, Backspace widens it,
# the arrows and Ctrl-n/p/j/k move the selection, Enter opens, Esc and
# Ctrl-c close, Ctrl-d/u scroll fff's preview
def Pick.key(+s: T.St, +k: T.Pick, +q: String, +its: List<&2, T.Item>, +n: Nat, +sel: Nat, +pv: Nat, +key: String) -> T.St:
  +ch = Bool.pick(String, String.eq(key, "<Space>"), " ", key)
  X.Bool.when(T.St, Pick.char(ch), u => Pick.special(s, k, q, its, n, sel, pv, Pick.find(Pick.keys(), key, 0n)), u => Pick.open(s, k, String.append(q, ch)))

# The float, the statusline, the cursor
# -------------------------------------

def Pick.text(m: Maybe<&2, T.Item>) -> String:
  match m:
    case None{}:
      ""
    case Some{T.Item{tgt, pos, text, hits}}:
      text


def Pick.float(+s: T.St, +k: T.Pick, +q: String, +its: List<&2, T.Item>, +n: Nat, +sel: Nat, +pv: Nat) -> T.Float:
  +r = S.St.rows(s)
  +c = S.St.cols(s)
  +fs = S.St.files(s)
  +cur = Pick.cur(S.Win.tgt(S.St.win(s)))
  +bufs = Pick.buffers(s)
  X.Bool.when(T.Float, Pick.is_fff(k), u => X.Bool.when(T.Float, Pick.is_lines(k), u => Z.Fzf.float(False{}, fs, S.St.bufs(s), " Buffers ", q, [":: <ctrl-x> to close", Pick.text(List.head(&2, T.Item, bufs))], its, Nat.sub(List.length(&2, T.Item, bufs), 1n), sel, r, c), u => Z.Fzf.float(True{}, fs, S.St.bufs(s), " Buffer Lines ", q, Nil{}, its, B.Lines.len(C.St.lines(s)), sel, r, c)), u => FF.Fff.float(Bool.not(Pick.is_files(k)), fs, q, its, sel, 0n, pv, cur, r, c))

