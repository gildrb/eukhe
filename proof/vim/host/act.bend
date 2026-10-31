# eukhe.com's Neovim: what the host is asked to do (R7)
# =====================================================
#
# Host.good(fs, a): the act is honest (copies only the install command,
# opens only a URL in a file) and asks for a web address. Every step's
# act comes from Key.in: Nothing, Key.yank's CopyText (only when the line
# is the install command) or Link.gx's OpenUrl (only on a file window,
# when the WORD's target starts "http(s)://": a run of the cursor's line,
# a line of a file of fs).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/ex.bend as E
import ../../../vim/pick.bend as P
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/reach.bend as Re
import ../screen/base.bend as Sc
import ../buffers/real.bend as Rb
import ./base.bend as H

def Host.good(+fs: List<&2, T.Buf>, +a: T.Act) -> Bool:
  Bool.and(Laws.Spec.honest(fs, a), Laws.Spec.url_ok(fs, a))

def Good(+fs: List<&2, T.Buf>, +a: T.Act) -> Type:
  {Host.good(fs, a) == True{} : Bool}

# Web addresses
# -------------

# a web address is not empty
def Url.ne(u: String, h: {E.Link.is_url(u) == True{} : Bool}) -> {String.is_empty(u) == False{} : Bool}:
  match u:
    case SNil{}:
      L.Bool.false_true({String.is_empty(SNil{}) == False{} : Bool}, h)
    case SCon{c, t}:
      {==}

# gx's test is the spec's
def Url.spec(+u: String) -> {E.Link.is_url(u) == Bool.or(Laws.Spec.prefix("https://", u), Laws.Spec.prefix("http://", u)) : Bool}:
  %Rb.Prefix.eq("https://", u) : {E.Link.is_url(u) == Bool.or(_, Laws.Spec.prefix("http://", u)) : Bool}
  %Rb.Prefix.eq("http://", u) : {E.Link.is_url(u) == Bool.or(X.Text.prefix("https://", u), _) : Bool}
  {==}

# Lines of the files
# ------------------

def Or.false(a: Bool, -G: Type, h: {Bool.or(a, False{}) == True{} : Bool}, ne: {a == False{} : Bool}) -> G:
  match a:
    case True{}:
      L.Bool.true_false(G, ne)
    case False{}:
      L.Bool.false_true(G, h)

# a nonempty run of line l of ls is in ls
def In.at(+u: String, ls: List<&2, String>, l: Nat, ne: {String.is_empty(u) == False{} : Bool}, hw: {Laws.Spec.within(u, B.Lines.at(ls, l)) == True{} : Bool}) -> {Laws.Spec.in_lines(u, ls) == True{} : Bool}:
  match ls l:
    case Nil{} _:
      L.Bool.both({Laws.Spec.in_lines(u, Nil{}) == True{} : Bool}, String.is_empty(u), hw, ne)
    case Con{+h, +t} 0n:
      L.Or.l(Laws.Spec.within(u, h), Laws.Spec.in_lines(u, t), hw)
    case Con{+h, +t} 1n+p:
      L.Or.r(Laws.Spec.within(u, h), Laws.Spec.in_lines(u, t), In.at(u, t, p, ne, hw))

def In.some(+u: String, ls: List<&2, String>, ne: {String.is_empty(u) == False{} : Bool}, h: {Laws.Spec.in_lines(u, Laws.Spec.some(ls)) == True{} : Bool}) -> {Laws.Spec.in_lines(u, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      Or.false(String.is_empty(u), {Laws.Spec.in_lines(u, Nil{}) == True{} : Bool}, h, ne)
    case Con{hd, tl}:
      h

# a nonempty string in the lines of file i of fs is in fs
def In.file(+u: String, fs: List<&2, T.Buf>, i: Nat, ne: {String.is_empty(u) == False{} : Bool}, hl: {Laws.Spec.in_lines(u, Laws.Spec.file(fs, i)) == True{} : Bool}) -> {Laws.Spec.in_files(u, fs) == True{} : Bool}:
  match fs i:
    case Nil{} _:
      Or.false(String.is_empty(u), {Laws.Spec.in_files(u, Nil{}) == True{} : Bool}, hl, ne)
    case Con{T.Buf{+path, +lines}, +t} 0n:
      L.Or.l(Laws.Spec.in_lines(u, lines), Laws.Spec.in_files(u, t), In.some(u, lines, ne, hl))
    case Con{T.Buf{+path, +lines}, +t} 1n+p:
      L.Or.r(Laws.Spec.in_lines(u, lines), Laws.Spec.in_files(u, t), In.file(u, t, p, ne, hl))

# gx
# --

def Gx.act(+fs: List<&2, T.Buf>, +t: String, -s2: T.St, -s1: T.St, b: Bool, +e: {E.Link.is_url(t) == b : Bool}, hin: {String.is_empty(t) == False{} : Bool} -> {Laws.Spec.in_files(t, fs) == True{} : Bool})
  -> Good(fs, Laws.Spec.act(X.Bool.when(T.Step, b, u => T.Step{s2, T.Nothing{}}, u => T.Step{s1, T.OpenUrl{t}}))):
  match b:
    case True{}:
      +hi = hin(Url.ne(t, e))
      +web = Bool.or(Laws.Spec.prefix("https://", t), Laws.Spec.prefix("http://", t))
      hu = Equal.trans(Bool, web, E.Link.is_url(t), True{}, Equal.sym(Bool, E.Link.is_url(t), web, Url.spec(t)), e)
      L.And.intro(Laws.Spec.in_files(t, fs), Bool.and(web, Laws.Spec.in_files(t, fs)), hi, L.And.intro(web, Laws.Spec.in_files(t, fs), hu, hi))
    case False{}:
      {==}

# what gx opens on file i is in fs
def Gx.in(+fs: List<&2, T.Buf>, +files: List<&2, T.Buf>, +i: Nat, +l: Nat, +c: Nat, hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +ne: {String.is_empty(E.Link.target(E.Link.big(B.Lines.at(B.Lines.some(B.Buf.lines(B.Files.at(files, i))), l), c))) == False{} : Bool})
  -> {Laws.Spec.in_files(E.Link.target(E.Link.big(B.Lines.at(B.Lines.some(B.Buf.lines(B.Files.at(files, i))), l), c)), fs) == True{} : Bool}:
  -ls = B.Lines.some(B.Buf.lines(B.Files.at(files, i)))
  -line = B.Lines.at(ls, l)
  +t = E.Link.target(E.Link.big(B.Lines.at(B.Lines.some(B.Buf.lines(B.Files.at(files, i))), l), c))
  hw = H.Sub.within(t, line, H.Gx.sub(B.Lines.at(B.Lines.some(B.Buf.lines(B.Files.at(files, i))), l), c))
  +hl = In.at(t, B.Lines.some(B.Buf.lines(B.Files.at(files, i))), l, ne, hw)
  ef = Equal.cong(List<&2, String>, Bool, xs => Laws.Spec.in_lines(t, xs), Laws.Spec.file(fs, i), ls, Sc.Files.spec(fs, files, i, hf))
  In.file(t, fs, i, ne, Equal.trans(Bool, Laws.Spec.in_lines(t, Laws.Spec.file(fs, i)), Laws.Spec.in_lines(t, ls), True{}, ef, hl))

def Gx.good(+fs: List<&2, T.Buf>, x: T.St, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(E.Link.gx(x))):
  match x:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              +x0 = {T.St{files, folded, dirs, T.Win{T.File{i}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
              +t = E.Link.target(E.Link.big(C.St.text(x0), C.St.col(x0)))
              Gx.act(fs, t, E.Link.gf(x0), x0, E.Link.is_url(t), {==}, ne => Gx.in(fs, files, i, S.Pos.line(cur), S.Pos.col(cur), hf, ne))

# yy
# --

def Yank.good(+fs: List<&2, T.Buf>, +line: String, -s: T.St, b: Bool, e: {String.eq(line, E.Vim.install()) == b : Bool})
  -> Good(fs, Laws.Spec.act(T.Step{s, Bool.pick(T.Act, b, T.CopyText{line}, T.Nothing{})})):
  match b:
    case True{}:
      %Equal.sym(Bool, String.eq(line, E.Vim.install()), True{}, e) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case False{}:
      {==}

def Yank.of(+fs: List<&2, T.Buf>, +x: T.St) -> Good(fs, Laws.Spec.act(K.Key.yank(x))):
  Yank.good(fs, C.St.text(x), x, String.eq(C.St.text(x), E.Vim.install()), {==})

# Keys
# ----

def Hi.good(+fs: List<&2, T.Buf>, +x: T.St, k: Nat, +n: Nat) -> Good(fs, Laws.Spec.act(K.Key.normal.hi(x, k, n))):
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n+p:
      {==}

def Normal.good(+fs: List<&2, T.Buf>, +x: T.St, k: Nat, +n: Nat, +n0: Nat) -> Good(fs, Laws.Spec.act(K.Key.normal.at(x, k, n, n0))):
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n:
      {==}
    case 17n:
      {==}
    case 18n:
      {==}
    case 19n:
      {==}
    case 20n:
      {==}
    case 21n:
      {==}
    case 22n:
      {==}
    case 23n:
      {==}
    case 24n:
      {==}
    case 25n:
      {==}
    case 26n:
      {==}
    case 27n:
      {==}
    case 28n:
      {==}
    case 29n:
      {==}
    case 30n:
      {==}
    case 31n:
      {==}
    case 32n:
      {==}
    case 33n:
      {==}
    case 34n:
      {==}
    case 35n:
      {==}
    case 36n:
      {==}
    case 37n:
      {==}
    case 38n:
      {==}
    case 39n:
      {==}
    case 40n:
      {==}
    case 41n:
      {==}
    case 42n:
      {==}
    case 43n:
      {==}
    case 44n:
      {==}
    case 45n:
      {==}
    case 46n:
      {==}
    case 47n:
      {==}
    case 48n:
      {==}
    case 49n:
      {==}
    case 50n:
      {==}
    case 51n:
      {==}
    case 52n:
      {==}
    case 53n:
      {==}
    case 54n:
      {==}
    case 55n:
      Yank.of(fs, x)
    case 56n+p:
      Hi.good(fs, x, p, n)

def G.good(+fs: List<&2, T.Buf>, +x: T.St, k: Nat, +n0: Nat, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(K.Key.g.at(x, k, n0))):
  match k:
    case 0n:
      {==}
    case 1n:
      Gx.good(fs, x, hf)
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n+p:
      {==}

def Reset.files(x: T.St) -> {S.St.files(S.St.set_count(S.St.set_pend(x, T.NoPend{}), 0n)) == S.St.files(x) : List<&2, T.Buf>}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Pend.good(+fs: List<&2, T.Buf>, +x: T.St, p: T.Pend, +key: String, +n0: Nat, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(K.Key.pend(x, p, key, n0))):
  match p:
    case T.NoPend{}:
      Normal.good(fs, x, E.Ex.find(K.Key.names(), key, 0n), Nat.max(n0, 1n), n0)
    case T.PendG{}:
      G.good(fs, x, E.Ex.find(["g", "x", "f", "j", "k", "0", "^", "$", "_"], key, 0n), n0, hf)
    case T.PendZ{}:
      {==}
    case T.PendLead{}:
      {==}
    case T.PendLeadF{}:
      {==}
    case T.PendY{}:
      H.Pick.both(T.Step, r => Good(fs, Laws.Spec.act(r)), String.eq(key, "y"), K.Key.yank(x), K.Key.ok(x), Yank.of(fs, x), {==})

def In.normal(+fs: List<&2, T.Buf>, +x: T.St, +key: String, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(K.Key.in_normal(x, key))):
  +n0 = S.St.count(x)
  +d = E.Ex.find(["0", "1", "2", "3", "4", "5", "6", "7", "8", "9"], key, 0n)
  +digit = Bool.and(Nat.is_lt(d, 10n), Bool.or(Nat.is_gt(d, 0n), Nat.is_gt(n0, 0n)))
  +x2 = S.St.set_count(S.St.set_pend(x, T.NoPend{}), 0n)
  hf2 = Equal.trans(List<&2, T.Buf>, S.St.files(x2), S.St.files(x), B.Files.some(fs, Nil{}), Reset.files(x), hf)
  pf = Pend.good(fs, x2, S.St.pend(x), key, n0, hf2)
  H.When.both(T.Step, r => Good(fs, Laws.Spec.act(r)), Bool.and(digit, K.Key.idle(S.St.pend(x))), u => K.Key.pend(x2, S.St.pend(x), key, n0), u => K.Key.ok(S.St.set_count(x, K.Count.add(n0, d))), pf, {==})

def Special.good(+fs: List<&2, T.Buf>, +x: T.St, +kind: T.Line, +text: String, k: Nat) -> Good(fs, Laws.Spec.act(K.Key.special(x, kind, text, k))):
  match k:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+p:
      {==}

def Typing.good(+fs: List<&2, T.Buf>, +x: T.St, +kind: T.Line, +text: String, +key: String) -> Good(fs, Laws.Spec.act(K.Key.typing(x, kind, text, key))):
  +ch = Bool.pick(String, String.eq(key, "<Space>"), " ", key)
  +k = E.Ex.find(["<BS>", "<CR>", "<Esc>", "<C-c>"], key, 0n)
  H.When.both(T.Step, r => Good(fs, Laws.Spec.act(r)), P.Pick.char(ch), u => K.Key.special(x, kind, text, k), u => K.Key.ok(S.St.set_mode(x, T.Typing{kind, String.append(text, ch)})), Special.good(fs, x, kind, text, k), {==})

def In.good(+fs: List<&2, T.Buf>, +x: T.St, m: T.Mode, +key: String, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(K.Key.in(x, m, key))):
  match m:
    case T.Normal{}:
      In.normal(fs, x, key, hf)
    case T.Typing{+kind, +text}:
      Typing.good(fs, x, kind, text, key)
    case T.Picking{kind, q, its, n, sel, top, pv, levels}:
      {==}

# Steps
# -----

def Done.act(-s: T.St, r: T.Step) -> {Laws.Spec.act(Vim.Vim.done(s, r)) == Laws.Spec.act(r) : T.Act}:
  match r:
    case T.Step{st, a}:
      {==}

# every step asks the host only for what the files hold
def Step.good(+fs: List<&2, T.Buf>, +s: T.St, e: T.Ev, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> Good(fs, Laws.Spec.act(Vim.Vim.step(s, e))):
  match e:
    case T.EvKey{+name}:
      +r = K.Key.in(s, S.St.mode(s), name)
      %Equal.sym(T.Act, Laws.Spec.act(Vim.Vim.done(s, r)), Laws.Spec.act(r), Done.act(s, r)) : Good(fs, _)
      In.good(fs, s, S.St.mode(s), name, hf)
    case T.EvClick{row, col}:
      {==}
    case T.EvWheel{down, notches}:
      {==}
    case T.EvSize{rows, cols}:
      {==}

# the next step after any events
def Host.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, e: T.Ev) -> Good(fs, Laws.Spec.act(Vim.Vim.step(Laws.Spec.run(fs, rows, cols, evs), e))):
  Step.good(fs, Laws.Spec.run(fs, rows, cols, evs), e, Re.Reach.files_run(fs, rows, cols, evs))
