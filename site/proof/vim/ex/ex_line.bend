# eukhe.com's Neovim: the proof of LAW ex_line
# ============================================
#
# ":5<CR>" from normal mode with no waiting key: ":" opens the command
# line, "5" types, Enter runs Ex.run, which reads the number 5 and sends
# the cursor to line 4 (Win.go_line: at most the last line). The window
# shows a real buffer, so Vim.final keeps its target at every step and
# only re-settles (ExLine.rf); the files, listings and target stay (Same),
# so the lines stay; the cursor's line ends min(4, last), and the frame
# reads it back (top <= line in a settled window).
#
# Each step is a lemma over an abstract editor: unfolding the three steps
# at once does not terminate in reasonable time.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/view.bend as V
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/ex.bend as ExLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/text.bend as Tx
import ../../base/reach.bend as Re
import ../screen/base.bend as Sc
import ../screen/parts.bend as Pa
import ../buffers/real.bend as Rb
import ./base.bend as Eb

# Settling
# --------

# Vim.final of an editor on a real buffer: its window only re-settled
def ExLine.rf(+y: T.St) -> T.St:
  Vim.Vim.fit(S.St.set_count(S.St.set_pend(y, Vim.Vim.pend(S.St.mode(y), S.St.pend(y))), Vim.Vim.count(S.St.mode(y), S.St.count(y))))

def ExLine.real(y: T.St, hr: {B.Tgt.real(S.St.files(y), S.Win.tgt(S.St.win(y))) == True{} : Bool}) -> {Vim.Vim.final(y) == ExLine.rf(y) : T.St}:
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          +w = {T.Win{tgt, cur, want, top, left} : T.Win}
          +w0 = {T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n} : T.Win}
          %Equal.sym(Bool, B.Tgt.real(files, tgt), True{}, hr) : {Vim.Vim.fit(T.St{files, folded, dirs, Bool.pick(T.Win, _, w, w0), marks, spots, opened, bufs, back, fwd, mode, Vim.Vim.count(mode, count), Vim.Vim.pend(mode, pend), find, hl, opts, rows, cols, msg, stat}) == ExLine.rf(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}) : T.St}
          {==}

# x and z hold the same files and listings, and show the same target
def ExLine.Same(+x: T.St, +z: T.St) -> Data:
  Fi.And2({S.St.files(x) == S.St.files(z) : List<&2, T.Buf>}, Fi.And2({S.St.dirs(x) == S.St.dirs(z) : List<&2, T.Listing>}, {S.Win.tgt(S.St.win(x)) == S.Win.tgt(S.St.win(z)) : T.Tgt}))

def Same.trans(-x: T.St, -y: T.St, -z: T.St, a: ExLine.Same(x, y), b: ExLine.Same(y, z)) -> ExLine.Same(x, z):
  (af, ar) = a
  (ad, at) = ar
  (bf, br) = b
  (bd, bt) = br
  (Equal.trans(List<&2, T.Buf>, S.St.files(x), S.St.files(y), S.St.files(z), af, bf), (Equal.trans(List<&2, T.Listing>, S.St.dirs(x), S.St.dirs(y), S.St.dirs(z), ad, bd), Equal.trans(T.Tgt, S.Win.tgt(S.St.win(x)), S.Win.tgt(S.St.win(y)), S.Win.tgt(S.St.win(z)), at, bt)))

def Same.tgt_of(-x: T.St, -z: T.St, sm: ExLine.Same(x, z)) -> {S.Win.tgt(S.St.win(x)) == S.Win.tgt(S.St.win(z)) : T.Tgt}:
  (sf, sr) = sm
  (sd, st) = sr
  st

# a target real over z's files is real over x's
def Same.real(-x: T.St, -z: T.St, sm: ExLine.Same(x, z), hr: {B.Tgt.real(S.St.files(z), S.Win.tgt(S.St.win(z))) == True{} : Bool}) -> {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool}:
  (sf, sr) = sm
  (sd, st) = sr
  %Equal.sym(List<&2, T.Buf>, S.St.files(x), S.St.files(z), sf) : {B.Tgt.real(_, S.Win.tgt(S.St.win(x))) == True{} : Bool}
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(x)), S.Win.tgt(S.St.win(z)), st) : {B.Tgt.real(S.St.files(z), _) == True{} : Bool}
  hr

def At.same(-x: T.St, -z: T.St, t: T.Tgt, hf: {S.St.files(x) == S.St.files(z) : List<&2, T.Buf>}, hd: {S.St.dirs(x) == S.St.dirs(z) : List<&2, T.Listing>}) -> {C.St.lines.at(x, t) == C.St.lines.at(z, t) : List<&2, String>}:
  match t:
    case T.File{+i}:
      %Equal.sym(List<&2, T.Buf>, S.St.files(x), S.St.files(z), hf) : {B.Buf.lines(B.Files.at(_, i)) == B.Buf.lines(B.Files.at(S.St.files(z), i)) : List<&2, String>}
      {==}
    case T.Dir{+path}:
      %Equal.sym(List<&2, T.Buf>, S.St.files(x), S.St.files(z), hf) : {Maybe.default(&2, List<&2, String>, C.Listing.find(S.St.dirs(x), path), B.Oil.list(_, path)) == Maybe.default(&2, List<&2, String>, C.Listing.find(S.St.dirs(z), path), B.Oil.list(S.St.files(z), path)) : List<&2, String>}
      %Equal.sym(List<&2, T.Listing>, S.St.dirs(x), S.St.dirs(z), hd) : {Maybe.default(&2, List<&2, String>, C.Listing.find(_, path), B.Oil.list(S.St.files(z), path)) == Maybe.default(&2, List<&2, String>, C.Listing.find(S.St.dirs(z), path), B.Oil.list(S.St.files(z), path)) : List<&2, String>}
      {==}

# the same files, listings and target: the same lines
def Lines.same(+x: T.St, +z: T.St, sm: ExLine.Same(x, z)) -> {C.St.lines(x) == C.St.lines(z) : List<&2, String>}:
  (sf, sr) = sm
  (sd, st) = sr
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(x)), S.Win.tgt(S.St.win(z)), st) : {B.Lines.some(C.St.lines.at(x, _)) == C.St.lines(z) : List<&2, String>}
  Equal.cong(List<&2, String>, List<&2, String>, ls => B.Lines.some(ls), C.St.lines.at(x, S.Win.tgt(S.St.win(z))), C.St.lines.at(z, S.Win.tgt(S.St.win(z))), At.same(x, z, S.Win.tgt(S.St.win(z)), sf, sd))

def Fit.same(+y: T.St) -> ExLine.Same(ExLine.rf(y), y):
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      ({==}, ({==}, {==}))

def Fit.mode(+y: T.St) -> {S.St.mode(ExLine.rf(y)) == S.St.mode(y) : T.Mode}:
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      {==}

# settling pulls the cursor's line onto the text
def Fit.line(+y: T.St) -> {C.St.line(ExLine.rf(y)) == Nat.min(C.St.line(y), M.Move.last_line(C.St.lines(y))) : Nat}:
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              match cur:
                case T.Pos{+line, +col}:
                  {==}
            case T.Dir{+path}:
              match cur:
                case T.Pos{+line, +col}:
                  {==}

def Fit.final(+y: T.St) -> Fi.Final(ExLine.rf(y)):
  Fi.Final.of_fit(S.St.set_count(S.St.set_pend(y, Vim.Vim.pend(S.St.mode(y), S.St.pend(y))), Vim.Vim.count(S.St.mode(y), S.St.count(y))))

# Steps
# -----

# the editor key k leaves before Vim.keep and Vim.final
def ExLine.st(+x: T.St, +k: String) -> T.St:
  Laws.Spec.after(K.Key.in(x, S.St.mode(x), k))

def Keep.tgt(+s: T.St, st: T.St) -> {S.Win.tgt(S.St.win(Vim.Vim.keep(s, st))) == S.Win.tgt(S.St.win(st)) : T.Tgt}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.line(+s: T.St, st: T.St) -> {C.St.line(Vim.Vim.keep(s, st)) == C.St.line(st) : Nat}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Keep.same(+x: T.St, +st: T.St, hw: {S.Win.tgt(S.St.win(st)) == S.Win.tgt(S.St.win(x)) : T.Tgt}) -> ExLine.Same(Vim.Vim.keep(x, st), x):
  (Re.Keep.files(x, st), (Re.Keep.dirs(x, st), Equal.trans(T.Tgt, S.Win.tgt(S.St.win(Vim.Vim.keep(x, st))), S.Win.tgt(S.St.win(st)), S.Win.tgt(S.St.win(x)), Keep.tgt(x, st), hw)))

# a key that keeps the target, on a real buffer: the editor after it is
# the raw one kept and re-settled
def Press.eq(+x: T.St, +k: String, +hw: {S.Win.tgt(S.St.win(ExLine.st(x, k))) == S.Win.tgt(S.St.win(x)) : T.Tgt}, +hr: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool})
  -> {Laws.Spec.press(x, k) == ExLine.rf(Vim.Vim.keep(x, ExLine.st(x, k))) : T.St}:
  +y = Vim.Vim.keep(x, ExLine.st(x, k))
  Equal.trans(T.St, Laws.Spec.press(x, k), Vim.Vim.final(y), ExLine.rf(y), Re.Reach.step(x, T.EvKey{k}), ExLine.real(y, Same.real(y, x, Keep.same(x, ExLine.st(x, k), hw), hr)))

def Press.same(+x: T.St, +k: String, +hw: {S.Win.tgt(S.St.win(ExLine.st(x, k))) == S.Win.tgt(S.St.win(x)) : T.Tgt}, +hr: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool}) -> ExLine.Same(Laws.Spec.press(x, k), x):
  +y = Vim.Vim.keep(x, ExLine.st(x, k))
  %Equal.sym(T.St, Laws.Spec.press(x, k), ExLine.rf(y), Press.eq(x, k, hw, hr)) : ExLine.Same(_, x)
  Same.trans(ExLine.rf(y), y, x, Fit.same(y), Keep.same(x, ExLine.st(x, k), hw))

def Press.mode(+x: T.St, +k: String, +hw: {S.Win.tgt(S.St.win(ExLine.st(x, k))) == S.Win.tgt(S.St.win(x)) : T.Tgt}, +hr: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool}) -> {S.St.mode(Laws.Spec.press(x, k)) == S.St.mode(ExLine.st(x, k)) : T.Mode}:
  +y = Vim.Vim.keep(x, ExLine.st(x, k))
  %Equal.sym(T.St, Laws.Spec.press(x, k), ExLine.rf(y), Press.eq(x, k, hw, hr)) : {S.St.mode(_) == S.St.mode(ExLine.st(x, k)) : T.Mode}
  Equal.trans(T.Mode, S.St.mode(ExLine.rf(y)), S.St.mode(y), S.St.mode(ExLine.st(x, k)), Fit.mode(y), Re.Keep.mode(x, ExLine.st(x, k)))

def Press.line(+x: T.St, +k: String, +hw: {S.Win.tgt(S.St.win(ExLine.st(x, k))) == S.Win.tgt(S.St.win(x)) : T.Tgt}, +hr: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool})
  -> {C.St.line(Laws.Spec.press(x, k)) == Nat.min(C.St.line(ExLine.st(x, k)), M.Move.last_line(C.St.lines(x))) : Nat}:
  +st = ExLine.st(x, k)
  +y = Vim.Vim.keep(x, st)
  +rhs = Nat.min(C.St.line(st), M.Move.last_line(C.St.lines(x)))
  %Equal.sym(T.St, Laws.Spec.press(x, k), ExLine.rf(y), Press.eq(x, k, hw, hr)) : {C.St.line(_) == rhs : Nat}
  %Equal.sym(Nat, C.St.line(ExLine.rf(y)), Nat.min(C.St.line(y), M.Move.last_line(C.St.lines(y))), Fit.line(y)) : {_ == rhs : Nat}
  %Equal.sym(Nat, C.St.line(y), C.St.line(st), Keep.line(x, st)) : {Nat.min(_, M.Move.last_line(C.St.lines(y))) == rhs : Nat}
  %Equal.sym(List<&2, String>, C.St.lines(y), C.St.lines(x), Lines.same(y, x, Keep.same(x, st, hw))) : {Nat.min(C.St.line(st), M.Move.last_line(_)) == rhs : Nat}
  {==}

def Press.final(+x: T.St, +k: String, +hw: {S.Win.tgt(S.St.win(ExLine.st(x, k))) == S.Win.tgt(S.St.win(x)) : T.Tgt}, +hr: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool}) -> Fi.Final(Laws.Spec.press(x, k)):
  +y = Vim.Vim.keep(x, ExLine.st(x, k))
  %Equal.sym(T.St, Laws.Spec.press(x, k), ExLine.rf(y), Press.eq(x, k, hw, hr)) : Fi.Final(_)
  Fit.final(y)

# The keys
# --------

# ":" in normal mode, no key waiting: the command line opens
def Colon.after(+s: T.St) -> T.St:
  S.St.set_mode(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), T.Typing{T.Colon{}, ""})

def Colon.G(+s: T.St) -> Type:
  {ExLine.st(s, ":") == Colon.after(s) : T.St}

def Colon.kst(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}) -> Colon.G(s):
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          match pend:
            case T.NoPend{}:
              {==}
            case T.PendG{}:
              Eb.Pend.clash(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendG{}, find, hl, opts, rows, cols, msg, stat}), T.PendG{}, hp)
            case T.PendZ{}:
              Eb.Pend.clash(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat}), T.PendZ{}, hp)
            case T.PendLead{}:
              Eb.Pend.clash(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendLead{}, find, hl, opts, rows, cols, msg, stat}), T.PendLead{}, hp)
            case T.PendLeadF{}:
              Eb.Pend.clash(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendLeadF{}, find, hl, opts, rows, cols, msg, stat}), T.PendLeadF{}, hp)
            case T.PendY{}:
              Eb.Pend.clash(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat}), T.PendY{}, hp)
        case T.Typing{kind, text}:
          Sc.Mode.typing(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat}), kind, text, hm)
        case T.Picking{k, q, its, n, sel, top, pv, levels}:
          Sc.Mode.picking(Colon.G(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}), k, q, its, n, sel, top, pv, levels, hm)

def Colon.amode(+s: T.St) -> {S.St.mode(Colon.after(s)) == T.Typing{T.Colon{}, ""} : T.Mode}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Colon.atgt(+s: T.St) -> {S.Win.tgt(S.St.win(Colon.after(s))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Colon.mode(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}) -> {S.St.mode(ExLine.st(s, ":")) == T.Typing{T.Colon{}, ""} : T.Mode}:
  %Equal.sym(T.St, ExLine.st(s, ":"), Colon.after(s), Colon.kst(s, hm, hp)) : {S.St.mode(_) == T.Typing{T.Colon{}, ""} : T.Mode}
  Colon.amode(s)

def Colon.tgt(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}) -> {S.Win.tgt(S.St.win(ExLine.st(s, ":"))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  %Equal.sym(T.St, ExLine.st(s, ":"), Colon.after(s), Colon.kst(s, hm, hp)) : {S.Win.tgt(S.St.win(_)) == S.Win.tgt(S.St.win(s)) : T.Tgt}
  Colon.atgt(s)

# "5" on the command line ":": it types
def Five.kmode(+s: T.St) -> {S.St.mode(Laws.Spec.after(K.Key.in(s, T.Typing{T.Colon{}, ""}, "5"))) == T.Typing{T.Colon{}, "5"} : T.Mode}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Five.ktgt(+s: T.St) -> {S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, T.Typing{T.Colon{}, ""}, "5")))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Five.mode(+s: T.St, hm: {S.St.mode(s) == T.Typing{T.Colon{}, ""} : T.Mode}) -> {S.St.mode(ExLine.st(s, "5")) == T.Typing{T.Colon{}, "5"} : T.Mode}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Typing{T.Colon{}, ""}, hm) : {S.St.mode(Laws.Spec.after(K.Key.in(s, _, "5"))) == T.Typing{T.Colon{}, "5"} : T.Mode}
  Five.kmode(s)

def Five.tgt(+s: T.St, hm: {S.St.mode(s) == T.Typing{T.Colon{}, ""} : T.Mode}) -> {S.Win.tgt(S.St.win(ExLine.st(s, "5"))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Typing{T.Colon{}, ""}, hm) : {S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, _, "5")))) == S.Win.tgt(S.St.win(s)) : T.Tgt}
  Five.ktgt(s)

# Enter on the command line ":5": Ex.run goes to line 4 (at most the last)
def Cr.kmode(+s: T.St) -> {S.St.mode(Laws.Spec.after(K.Key.in(s, T.Typing{T.Colon{}, "5"}, "<CR>"))) == T.Normal{} : T.Mode}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Cr.ktgt(+s: T.St) -> {S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, T.Typing{T.Colon{}, "5"}, "<CR>")))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Cr.kline(+s: T.St) -> {C.St.line(Laws.Spec.after(K.Key.in(s, T.Typing{T.Colon{}, "5"}, "<CR>"))) == Nat.min(Nat.min(Nat.min(4n, M.Move.last_line(C.St.lines(s))), M.Move.last_line(C.St.lines(s))), M.Move.last_line(C.St.lines(s))) : Nat}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

def Cr.mode(+s: T.St, hm: {S.St.mode(s) == T.Typing{T.Colon{}, "5"} : T.Mode}) -> {S.St.mode(ExLine.st(s, "<CR>")) == T.Normal{} : T.Mode}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Typing{T.Colon{}, "5"}, hm) : {S.St.mode(Laws.Spec.after(K.Key.in(s, _, "<CR>"))) == T.Normal{} : T.Mode}
  Cr.kmode(s)

def Cr.tgt(+s: T.St, hm: {S.St.mode(s) == T.Typing{T.Colon{}, "5"} : T.Mode}) -> {S.Win.tgt(S.St.win(ExLine.st(s, "<CR>"))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Typing{T.Colon{}, "5"}, hm) : {S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, _, "<CR>")))) == S.Win.tgt(S.St.win(s)) : T.Tgt}
  Cr.ktgt(s)

def Cr.line(+s: T.St, hm: {S.St.mode(s) == T.Typing{T.Colon{}, "5"} : T.Mode}) -> {C.St.line(ExLine.st(s, "<CR>")) == Nat.min(Nat.min(Nat.min(4n, M.Move.last_line(C.St.lines(s))), M.Move.last_line(C.St.lines(s))), M.Move.last_line(C.St.lines(s))) : Nat}:
  +ll = M.Move.last_line(C.St.lines(s))
  %Equal.sym(T.Mode, S.St.mode(s), T.Typing{T.Colon{}, "5"}, hm) : {C.St.line(Laws.Spec.after(K.Key.in(s, _, "<CR>"))) == Nat.min(Nat.min(Nat.min(4n, ll), ll), ll) : Nat}
  Cr.kline(s)

# The claim
# ---------

# min(min(a, b), b) is min(a, b)
def Min.idem(a: Nat, +b: Nat) -> {Nat.min(Nat.min(a, b), b) == Nat.min(a, b) : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.min(Nat.min(p, q), q), Nat.min(p, q), Min.idem(p, q))

def Min.four(+b: Nat) -> {Nat.min(Nat.min(Nat.min(Nat.min(4n, b), b), b), b) == Nat.min(4n, b) : Nat}:
  +a = Nat.min(4n, b)
  +y = Nat.min(a, b)
  Equal.trans(Nat, Nat.min(Nat.min(y, b), b), Nat.min(y, b), a, Min.idem(y, b), Equal.trans(Nat, Nat.min(y, b), y, a, Min.idem(a, b), Min.idem(4n, b)))

def Same.tgt(t: T.Tgt) -> {Laws.Spec.same_tgt(t, t) == True{} : Bool}:
  match t:
    case T.File{+i}:
      L.Nat.eq_refl(i)
    case T.Dir{+path}:
      Tx.String.eq_refl(path)

def Same.frames(+n: T.St, +p: T.St, st: {S.Win.tgt(S.St.win(p)) == S.Win.tgt(S.St.win(n)) : T.Tgt}) -> {Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(n)), Laws.F.tgt(Vim.Vim.frame(p))) == True{} : Bool}:
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(p)), S.Win.tgt(S.St.win(n)), st) : {Laws.Spec.same_tgt(S.Win.tgt(S.St.win(n)), _) == True{} : Bool}
  Same.tgt(S.Win.tgt(S.St.win(n)))

# the spec's lines of a window are its own
def Lines.spec(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.lines(fs, s) == C.St.lines(s) : List<&2, String>}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              Sc.Files.spec(fs, files, i, hf)
            case T.Dir{+path}:
              {==}

# the line the law asks for: min(4, the last line)
def Want.eq(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.min(4n, Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, s)))) == Nat.min(4n, M.Move.last_line(C.St.lines(s))) : Nat}:
  +ls = C.St.lines(s)
  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, s), ls, Lines.spec(fs, s, hf)) : {Laws.Spec.min(4n, Laws.Spec.last(Laws.Spec.count(_))) == Nat.min(4n, M.Move.last_line(ls)) : Nat}
  %Tx.Count.eq(ls) : {Laws.Spec.min(4n, Laws.Spec.last(_)) == Nat.min(4n, M.Move.last_line(ls)) : Nat}
  Sc.Spec.min_eq(4n, Nat.sub(B.Lines.len(ls), 1n))

# a settled editor in normal mode: the frame reads back the cursor's line
def ExLine.at_line(+s: T.St, fin: Fi.Final(s), hm: {S.St.mode(s) == T.Normal{} : T.Mode}) -> {Laws.Spec.at_line(Vim.Vim.frame(s)) == C.St.line(s) : Nat}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          (f3, r1) = fin
          (f12, r2) = r1
          (fl, r3) = r2
          (fc, r4) = r3
          (bt, bl) = r4
          (bth, btl) = bt
          +s0 = {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}
          +l = C.St.line(s0)
          +top = S.Win.top(win)
          +h = C.St.h(s0)
          L.Nat.add_sub(l, top, Sc.Win.top_le(l, V.View.so_in(h), top, btl))
        case T.Typing{kind, text}:
          Sc.Mode.typing({Laws.Spec.at_line(Vim.Vim.frame(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat})) == C.St.line(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat}) : Nat}, kind, text, hm)
        case T.Picking{k, q, its, n, sel, top, pv, levels}:
          Sc.Mode.picking({Laws.Spec.at_line(Vim.Vim.frame(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat})) == C.St.line(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}) : Nat}, k, q, its, n, sel, top, pv, levels, hm)

# p shows n's target, settled in normal mode on line min(4, last)
def ExLine.claim(+fs: List<&2, T.Buf>, +n: T.St, +p: T.St, hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, st: {S.Win.tgt(S.St.win(p)) == S.Win.tgt(S.St.win(n)) : T.Tgt},
  fin: Fi.Final(p), hm: {S.St.mode(p) == T.Normal{} : T.Mode}, hl: {C.St.line(p) == Nat.min(4n, M.Move.last_line(C.St.lines(n))) : Nat})
  -> {Laws.Spec.moved_line(n, p, Laws.Spec.min(4n, Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, n))))) == True{} : Bool}:
  +want = Laws.Spec.min(4n, Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, n))))
  +four = Nat.min(4n, M.Move.last_line(C.St.lines(n)))
  +at = Laws.Spec.at_line(Vim.Vim.frame(p))
  +e = Equal.trans(Nat, at, C.St.line(p), want, ExLine.at_line(p, fin, hm), Equal.trans(Nat, C.St.line(p), four, want, hl, Equal.sym(Nat, want, four, Want.eq(fs, n, hf))))
  L.And.intro(Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(n)), Laws.F.tgt(Vim.Vim.frame(p))), Nat.is_eq(at, want), Same.frames(n, p, st), Pa.Eq.of(at, want, e))

# The law
# -------

# ":5<CR>" from a settled editor in normal mode, no key waiting, on a
# real buffer over the files of fs
def ExLine.of(+fs: List<&2, T.Buf>, +n: T.St, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, +hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +hr: {B.Tgt.real(S.St.files(n), S.Win.tgt(S.St.win(n))) == True{} : Bool}) -> {Laws.Claim.ex_line(fs, n) == True{} : Bool}:
  +p1 = Laws.Spec.press(n, ":")
  +p2 = Laws.Spec.press(p1, "5")
  +p3 = Laws.Spec.press(p2, "<CR>")
  +w1 = Colon.tgt(n, hm, hp)
  +s1 = Press.same(n, ":", w1, hr)
  +m1 = Equal.trans(T.Mode, S.St.mode(p1), S.St.mode(ExLine.st(n, ":")), T.Typing{T.Colon{}, ""}, Press.mode(n, ":", w1, hr), Colon.mode(n, hm, hp))
  +r1 = Same.real(p1, n, s1, hr)
  +w2 = Five.tgt(p1, m1)
  +s2 = Press.same(p1, "5", w2, r1)
  +m2 = Equal.trans(T.Mode, S.St.mode(p2), S.St.mode(ExLine.st(p1, "5")), T.Typing{T.Colon{}, "5"}, Press.mode(p1, "5", w2, r1), Five.mode(p1, m1))
  +r2 = Same.real(p2, p1, s2, r1)
  +w3 = Cr.tgt(p2, m2)
  +s12 = Same.trans(p2, p1, n, s2, s1)
  +s3 = Same.trans(p3, p2, n, Press.same(p2, "<CR>", w3, r2), s12)
  +m3 = Equal.trans(T.Mode, S.St.mode(p3), S.St.mode(ExLine.st(p2, "<CR>")), T.Normal{}, Press.mode(p2, "<CR>", w3, r2), Cr.mode(p2, m2))
  +ll2 = M.Move.last_line(C.St.lines(p2))
  +l3 = Equal.trans(Nat, C.St.line(p3), Nat.min(C.St.line(ExLine.st(p2, "<CR>")), ll2), Nat.min(4n, ll2), Press.line(p2, "<CR>", w3, r2),
    Equal.trans(Nat, Nat.min(C.St.line(ExLine.st(p2, "<CR>")), ll2), Nat.min(Nat.min(Nat.min(Nat.min(4n, ll2), ll2), ll2), ll2), Nat.min(4n, ll2),
      Equal.cong(Nat, Nat, z => Nat.min(z, ll2), C.St.line(ExLine.st(p2, "<CR>")), Nat.min(Nat.min(Nat.min(4n, ll2), ll2), ll2), Cr.line(p2, m2)), Min.four(ll2)))
  +l4 = Equal.trans(Nat, C.St.line(p3), Nat.min(4n, ll2), Nat.min(4n, M.Move.last_line(C.St.lines(n))), l3,
    Equal.cong(List<&2, String>, Nat, ls => Nat.min(4n, M.Move.last_line(ls)), C.St.lines(p2), C.St.lines(n), Lines.same(p2, n, s12)))
  ExLine.claim(fs, n, p3, hf, Same.tgt_of(p3, n, s3), Press.final(p2, "<CR>", w3, r2), m3, l4)

# the editor after evs and an Esc shows a real buffer
def ExLine.real_normal(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {B.Tgt.real(S.St.files(Laws.Spec.normal(fs, rows, cols, evs)), S.Win.tgt(S.St.win(Laws.Spec.normal(fs, rows, cols, evs)))) == True{} : Bool}:
  +evs2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  +y = Re.Reach.pre(evs2, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs2), Vim.Vim.final(y), Re.Reach.run(fs, rows, cols, evs2)) : {B.Tgt.real(S.St.files(_), S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(Vim.Vim.final(y)), S.St.files(y), Re.Field.files_final(y)) : {B.Tgt.real(_, S.Win.tgt(S.St.win(Vim.Vim.final(y)))) == True{} : Bool}
  Rb.Real.of(y)

def ExLine.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.ex_line(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  ExLine.of(fs, Laws.Spec.normal(fs, rows, cols, evs), Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs), Re.Reach.files_run(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))), ExLine.real_normal(fs, rows, cols, evs))

def ExLaws.ex_line(fs, rows, cols, evs):
  ExLine.law(fs, rows, cols, evs)
