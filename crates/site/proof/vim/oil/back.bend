# eukhe.com's Neovim: the proof of LAW oil_back
# =============================================
#
# From file i in normal mode with no key waiting, "-" opens Oil on the
# file's folder (real: Path.real_dir, so Vim.final keeps it); leaving the
# file put i first among the files opened (Win.leave), and a folder's jump
# keeps that list. Ctrl-c there is Win.alt: the head of that list, file i,
# which is real since the window showed it.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/oil.bend as OilLaws
import ../../base.bend as L
import ../../base/reach.bend as Rc
import ./base.bend as O
import ./path.bend as Pa

# the editor "-" settles on, from n, and the folder it shows
def Back.y(+n: T.St) -> T.St:
  Vim.Vim.keep(n, C.Oil.here(O.Oil.idle(n)))

def Back.dir(+n: T.St, +i: Nat) -> String:
  B.Path.dir(B.Buf.path(B.Files.at(S.St.files(n), i)))

# the files opened after "-": i first
def Back.rest(+n: T.St, +i: Nat) -> List<&2, Nat>:
  C.Opened.drop(S.St.opened(O.Oil.idle(n)), i, Nil{})

def Back.tgt(+n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}) -> {O.Oil.tgt(Back.y(n)) == T.Dir{Back.dir(n, i)} : T.Tgt}:
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  Equal.trans(T.Tgt, O.Oil.tgt(Back.y(n)), O.Oil.tgt(h), T.Dir{Back.dir(n, i)},
    Equal.cong(T.Win, T.Tgt, w => S.Win.tgt(w), S.St.win(Back.y(n)), S.St.win(h), O.Oil.keep_win(n, h)),
    Equal.trans(T.Tgt, O.Oil.tgt(h), T.Dir{B.Path.dir(B.Buf.path(B.Files.at(S.St.files(z), i)))}, T.Dir{Back.dir(n, i)},
      O.Oil.here_file(z, i, Equal.trans(T.Tgt, O.Oil.tgt(z), O.Oil.tgt(n), T.File{i}, O.Oil.idle_tgt(n), e)),
      Equal.cong(List<&2, T.Buf>, T.Tgt, fs => T.Dir{B.Path.dir(B.Buf.path(B.Files.at(fs, i)))}, S.St.files(z), S.St.files(n), O.Oil.idle_files(n))))

def Back.real0(+n: T.St, -i: Nat, e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}) -> {B.Tgt.real(S.St.files(n), T.File{i}) == True{} : Bool}:
  %e : {B.Tgt.real(S.St.files(n), _) == True{} : Bool}
  hr

def Back.real(+n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}) -> {B.Tgt.real(S.St.files(Back.y(n)), O.Oil.tgt(Back.y(n))) == True{} : Bool}:
  +y = Back.y(n)
  %Equal.sym(List<&2, T.Buf>, S.St.files(y), S.St.files(n), Rc.Keep.files(n, C.Oil.here(O.Oil.idle(n)))) : {B.Tgt.real(_, O.Oil.tgt(y)) == True{} : Bool}
  %Equal.sym(T.Tgt, O.Oil.tgt(y), T.Dir{Back.dir(n, i)}, Back.tgt(n, i, e)) : {B.Tgt.real(S.St.files(n), _) == True{} : Bool}
  Pa.Path.real_dir(S.St.files(n), i, Back.real0(n, i, e, hr))

# the settled editor after "-"
def Back.y1(+n: T.St) -> T.St:
  Vim.Vim.final(Back.y(n))

def Back.y_mode(+n: T.St, hm: {S.St.mode(n) == T.Normal{} : T.Mode}) -> {S.St.mode(Back.y(n)) == T.Normal{} : T.Mode}:
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  Equal.trans(T.Mode, S.St.mode(Back.y(n)), S.St.mode(h), T.Normal{}, Rc.Keep.mode(n, h),
    Equal.trans(T.Mode, S.St.mode(h), S.St.mode(z), T.Normal{}, O.Oil.here_mode(z),
      Equal.trans(T.Mode, S.St.mode(z), S.St.mode(n), T.Normal{}, O.Oil.idle_mode(n), hm)))

def Back.y1_mode(+n: T.St, hm: {S.St.mode(n) == T.Normal{} : T.Mode}) -> {S.St.mode(Back.y1(n)) == T.Normal{} : T.Mode}:
  Equal.trans(T.Mode, S.St.mode(Back.y1(n)), S.St.mode(Back.y(n)), T.Normal{}, Rc.Field.mode_final(Back.y(n)), Back.y_mode(n, hm))

def Back.y_pend(+n: T.St, hm: {S.St.mode(n) == T.Normal{} : T.Mode}) -> {Vim.Vim.pend(S.St.mode(Back.y(n)), S.St.pend(Back.y(n))) == T.NoPend{} : T.Pend}:
  +y = Back.y(n)
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  %Equal.sym(T.Mode, S.St.mode(y), T.Normal{}, Back.y_mode(n, hm)) : {Vim.Vim.pend(_, S.St.pend(y)) == T.NoPend{} : T.Pend}
  Equal.trans(T.Pend, S.St.pend(y), S.St.pend(h), T.NoPend{}, Rc.Keep.pend(n, h),
    Equal.trans(T.Pend, S.St.pend(h), S.St.pend(z), T.NoPend{}, O.Oil.here_pend(z), O.Oil.idle_pend(n)))

def Back.y1_pend(+n: T.St, hm: {S.St.mode(n) == T.Normal{} : T.Mode}) -> {S.St.pend(Back.y1(n)) == T.NoPend{} : T.Pend}:
  +y = Back.y(n)
  Equal.trans(T.Pend, S.St.pend(Back.y1(n)), Vim.Vim.pend(S.St.mode(y), S.St.pend(y)), T.NoPend{}, Rc.Field.pend_final(y), Back.y_pend(n, hm))

def Back.put_head(+n: T.St, +i: Nat, e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}) -> {Vim.Vim.opened(C.Opened.put(S.St.opened(O.Oil.idle(n)), O.Oil.tgt(O.Oil.idle(n)))) == Con{i, Back.rest(n, i)} : List<&2, Nat>}:
  +z = O.Oil.idle(n)
  %Equal.sym(T.Tgt, O.Oil.tgt(z), T.File{i}, Equal.trans(T.Tgt, O.Oil.tgt(z), O.Oil.tgt(n), T.File{i}, O.Oil.idle_tgt(n), e)) : {Vim.Vim.opened(C.Opened.put(S.St.opened(z), _)) == Con{i, Back.rest(n, i)} : List<&2, Nat>}
  {==}

def Back.y1_opened(+n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}) -> {S.St.opened(Back.y1(n)) == Con{i, Back.rest(n, i)} : List<&2, Nat>}:
  +y = Back.y(n)
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  +o = C.Opened.put(S.St.opened(z), O.Oil.tgt(z))
  Equal.trans(List<&2, Nat>, S.St.opened(Back.y1(n)), S.St.opened(y), Con{i, Back.rest(n, i)}, Rc.Field.opened_final(y),
    Equal.trans(List<&2, Nat>, S.St.opened(y), Vim.Vim.opened(S.St.opened(h)), Con{i, Back.rest(n, i)}, Rc.Keep.opened(n, h),
      Equal.trans(List<&2, Nat>, Vim.Vim.opened(S.St.opened(h)), Vim.Vim.opened(o), Con{i, Back.rest(n, i)}, Equal.cong(List<&2, Nat>, List<&2, Nat>, os => Vim.Vim.opened(os), S.St.opened(h), o, O.Oil.here_opened(z)),
        Back.put_head(n, i, e))))

def Back.y1_tgt(+n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}) -> {O.Oil.tgt(Back.y1(n)) == T.Dir{Back.dir(n, i)} : T.Tgt}:
  Equal.trans(T.Tgt, O.Oil.tgt(Back.y1(n)), O.Oil.tgt(Back.y(n)), T.Dir{Back.dir(n, i)}, O.Oil.fin_tgt(Back.y(n), Back.real(n, i, e, hr)), Back.tgt(n, i, e))

def Back.y1_files(+n: T.St) -> {S.St.files(Back.y1(n)) == S.St.files(n) : List<&2, T.Buf>}:
  Equal.trans(List<&2, T.Buf>, S.St.files(Back.y1(n)), S.St.files(Back.y(n)), S.St.files(n), Rc.Field.files_final(Back.y(n)), Rc.Keep.files(n, C.Oil.here(O.Oil.idle(n))))

# Ctrl-c in Oil goes to the first file opened
def Back.alt_tgt(+z: T.St, +i: Nat, -rest: List<&2, Nat>, eof: {C.St.on_file(z) == False{} : Bool}, eo: {S.St.opened(z) == Con{i, rest} : List<&2, Nat>}) -> {O.Oil.tgt(Bool.pick(T.St, C.St.on_file(z), z, C.Win.alt(z))) == T.File{i} : T.Tgt}:
  %Equal.sym(Bool, C.St.on_file(z), False{}, eof) : {O.Oil.tgt(Bool.pick(T.St, _, z, C.Win.to(z, List.head(&2, Nat, List.drop(&2, Nat, S.St.opened(z), Bool.pick(Nat, _, 1n, 0n)))))) == T.File{i} : T.Tgt}
  %Equal.sym(List<&2, Nat>, S.St.opened(z), Con{i, rest}, eo) : {O.Oil.tgt(C.Win.to(z, List.head(&2, Nat, List.drop(&2, Nat, _, 0n)))) == T.File{i} : T.Tgt}
  O.Oil.open_tgt(z, T.File{i}, Maybe.default(&2, T.Pos, List.get(&2, T.Pos, S.St.marks(z), i), T.Pos{0n, 0n}))

def Back.onfile(+y1: T.St, -d: String, e: {O.Oil.tgt(y1) == T.Dir{d} : T.Tgt}) -> {C.St.on_file(O.Oil.idle(y1)) == False{} : Bool}:
  %Equal.sym(T.Tgt, O.Oil.tgt(O.Oil.idle(y1)), T.Dir{d}, Equal.trans(T.Tgt, O.Oil.tgt(O.Oil.idle(y1)), O.Oil.tgt(y1), T.Dir{d}, O.Oil.idle_tgt(y1), e)) : {C.Tgt.is_file(_) == False{} : Bool}
  {==}

def Back.real2(-y2: T.St, -n: T.St, -i: Nat, fy: {S.St.files(y2) == S.St.files(n) : List<&2, T.Buf>}, ty: {O.Oil.tgt(y2) == T.File{i} : T.Tgt}, h: {B.Tgt.real(S.St.files(n), T.File{i}) == True{} : Bool})
  -> {B.Tgt.real(S.St.files(y2), O.Oil.tgt(y2)) == True{} : Bool}:
  %Equal.sym(List<&2, T.Buf>, S.St.files(y2), S.St.files(n), fy) : {B.Tgt.real(_, O.Oil.tgt(y2)) == True{} : Bool}
  %Equal.sym(T.Tgt, O.Oil.tgt(y2), T.File{i}, ty) : {B.Tgt.real(S.St.files(n), _) == True{} : Bool}
  h

# Ctrl-c after "-": back on file i
def Back.b_tgt(+n: T.St, +i: Nat, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool})
  -> {O.Oil.tgt(Laws.Spec.press(Back.y1(n), "<C-c>")) == T.File{i} : T.Tgt}:
  +y1 = Back.y1(n)
  +z1 = O.Oil.idle(y1)
  +p1 = Bool.pick(T.St, C.St.on_file(z1), z1, C.Win.alt(z1))
  +y2 = Vim.Vim.keep(y1, p1)
  +ht = Back.alt_tgt(z1, i, Back.rest(n, i), Back.onfile(y1, Back.dir(n, i), Back.y1_tgt(n, i, e, hr)), Equal.trans(List<&2, Nat>, S.St.opened(z1), S.St.opened(y1), Con{i, Back.rest(n, i)}, O.Oil.idle_opened(y1), Back.y1_opened(n, i, e)))
  +ty2 = Equal.trans(T.Tgt, O.Oil.tgt(y2), O.Oil.tgt(p1), T.File{i}, Equal.cong(T.Win, T.Tgt, w => S.Win.tgt(w), S.St.win(y2), S.St.win(p1), O.Oil.keep_win(y1, p1)), ht)
  +fy2 = Equal.trans(List<&2, T.Buf>, S.St.files(y2), S.St.files(y1), S.St.files(n), Rc.Keep.files(y1, p1), Back.y1_files(n))
  %Equal.sym(T.St, Laws.Spec.press(y1, "<C-c>"), Vim.Vim.final(Vim.Vim.keep(y1, Laws.Spec.after(K.Key.in(y1, S.St.mode(y1), "<C-c>")))), O.Oil.press(y1, "<C-c>")) : {O.Oil.tgt(_) == T.File{i} : T.Tgt}
  %Equal.sym(T.St, Laws.Spec.after(K.Key.in(y1, S.St.mode(y1), "<C-c>")), p1, O.Oil.ctrl_c(y1, Back.y1_mode(n, hm), Back.y1_pend(n, hm))) : {O.Oil.tgt(Vim.Vim.final(Vim.Vim.keep(y1, _))) == T.File{i} : T.Tgt}
  +hy2 = Back.real2(y2, n, i, fy2, ty2, Back.real0(n, i, e, hr))
  Equal.trans(T.Tgt, O.Oil.tgt(Vim.Vim.final(y2)), O.Oil.tgt(y2), T.File{i}, O.Oil.fin_tgt(y2, hy2), ty2)

def Back.at(+n: T.St, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, t: T.Tgt, +e: {O.Oil.tgt(n) == t : T.Tgt})
  -> {Bool.pick(Bool, Laws.Spec.is_file(t), Laws.Spec.same_tgt(t, O.Oil.tgt(Laws.Spec.press(Laws.Spec.press(n, "-"), "<C-c>"))), True{}) == True{} : Bool}:
  match t:
    case T.File{+i}:
      %Equal.sym(T.St, Laws.Spec.press(n, "-"), Vim.Vim.final(Vim.Vim.keep(n, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")))), O.Oil.press(n, "-")) : {Laws.Spec.same_tgt(T.File{i}, O.Oil.tgt(Laws.Spec.press(_, "<C-c>"))) == True{} : Bool}
      %Equal.sym(T.St, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")), C.Oil.here(O.Oil.idle(n)), O.Oil.dash(n, hm, hp)) : {Laws.Spec.same_tgt(T.File{i}, O.Oil.tgt(Laws.Spec.press(Vim.Vim.final(Vim.Vim.keep(n, _)), "<C-c>"))) == True{} : Bool}
      %Equal.sym(T.Tgt, O.Oil.tgt(Laws.Spec.press(Back.y1(n), "<C-c>")), T.File{i}, Back.b_tgt(n, i, hm, e, hr)) : {Laws.Spec.same_tgt(T.File{i}, _) == True{} : Bool}
      L.Nat.eq_refl(i)
    case T.Dir{path}:
      {==}

def Back.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.back(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  Back.at(n, Rc.Reach.normal_mode(fs, rows, cols, evs), Rc.Reach.normal_pend(fs, rows, cols, evs), O.Oil.run_real(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))), O.Oil.tgt(n), {==})

def OilLaws.oil_back(fs, rows, cols, evs):
  Back.law(fs, rows, cols, evs)
