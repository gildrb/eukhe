# eukhe.com's Neovim: the proof of LAW oil_parent
# ===============================================
#
# In normal mode with no key waiting (an Esc's doing), "-" on folder path
# is Oil.here: Win.open on B.Path.up(path) (the root stays). That folder is
# real (Path.real_up), so Vim.final keeps it, and B.Path.up is the spec's
# parent (Path.up_eq).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/oil.bend as OilLaws
import ../../base/text.bend as Tx
import ../../base/reach.bend as Rc
import ./base.bend as O
import ./path.bend as Pa

# the editor "-" settles on, from n
def Parent.y(+n: T.St) -> T.St:
  Vim.Vim.keep(n, C.Oil.here(O.Oil.idle(n)))

# it shows the folder above path
def Parent.tgt(+n: T.St, +path: String, +e: {O.Oil.tgt(n) == T.Dir{path} : T.Tgt}) -> {O.Oil.tgt(Parent.y(n)) == T.Dir{B.Path.up(path)} : T.Tgt}:
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  Equal.trans(T.Tgt, O.Oil.tgt(Parent.y(n)), O.Oil.tgt(h), T.Dir{B.Path.up(path)},
    Equal.cong(T.Win, T.Tgt, w => S.Win.tgt(w), S.St.win(Parent.y(n)), S.St.win(h), O.Oil.keep_win(n, h)),
    O.Oil.here_dir(z, path, Equal.trans(T.Tgt, O.Oil.tgt(z), O.Oil.tgt(n), T.Dir{path}, O.Oil.idle_tgt(n), e)))

def Parent.real0(+n: T.St, -path: String, e: {O.Oil.tgt(n) == T.Dir{path} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}) -> {B.Tgt.real(S.St.files(n), T.Dir{path}) == True{} : Bool}:
  %e : {B.Tgt.real(S.St.files(n), _) == True{} : Bool}
  hr

# which is real
def Parent.real(+n: T.St, +path: String, +e: {O.Oil.tgt(n) == T.Dir{path} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}) -> {B.Tgt.real(S.St.files(Parent.y(n)), O.Oil.tgt(Parent.y(n))) == True{} : Bool}:
  +y = Parent.y(n)
  %Equal.sym(List<&2, T.Buf>, S.St.files(y), S.St.files(n), Rc.Keep.files(n, C.Oil.here(O.Oil.idle(n)))) : {B.Tgt.real(_, O.Oil.tgt(y)) == True{} : Bool}
  %Equal.sym(T.Tgt, O.Oil.tgt(y), T.Dir{B.Path.up(path)}, Parent.tgt(n, path, e)) : {B.Tgt.real(S.St.files(n), _) == True{} : Bool}
  Pa.Path.real_up(S.St.files(n), path, Parent.real0(n, path, e, hr))

def Parent.at(+n: T.St, hm: {S.St.mode(n) == T.Normal{} : T.Mode}, hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, t: T.Tgt, +e: {O.Oil.tgt(n) == t : T.Tgt})
  -> {Laws.Claim.parent.of(n, t) == True{} : Bool}:
  match t:
    case T.File{i}:
      {==}
    case T.Dir{+path}:
      +y = Parent.y(n)
      +up = B.Path.up(path)
      %Equal.sym(T.St, Laws.Spec.press(n, "-"), Vim.Vim.final(Vim.Vim.keep(n, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")))), O.Oil.press(n, "-")) : {Laws.Spec.is_dir(O.Oil.tgt(_), Laws.Spec.parent(path)) == True{} : Bool}
      %Equal.sym(T.St, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")), C.Oil.here(O.Oil.idle(n)), O.Oil.dash(n, hm, hp)) : {Laws.Spec.is_dir(O.Oil.tgt(Vim.Vim.final(Vim.Vim.keep(n, _))), Laws.Spec.parent(path)) == True{} : Bool}
      %Equal.sym(T.Tgt, O.Oil.tgt(Vim.Vim.final(y)), O.Oil.tgt(y), O.Oil.fin_tgt(y, Parent.real(n, path, e, hr))) : {Laws.Spec.is_dir(_, Laws.Spec.parent(path)) == True{} : Bool}
      %Equal.sym(T.Tgt, O.Oil.tgt(y), T.Dir{up}, Parent.tgt(n, path, e)) : {Laws.Spec.is_dir(_, Laws.Spec.parent(path)) == True{} : Bool}
      %Equal.sym(String, up, Laws.Spec.parent(path), Pa.Path.up_eq(path)) : {String.eq(_, Laws.Spec.parent(path)) == True{} : Bool}
      Tx.String.eq_refl(Laws.Spec.parent(path))

def Parent.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.parent(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  Parent.at(n, Rc.Reach.normal_mode(fs, rows, cols, evs), Rc.Reach.normal_pend(fs, rows, cols, evs), O.Oil.run_real(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))), O.Oil.tgt(n), {==})

def OilLaws.oil_parent(fs, rows, cols, evs):
  Parent.law(fs, rows, cols, evs)
