# eukhe.com's Neovim: the proofs of the visual-mode laws vis_label, v_v,
# V_v and v_j
# ======================================================================
#
# The command line in visual mode is the mode's name cut to the screen
# (Scr.cmd): at 17 columns or more, the whole name (Label.cut). v and V
# from Idle.mk of the editor enter visual mode on a file; a second v, or v
# after V, is Key.visual.toggle; j runs normal mode's j and Key.revisual
# keeps visual mode on the same file (Revis.keep).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/screen.bend as R
import ../../../vim/visual.bend as Vi
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/visual.bend as VisualLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../../base/text.bend as Tx
import ../motion/base.bend as Mo
import ../esc/base.bend as Eb
import ./yank_char.bend as Yc

# The mode's name
# ---------------

# the name cut to 17 columns or more: every one of its characters fits
def Label.text(k: T.Vis, +c: Nat) -> {X.Text.cut(Vi.Vis.label(k), Nat.add(17n, c)) == Laws.Spec.vis_name(k) : String}:
  match k:
    case T.VChars{}:
      {==}
    case T.VLines{}:
      %Equal.sym(Bool, Nat.is_le(0n, c), True{}, L.Nat.le_zero(c)) : {X.Text.rest(Bool.pick(String, _, " -- VISUAL LINE --", " -- VISUAL LINE -")) == "-- VISUAL LINE --" : String}
      {==}

def Label.cut(+k: T.Vis, +c: Nat) -> {String.eq(X.Text.cut(Vi.Vis.label(k), Nat.add(17n, c)), Laws.Spec.vis_name(k)) == True{} : Bool}:
  Tx.String.eq_same(X.Text.cut(Vi.Vis.label(k), Nat.add(17n, c)), Laws.Spec.vis_name(k), Label.text(k, c))

def Label.pick(b: Bool, +k: T.Vis, +cols: Nat, e: {Nat.is_le(17n, cols) == b : Bool}) -> {Laws.Spec.implies(b, String.eq(X.Text.cut(Vi.Vis.label(k), cols), Laws.Spec.vis_name(k))) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      %L.Nat.add_sub(cols, 17n, e) : {String.eq(X.Text.cut(Vi.Vis.label(k), _), Laws.Spec.vis_name(k)) == True{} : Bool}
      Label.cut(k, Nat.sub(cols, 17n))

def Label.of(s: T.St) -> {Laws.Claim.vis_label(s) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          {==}
        case T.Typing{kind, text}:
          {==}
        case T.Picking{kind, q, its, n, sel, top, pv, levels}:
          {==}
        case T.Visual{+k, +start}:
          Label.pick(Nat.is_le(17n, cols), k, cols, {==})

def VisualLaws.vis_label(fs, rows, cols, evs):
  Label.of(Laws.Spec.run(fs, rows, cols, evs))

# v, v
# ----

def VV.core(s: T.St) -> {Laws.Claim.v_v(Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              {==}

def VV.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.v_v(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.v_v(_) == True{} : Bool}
  VV.core(n)

def VisualLaws.v_v(fs, rows, cols, evs):
  VV.law(fs, rows, cols, evs)

# V, v
# ----

def BigVV.core(s: T.St, +fin: Fi.Final(Mo.Idle.mk(s))) -> {Laws.Claim.V_v(Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              (e3, r1) = fin
              (e12, r2) = r1
              +name = {"-- VISUAL --" : String}
              %Eb.Esc.max_back(cols, 12n, e12) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(X.Text.cut(Vi.Vis.label(T.VChars{}), Nat.max(_, 12n)), name)) == True{} : Bool}
              %Eb.Esc.max_back(cols, 12n, e12) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(X.Text.cut(Vi.Vis.label(T.VChars{}), _), name)) == True{} : Bool}
              Label.pick(Nat.is_le(17n, cols), T.VChars{}, cols, {==})

def BigVV.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.V_v(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.V_v(_) == True{} : Bool}
  BigVV.core(n, Mo.Ready.fin(fs, rows, cols, evs))

def VisualLaws.V_v(fs, rows, cols, evs):
  BigVV.law(fs, rows, cols, evs)

# v, j
# ----

# V, V
# ----

def VVb.core(s: T.St) -> {Laws.Claim.V_V(Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              {==}

def VVb.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.V_V(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.V_V(_) == True{} : Bool}
  VVb.core(n)

def VisualLaws.V_V(fs, rows, cols, evs):
  VVb.law(fs, rows, cols, evs)

# v, V
# ----

def SmallVBigV.core(s: T.St, +fin: Fi.Final(Mo.Idle.mk(s))) -> {Laws.Claim.v_V(Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              (e3, r1) = fin
              (e12, r2) = r1
              +name = {"-- VISUAL LINE --" : String}
              %Eb.Esc.max_back(cols, 12n, e12) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(X.Text.cut(Vi.Vis.label(T.VLines{}), Nat.max(_, 12n)), name)) == True{} : Bool}
              %Eb.Esc.max_back(cols, 12n, e12) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(X.Text.cut(Vi.Vis.label(T.VLines{}), _), name)) == True{} : Bool}
              Label.pick(Nat.is_le(17n, cols), T.VLines{}, cols, {==})

def SmallVBigV.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.v_V(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.v_V(_) == True{} : Bool}
  SmallVBigV.core(n, Mo.Ready.fin(fs, rows, cols, evs))

def VisualLaws.v_V(fs, rows, cols, evs):
  SmallVBigV.law(fs, rows, cols, evs)

# v, j
# ----

# the command line after a step that ends in visual mode: the mode's name
# cut to the screen, whatever the step did (so the step itself is never
# computed)
def Cmd.vis(+v1: T.St, st: T.St, +k: T.Vis, +p: T.Pos) -> {Laws.F.cmd(Vim.Vim.frame(Vim.Vim.final(Vim.Vim.keep(v1, S.St.set_mode(st, T.Visual{k, p}))))) == X.Text.cut(Vi.Vis.label(k), Nat.max(S.St.cols(v1), 12n)) : String}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# j in visual mode
# ----------------

def Revis.after(r: T.Step, +k: T.Vis, +start: T.Pos, +tgt: T.Tgt) -> {Laws.Spec.after(K.Key.revisual.step(r, k, start, tgt)) == K.Key.revisual(Laws.Spec.after(r), S.St.mode(Laws.Spec.after(r)), k, start, tgt) : T.St}:
  match r:
    case T.Step{+st, act}:
      {==}

def Revis.normal(+st: T.St, +k: T.Vis, +start: T.Pos, +i: Nat, hm: {S.St.mode(st) == T.Normal{} : T.Mode}, ht: {S.Win.tgt(S.St.win(st)) == T.File{i} : T.Tgt})
  -> {K.Key.revisual(st, S.St.mode(st), k, start, T.File{i}) == S.St.set_mode(st, T.Visual{k, start}) : T.St}:
  %Equal.sym(T.Mode, S.St.mode(st), T.Normal{}, hm) : {K.Key.revisual(st, _, k, start, T.File{i}) == S.St.set_mode(st, T.Visual{k, start}) : T.St}
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(st)), T.File{i}, ht) : {Bool.pick(T.St, Vi.Vis.same_tgt(T.File{i}, _), S.St.set_mode(st, T.Visual{k, start}), st) == S.St.set_mode(st, T.Visual{k, start}) : T.St}
  %Equal.sym(Bool, Nat.is_eq(i, i), True{}, L.Nat.eq_refl(i)) : {Bool.pick(T.St, _, S.St.set_mode(st, T.Visual{k, start}), st) == S.St.set_mode(st, T.Visual{k, start}) : T.St}
  {==}

def GoLine.mode(s: T.St, +l: Nat) -> {S.St.mode(C.Win.go_line(s, l)) == S.St.mode(s) : T.Mode}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      {==}

def GoLine.tgt(s: T.St, +l: Nat) -> {S.Win.tgt(S.St.win(C.Win.go_line(s, l))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          {==}

# from an editor y in visual mode (characters, from p) on file i, j is
# normal mode's j back in visual mode
def Press.hn(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")) == C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)) : T.St}:
  {==}

def PV.next(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Re.Reach.next(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, T.EvKey{"j"}) == Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i}))) : T.St}:
  {==}

def PV.e1(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j") == Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})))) : T.St}:
  Equal.trans(T.St, Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), Vim.Vim.final(Re.Reach.next(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, T.EvKey{"j"})), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})))), Re.Reach.step(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, T.EvKey{"j"}), Equal.cong(T.St, T.St, q => Vim.Vim.final(q), Re.Reach.next(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, T.EvKey{"j"}), Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i}))), PV.next(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left)))

def PV.e2(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})))) == Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), S.St.mode(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), T.VChars{}, p, T.File{i}))) : T.St}:
  Equal.cong(T.St, T.St, q => Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, q)), Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})), K.Key.revisual(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), S.St.mode(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), T.VChars{}, p, T.File{i}), Revis.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i}))

def PV.e3(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), S.St.mode(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), T.VChars{}, p, T.File{i}))) == Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), S.St.mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n))), T.VChars{}, p, T.File{i}))) : T.St}:
  Equal.cong(T.St, T.St, q => Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(q, S.St.mode(q), T.VChars{}, p, T.File{i}))), Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), Press.hn(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left))

def PV.e4(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), S.St.mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n))), T.VChars{}, p, T.File{i}))) == Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))) : T.St}:
  Equal.cong(T.St, T.St, q => Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, q)), K.Key.revisual(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), S.St.mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n))), T.VChars{}, p, T.File{i}), S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}), Revis.normal(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.VChars{}, p, i, GoLine.mode(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), GoLine.tgt(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n))))

def Press.vj(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat) -> {Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j") == Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))) : T.St}:
  Equal.trans(T.St, Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})))), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))), PV.e1(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left), Equal.trans(T.St, Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Laws.Spec.after(K.Key.revisual.step(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), T.VChars{}, p, T.File{i})))), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), S.St.mode(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), T.VChars{}, p, T.File{i}))), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))), PV.e2(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left), Equal.trans(T.St, Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j")), S.St.mode(Laws.Spec.after(K.Key.in_normal(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), T.VChars{}, p, T.File{i}))), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, K.Key.revisual(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), S.St.mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n))), T.VChars{}, p, T.File{i}))), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))), PV.e3(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left), PV.e4(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left))))

# v from a settled normal-mode editor on file i: visual mode from the cursor
def VJ.vnext(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat) -> {Re.Reach.next(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), T.EvKey{"v"}) == Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}) : T.St}:
  {==}

def VJ.vpress(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat) -> {Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v") == Vim.Vim.final(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})) : T.St}:
  Equal.trans(T.St, Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v"), Vim.Vim.final(Re.Reach.next(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), T.EvKey{"v"})), Vim.Vim.final(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), Re.Reach.step(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), T.EvKey{"v"}), Equal.cong(T.St, T.St, q => Vim.Vim.final(q), Re.Reach.next(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), T.EvKey{"v"}), Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}), VJ.vnext(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left)))

# a settled editor stays settled in visual mode: Final reads no mode
def VJ.fin(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}))) -> Fi.Final(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})):
  fin

def VJ.tail(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +p: T.Pos, +want: T.Want, +top: Nat, +left: Nat, e12: L.LE(12n, cols)) -> {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(Laws.F.cmd(Vim.Vim.frame(Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"))), "-- VISUAL --")) == True{} : Bool}:
  +name = {"-- VISUAL --" : String}
  +hl17 = Nat.is_le(17n, cols)
  %Equal.sym(T.St, Laws.Spec.press(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, "j"), Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))), Press.vj(files, folded, dirs, marks, spots, opened, bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, p, want, top, left)) : {Laws.Spec.implies(hl17, String.eq(Laws.F.cmd(Vim.Vim.frame(_)), name)) == True{} : Bool}
  %Equal.sym(String, Laws.F.cmd(Vim.Vim.frame(Vim.Vim.final(Vim.Vim.keep(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, S.St.set_mode(C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.Visual{T.VChars{}, p}))))), X.Text.cut(Vi.Vis.label(T.VChars{}), Nat.max(S.St.cols(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 12n)), Cmd.vis(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Visual{T.VChars{}, p}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, C.Win.go_line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}, Nat.add(C.St.line(T.St{files, folded, dirs, T.Win{T.File{i}, p, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat}), 1n)), T.VChars{}, p)) : {Laws.Spec.implies(hl17, String.eq(_, name)) == True{} : Bool}
  %Eb.Esc.max_back(cols, 12n, e12) : {Laws.Spec.implies(hl17, String.eq(X.Text.cut(Vi.Vis.label(T.VChars{}), _), name)) == True{} : Bool}
  Label.pick(hl17, T.VChars{}, cols, {==})

def VJ.state(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, +hr: {B.Tgt.real(files, T.File{i}) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})))
  -> {Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v") == Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}) : T.St}:
  Equal.trans(T.St, Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v"), Vim.Vim.final(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}), VJ.vpress(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left), Equal.sym(T.St, Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}), Vim.Vim.final(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), Yc.Settle.vis(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.File{i}, line, col, want, top, left, VJ.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left, fin), hr)))

def VJ.eta(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat) -> {T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, T.Visual{T.VChars{}, T.Pos{line, col}}, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat} == Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}) : T.St}:
  {==}

def VJ.mid(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +i: Nat, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, +hr: {B.Tgt.real(files, T.File{i}) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})))
  -> {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(Laws.F.cmd(Vim.Vim.frame(Laws.Spec.press(Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v"), "j"))), "-- VISUAL --")) == True{} : Bool}:
  (e3, r1) = fin
  (e12, r2) = r1
  %Equal.sym(T.St, Laws.Spec.press(Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, T.Pos{line, col}, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), "v"), Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left}), VJ.state(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left, hr, fin)) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(Laws.F.cmd(Vim.Vim.frame(Laws.Spec.press(_, "j"))), "-- VISUAL --")) == True{} : Bool}
  %VJ.eta(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left) : {Laws.Spec.implies(Nat.is_le(17n, cols), String.eq(Laws.F.cmd(Vim.Vim.frame(Laws.Spec.press(_, "j"))), "-- VISUAL --")) == True{} : Bool}
  VJ.tail(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, find, hl, opts, rows, cols, msg, stat, i, T.Pos{line, col}, C.Want.at(C.St.lines(Yc.Vis.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, T.Pos{line, col}, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left, e12)

def VJ.core(s: T.St, +hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s))) -> {Laws.Claim.v_j(Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              match cur:
                case T.Pos{+line, +col}:
                  VJ.mid(files, folded, dirs, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat, i, line, col, want, top, left, hr, fin)

def VJ.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.v_j(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.v_j(_) == True{} : Bool}
  VJ.core(n, Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def VisualLaws.v_j(fs, rows, cols, evs):
  VJ.law(fs, rows, cols, evs)
