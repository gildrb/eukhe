# eukhe.com's Neovim: the proof of LAW esc_idle
# =============================================
#
# Esc in normal mode only drops the waiting key and the count (and, with
# none waiting, the search highlight), so the editor it gives is Vim.final
# of one with the same window. That editor is settled and on a real
# buffer, which Vim.final keeps up to the column j and k aim for
# (Settle.self): the frame's target, first line and column and cursor are
# the same.

import Base
import ../../../vim/types.bend as T
import ../../../vim/st.bend as S
import ../../../vim/buf.bend as B
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/esc.bend as EscLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../screen/base.bend as Sb
import ./base.bend as Eb

# what Claim.esc_idle compares, of editors s and t
def EscIdle.cmp(+s: T.St, +t: T.St) -> Bool:
  +a = Vim.Vim.frame(s)
  +b = Vim.Vim.frame(t)
  Bool.and(Bool.and(Laws.Spec.same_tgt(Laws.F.tgt(a), Laws.F.tgt(b)), Bool.and(Nat.is_eq(Laws.F.top(a), Laws.F.top(b)), Nat.is_eq(Laws.F.left(a), Laws.F.left(b)))), Bool.and(Nat.is_eq(Laws.F.row(a), Laws.F.row(b)), Nat.is_eq(Laws.F.col(a), Laws.F.col(b))))

def EscIdle.refl(+t: T.Tgt, +top: Nat, +left: Nat, +row: Nat, +col: Nat) -> {Bool.and(Bool.and(Laws.Spec.same_tgt(t, t), Bool.and(Nat.is_eq(top, top), Nat.is_eq(left, left))), Bool.and(Nat.is_eq(row, row), Nat.is_eq(col, col))) == True{} : Bool}:
  L.And.intro(Bool.and(Laws.Spec.same_tgt(t, t), Bool.and(Nat.is_eq(top, top), Nat.is_eq(left, left))), Bool.and(Nat.is_eq(row, row), Nat.is_eq(col, col)),
    L.And.intro(Laws.Spec.same_tgt(t, t), Bool.and(Nat.is_eq(top, top), Nat.is_eq(left, left)), Eb.Esc.same_refl(t), L.And.intro(Nat.is_eq(top, top), Nat.is_eq(left, left), L.Nat.eq_refl(top), L.Nat.eq_refl(left))),
    L.And.intro(Nat.is_eq(row, row), Nat.is_eq(col, col), L.Nat.eq_refl(row), L.Nat.eq_refl(col)))

# the editor Esc gives (no key waiting, no count, highlight hl2) and the
# one it came from show the same
def EscIdle.fin(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +hl2: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String,
  tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat,
  fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})),
  hr: {B.Tgt.real(files, tgt) == True{} : Bool})
  -> {EscIdle.cmp(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}), Vim.Vim.final(Eb.Esc.at(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl2, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}))) == True{} : Bool}:
  match tgt:
    case T.File{+i}:
      +x = Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{T.File{i}, T.Pos{line, col}, want, top, left})
      +f = Vim.Vim.frame(x)
      %Eb.Settle.self(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl2, opts, rows, cols, msg, stat, T.File{i}, line, col, want, top, left, fin, hr) : {EscIdle.cmp(x, _) == True{} : Bool}
      EscIdle.refl(Laws.F.tgt(f), Laws.F.top(f), Laws.F.left(f), Laws.F.row(f), Laws.F.col(f))
    case T.Dir{+p}:
      +x = Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{T.Dir{p}, T.Pos{line, col}, want, top, left})
      +f = Vim.Vim.frame(x)
      %Eb.Settle.self(files, folded, dirs, marks, spots, Vim.Vim.opened(opened), bufs, back, fwd, 0n, T.NoPend{}, find, hl2, opts, rows, cols, msg, stat, T.Dir{p}, line, col, want, top, left, fin, hr) : {EscIdle.cmp(x, _) == True{} : Bool}
      EscIdle.refl(Laws.F.tgt(f), Laws.F.top(f), Laws.F.left(f), Laws.F.row(f), Laws.F.col(f))

# z and y wait for a key: Esc drops them (proven on an opaque editor, so
# the kernel never unfolds the zz/zt/zb or yank it skips)
def EscIdle.zkey(+s: T.St) -> {s == K.Key.zkey(s, "<Esc>") : T.St}:
  {==}

def EscIdle.ykey(+s: T.St, +n: Nat) -> {K.Key.ok(s) == K.Key.pend(s, T.PendY{}, "<Esc>", n) : T.Step}:
  {==}

# Esc after each waiting key
def EscIdle.NoPend(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.NoPend{}, find, hl, False{}, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

def EscIdle.PendG(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendG{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendG{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendG{}, find, hl, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

def EscIdle.PendZ(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  +x = Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})
  +x1 = S.St.set_count(S.St.set_pend(x, T.NoPend{}), 0n)
  %EscIdle.zkey(x1) : {EscIdle.cmp(x, Vim.Vim.final(Vim.Vim.keep(x, _))) == True{} : Bool}
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendZ{}, find, hl, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

def EscIdle.PendLead(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLead{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLead{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLead{}, find, hl, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

def EscIdle.PendLeadF(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLeadF{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLeadF{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLeadF{}, find, hl, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

def EscIdle.PendY(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat, fin: Fi.Final(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), hr: {B.Tgt.real(files, tgt) == True{} : Bool}) -> {Laws.Claim.esc_idle(Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) == True{} : Bool}:
  +x = Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})
  +x1 = S.St.set_count(S.St.set_pend(x, T.NoPend{}), 0n)
  %EscIdle.ykey(x1, count) : {EscIdle.cmp(x, Vim.Vim.final(Vim.Vim.keep(x, Laws.Spec.after(_)))) == True{} : Bool}
  EscIdle.fin(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendY{}, find, hl, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)

# Esc.at is the editor it names
def EscIdle.lit(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, +w: T.Win)
  -> {Eb.Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, w) == T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat} : T.St}:
  {==}

# the editor is in normal mode: no other mode is
def EscIdle.typing(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, -w: T.Win, -kind: T.Line, -text: String, hm: {T.Typing{kind, text} == T.Normal{} : T.Mode}) -> {Laws.Claim.esc_idle(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat}) == True{} : Bool}:
  Sb.Mode.typing({Laws.Claim.esc_idle(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat}) == True{} : Bool}, kind, text, hm)

def EscIdle.picking(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, -w: T.Win, -kind: T.Pick, -q: String, -its: List<&2, T.Item>, -n: Nat, -sel: Nat, -ptop: Nat, -pv: Nat, -levels: List<&2, T.Level>, hm: {T.Picking{kind, q, its, n, sel, ptop, pv, levels} == T.Normal{} : T.Mode}) -> {Laws.Claim.esc_idle(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Picking{kind, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}) == True{} : Bool}:
  Sb.Mode.picking({Laws.Claim.esc_idle(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Picking{kind, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}) == True{} : Bool}, kind, q, its, n, sel, ptop, pv, levels, hm)

# every settled normal-mode editor on a real buffer
def EscIdle.of(+s: T.St, fin: Fi.Final(s), hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, hm: {S.St.mode(s) == T.Normal{} : T.Mode}) -> {Laws.Claim.esc_idle(s) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match cur:
            case T.Pos{+line, +col}:
              match mode:
                case T.Normal{}:
                  match pend:
                    case T.NoPend{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.NoPend(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                    case T.PendG{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendG{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.PendG(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                    case T.PendZ{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.PendZ(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                    case T.PendLead{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLead{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.PendLead(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                    case T.PendLeadF{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendLeadF{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.PendLeadF(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                    case T.PendY{}:
                      %EscIdle.lit(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}) : {Laws.Claim.esc_idle(_) == True{} : Bool}
                      EscIdle.PendY(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, find, hl, opts, rows, cols, msg, stat, tgt, line, col, want, top, left, fin, hr)
                case T.Typing{kind, text}:
                  EscIdle.typing(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}, kind, text, hm)
                case T.Picking{kind, q, its, n, sel, ptop, pv, levels}:
                  EscIdle.picking(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left}, kind, q, its, n, sel, ptop, pv, levels, hm)

def EscIdle.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.esc_idle(Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +evs2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  EscIdle.of(Laws.Spec.normal(fs, rows, cols, evs), Re.Reach.final(fs, rows, cols, evs2), Eb.Esc.real_run(fs, rows, cols, evs2), Re.Reach.normal_mode(fs, rows, cols, evs))

def EscLaws.esc_idle(fs, rows, cols, evs):
  EscIdle.law(fs, rows, cols, evs)
