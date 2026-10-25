# eukhe: the proof of LAW sel_release_copies
#
# A release in a selection being made shows its range and copies M.copy
# of it; the other modes answer quietly. M.copy walks the release rows:
# the first row from the range's start column, the last to its end
# column, every row in between whole; the spec takes each row up to the
# range's last row. Row by row (src.* in ./sel_release_copies/row.bend)
# the model's piece spells the spec's tokens of that row; the newline
# before a row, the trailing-blank rule and the rows after the last row
# agree (rc.*).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS
import ./sel_release_copies/row.bend as LR

# Row facts
# ---------

def rc.le(k: Nat, +R: Nat, -r2: Nat, e: {Nat.add(k, R) == r2 : Nat}) -> {Nat.is_le(R, r2) == True{} : Bool}:
  %e : {Nat.is_le(R, _) == True{} : Bool}
  LS.ls.le_add(k, R)

def rc.lt(+k: Nat, +R: Nat, -r2: Nat, e: {Nat.add(1n+k, R) == r2 : Nat}) -> {Nat.is_lt(R, r2) == True{} : Bool}:
  %e : {Nat.is_lt(R, _) == True{} : Bool}
  LS.ls.le_lt_succ(R, Nat.add(k, R), LS.ls.le_add(k, R))

def rc.ne(+k: Nat, +R: Nat, +r2: Nat, e: {Nat.add(1n+k, R) == r2 : Nat}) -> {Nat.is_eq(R, r2) == False{} : Bool}:
  LS.ls.lt_ne(R, r2, rc.lt(k, R, r2, e))

def rc.nlt0(+R: Nat, -r2: Nat, e: {R == r2 : Nat}) -> {Nat.is_lt(R, r2) == False{} : Bool}:
  %e : {Nat.is_lt(R, _) == False{} : Bool}
  LS.ls.lt_irrefl(R)

def rc.eq0(+R: Nat, -r2: Nat, e: {R == r2 : Nat}) -> {Nat.is_eq(R, r2) == True{} : Bool}:
  %e : {Nat.is_eq(R, _) == True{} : Bool}
  LS.ls.eq_refl(R)

def rc.r1lt(+i: Nat, +r1: Nat) -> {Nat.is_lt(r1, Nat.add(1n+i, r1)) == True{} : Bool}:
  LS.ls.le_lt_succ(r1, Nat.add(i, r1), LS.ls.le_add(i, r1))

def rc.nle_succ(n: Nat) -> {Nat.is_le(1n+n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rc.nle_succ(p)

def rc.next_le(+X: Nat, -r2: Nat, e: {X == r2 : Nat}) -> {Nat.is_le(1n+X, r2) == False{} : Bool}:
  %e : {Nat.is_le(1n+X, _) == False{} : Bool}
  rc.nle_succ(X)

def rc.nlt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case p 0n:
      LS.ls.le_zero(p)
    case 0n 1n+q:
      LS.ls.absurd_t({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      rc.nlt_le(p, q, h)

def rc.sub_add(+r1: Nat, +r2: Nat, h: {Nat.is_le(r1, r2) == True{} : Bool}) -> {Nat.add(Nat.sub(r2, r1), r1) == r2 : Nat}:
  match r1 r2:
    case 0n q:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, LS.ls.sub_zero(q)) : {Nat.add(_, 0n) == q : Nat}
      LS.ls.add_zero(q)
    case 1n+p 0n:
      LS.ls.absurd({Nat.add(Nat.sub(0n, 1n+p), 1n+p) == 0n : Nat}, h)
    case 1n+p 1n+q:
      %Equal.sym(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), LS.ls.add_succ(Nat.sub(q, p), p)) : {_ == 1n+q : Nat}
      %rc.sub_add(p, q, h) : {1n+Nat.add(Nat.sub(q, p), p) == 1n+_ : Nat}
      {==}

# Rows
# ----

def rc.nl(w: M.Wrap, +i: Nat) -> {Selection.sl_nltok(Bool.and(Bool.not(False{}), M.not_cont(w))) == Selection.sl_nl(1n+i, w) : List<&2, Selection.SlTok>}:
  match w:
    case M.Single{}:
      {==}
    case M.Head{}:
      {==}
    case M.Cont{}:
      {==}

# the model's piece of a row spells the spec's tokens of the row
def rc.pe(gs: List<&2, Nat>, +I: Nat, +R: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +qb1: Bool, +qb2: Bool, +qa1: Bool, +qa2: Bool, eb1: {Nat.is_lt(R, r2) == qb1 : Bool}, eb2: {Nat.is_eq(R, r2) == qb2 : Bool}, ea1: {Nat.is_lt(r1, R) == qa1 : Bool}, ea2: {Nat.is_eq(r1, R) == qa2 : Bool}, hb: {Bool.or(qb1, qb2) == True{} : Bool}, ha: {Bool.or(qa1, qa2) == True{} : Bool}, +t: Bool) -> {LR.src.sp(M.row_lo(gs, 0n, 0n, LR.src.fromf(qa1, qa2, c1)), M.row_nb(gs, 0n, 0n, LR.src.tof(qb1, qb2, c2), t), I) == Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, M.Cell{r1, c1}, M.Cell{r2, c2}), t), I) : List<&2, Selection.SlTok>}:
  +gg = gs
  %Equal.sym(List<&2, Selection.SlGl>, Selection.sl_pick(gg, 0n, 0n, R, M.Cell{r1, c1}, M.Cell{r2, c2}), LR.src.colf(gg, 0n, 0n, LR.src.fromf(qa1, qa2, c1), LR.src.tof(qb1, qb2, c2)), LR.src.pick(gg, 0n, 0n, R, r1, c1, r2, c2, qb1, qb2, qa1, qa2, eb1, eb2, ea1, ea2, hb, ha)) : {LR.src.sp(M.row_lo(gg, 0n, 0n, LR.src.fromf(qa1, qa2, c1)), M.row_nb(gg, 0n, 0n, LR.src.tof(qb1, qb2, c2), t), I) == Selection.sl_toks(Selection.sl_keep(_, t), I) : List<&2, Selection.SlTok>}
  Equal.sym(List<&2, Selection.SlTok>, Selection.sl_toks(Selection.sl_keep(LR.src.colf(gg, 0n, 0n, LR.src.fromf(qa1, qa2, c1), LR.src.tof(qb1, qb2, c2)), t), I), LR.src.sp(M.row_lo(gg, 0n, 0n, LR.src.fromf(qa1, qa2, c1)), M.row_nb(gg, 0n, 0n, LR.src.tof(qb1, qb2, c2), t), I), LR.src.range(gg, 0n, 0n, LR.src.fromf(qa1, qa2, c1), LR.src.tof(qb1, qb2, c2), t, I))

# a model span from column 0 is empty exactly when its glyphs are none
def rc.blank_eq(N: Nat, xs: List<&2, Selection.SlGl>, +I: Nat, h: {LR.src.sp(0n, N, I) == Selection.sl_toks(xs, I) : List<&2, Selection.SlTok>}) -> {Nat.is_eq(N, 0n) == Selection.sl_blank(xs) : Bool}:
  match N xs:
    case 0n Nil{}:
      {==}
    case 0n Con{x, more}:
      match x:
        case Selection.SlGl{j, g}:
          LS.ls.cons_nil({True{} == False{} : Bool}, Selection.SlG{I, j}, Selection.sl_toks(more, I), Equal.sym(List<&2, Selection.SlTok>, Nil{}, Selection.SlG{I, j} <> Selection.sl_toks(more, I), h))
    case 1n+p Nil{}:
      LS.ls.cons_nil({False{} == True{} : Bool}, Selection.SlG{I, 0n}, Selection.sl_span(p, I, 1n), h)
    case 1n+p Con{x, more}:
      {==}

# a row of the range past its first: the model's blank test is the spec's
def rc.rowblank(gs: List<&2, Nat>, +R: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +qb1: Bool, +qb2: Bool, eb1: {Nat.is_lt(R, r2) == qb1 : Bool}, eb2: {Nat.is_eq(R, r2) == qb2 : Bool}, ea1: {Nat.is_lt(r1, R) == True{} : Bool}, hb: {Bool.or(qb1, qb2) == True{} : Bool}) -> {M.blank_to(gs, LR.src.tof(qb1, qb2, c2)) == Selection.sl_blank(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, M.Cell{r1, c1}, M.Cell{r2, c2}), True{})) : Bool}:
  +gg = gs
  +NB = M.row_nb(gg, 0n, 0n, LR.src.tof(qb1, qb2, c2), True{})
  +KEEP = Selection.sl_keep(Selection.sl_pick(gg, 0n, 0n, R, M.Cell{r1, c1}, M.Cell{r2, c2}), True{})
  +pe = rc.pe(gg, 0n, R, r1, c1, r2, c2, qb1, qb2, True{}, Nat.is_eq(r1, R), eb1, eb2, ea1, {==}, hb, {==}, True{})
  +lo = LR.src.lo_at(gg, 0n, 0n, None{}, {==})
  rc.blank_eq(NB, KEEP, 0n, (%lo : {LR.src.sp(_, NB, 0n) == Selection.sl_toks(KEEP, 0n) : List<&2, Selection.SlTok>}; pe))

def rc.and_t(b: Bool) -> {Bool.and(b, True{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rc.brk(w: M.Wrap) -> {M.not_cont(w) == Selection.sl_brk(w) : Bool}:
  match w:
    case M.Single{}:
      {==}
    case M.Head{}:
      {==}
    case M.Cont{}:
      {==}

def rc.lt_eq(+R: Nat, -r2: Nat, e: {R == r2 : Nat}) -> {Nat.is_lt(r2, 1n+R) == True{} : Bool}:
  %e : {Nat.is_lt(_, 1n+R) == True{} : Bool}
  LS.ls.le_lt_succ(R, R, LS.ls.le_refl(R))

def rc.nlt_eq(+R: Nat, -r2: Nat, e: {R == r2 : Nat}) -> {Nat.is_lt(r2, R) == False{} : Bool}:
  %e : {Nat.is_lt(_, R) == False{} : Bool}
  LS.ls.lt_irrefl(R)

def rc.lt_asym(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LS.ls.absurd({Nat.is_lt(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LS.ls.absurd({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      rc.lt_asym(p, q, h)

# rows past the range's last row leave the line's look at True
def rc.tail_past(rows: List<&2, M.Row>, +i: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +e: {Nat.add(1n+i, r1) == r2 : Nat}) -> {Selection.sl_tail_blank(rows, 2n+i, M.Cell{r1, c1}, M.Cell{r2, c2}) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{row, +rest}:
      match row:
        case M.Row{w, gs}:
          +R = Nat.add(1n+i, r1)
          %Equal.sym(Bool, Nat.is_lt(r2, 1n+R), True{}, rc.lt_eq(R, r2, e)) : {Bool.or(Bool.or(_, Selection.sl_brk(w)), Bool.and(Selection.sl_blank(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, 1n+R, M.Cell{r1, c1}, M.Cell{r2, c2}), True{})), Selection.sl_tail_blank(rest, 3n+i, M.Cell{r1, c1}, M.Cell{r2, c2}))) == True{} : Bool}
          {==}

# the model's look past a row at the rest of its line is the spec's (rows
# from index 1 + i on, k rows before the last)
def rc.tail(rows: List<&2, M.Row>, +i: Nat, k: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +e: {Nat.add(k, Nat.add(1n+i, r1)) == r2 : Nat}) -> {M.rest_blank(rows, k, c2) == Selection.sl_tail_blank(rows, 1n+i, M.Cell{r1, c1}, M.Cell{r2, c2}) : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{row, +more}:
      match row:
        case M.Row{+w, +gs}:
          match k:
            case 0n:
              +R = Nat.add(1n+i, r1)
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +BL = Selection.sl_blank(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), True{}))
              +nlt = rc.nlt_eq(R, r2, e)
              +rb = rc.rowblank(gs, R, r1, c1, r2, c2, False{}, True{}, rc.nlt0(R, r2, e), rc.eq0(R, r2, e), rc.r1lt(i, r1), {==})
              %Equal.sym(Bool, Nat.is_lt(r2, R), False{}, nlt) : {Bool.or(M.not_cont(w), M.blank_to(gs, Some{c2})) == Bool.or(Bool.or(_, Selection.sl_brk(w)), Bool.and(BL, Selection.sl_tail_blank(more, 2n+i, a, b))) : Bool}
              %Equal.sym(Bool, Selection.sl_tail_blank(more, 2n+i, a, b), True{}, rc.tail_past(more, i, r1, c1, r2, c2, e)) : {Bool.or(M.not_cont(w), M.blank_to(gs, Some{c2})) == Bool.or(Selection.sl_brk(w), Bool.and(BL, _)) : Bool}
              %Equal.sym(Bool, Bool.and(BL, True{}), BL, rc.and_t(BL)) : {Bool.or(M.not_cont(w), M.blank_to(gs, Some{c2})) == Bool.or(Selection.sl_brk(w), _) : Bool}
              %rc.brk(w) : {Bool.or(M.not_cont(w), M.blank_to(gs, Some{c2})) == Bool.or(_, BL) : Bool}
              %rb : {Bool.or(M.not_cont(w), M.blank_to(gs, Some{c2})) == Bool.or(M.not_cont(w), _) : Bool}
              {==}
            case 1n++m:
              +R = Nat.add(1n+i, r1)
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +BL = Selection.sl_blank(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), True{}))
              +lt = rc.lt(m, R, r2, e)
              +nlt = rc.lt_asym(R, r2, lt)
              +e2 = Equal.trans(Nat, Nat.add(m, Nat.add(2n+i, r1)), 1n+Nat.add(m, Nat.add(1n+i, r1)), r2, LS.ls.add_succ(m, Nat.add(1n+i, r1)), e)
              +rb = rc.rowblank(gs, R, r1, c1, r2, c2, True{}, Nat.is_eq(R, r2), lt, {==}, rc.r1lt(i, r1), {==})
              %Equal.sym(Bool, Nat.is_lt(r2, R), False{}, nlt) : {Bool.or(M.not_cont(w), Bool.and(M.blank_to(gs, None{}), M.rest_blank(more, m, c2))) == Bool.or(Bool.or(_, Selection.sl_brk(w)), Bool.and(BL, Selection.sl_tail_blank(more, 2n+i, a, b))) : Bool}
              %rc.tail(more, 1n+i, m, r1, c1, r2, c2, e2) : {Bool.or(M.not_cont(w), Bool.and(M.blank_to(gs, None{}), M.rest_blank(more, m, c2))) == Bool.or(Selection.sl_brk(w), Bool.and(BL, _)) : Bool}
              %rc.brk(w) : {Bool.or(M.not_cont(w), Bool.and(M.blank_to(gs, None{}), M.rest_blank(more, m, c2))) == Bool.or(_, Bool.and(BL, M.rest_blank(more, m, c2))) : Bool}
              %rb : {Bool.or(M.not_cont(w), Bool.and(M.blank_to(gs, None{}), M.rest_blank(more, m, c2))) == Bool.or(M.not_cont(w), Bool.and(_, M.rest_blank(more, m, c2))) : Bool}
              {==}

# the rows after the range's last row add nothing
def rc.tail_out(rows: List<&2, M.Row>, +i: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +e: {Nat.add(i, r1) == r2 : Nat}) -> {Selection.sl_rows(rows, 1n+i, M.Cell{r1, c1}, M.Cell{r2, c2}) == Nil{} : List<&2, Selection.SlTok>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +rest}:
      %Equal.sym(Bool, Nat.is_le(1n+Nat.add(i, r1), r2), False{}, rc.next_le(Nat.add(i, r1), r2, e)) : {Selection.sl_rows.k(_, Selection.sl_row(row, 1n+i, Nat.add(1n+i, r1), M.Cell{r1, c1}, M.Cell{r2, c2}, Bool.or(Nat.is_eq(Nat.add(1n+i, r1), r2), Selection.sl_tail_blank(rest, 2n+i, M.Cell{r1, c1}, M.Cell{r2, c2}))), Selection.sl_rows(rest, 2n+i, M.Cell{r1, c1}, M.Cell{r2, c2})) == Nil{} : List<&2, Selection.SlTok>}
      {==}

# rows from index 1 + i on, k rows before the last
def rc.w1(rows: List<&2, M.Row>, +i: Nat, k: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +e: {Nat.add(k, Nat.add(1n+i, r1)) == r2 : Nat}) -> {Selection.sl_expand(M.copy.go(rows, 1n+i, k, None{}, c2, False{})) == Selection.sl_rows(rows, 1n+i, M.Cell{r1, c1}, M.Cell{r2, c2}) : List<&2, Selection.SlTok>}:
  match rows:
    case Nil{}:
      {==}
    case Con{row, +rest}:
      match row:
        case M.Row{+w, +gs}:
          match k:
            case 0n:
              +R = Nat.add(1n+i, r1)
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +NL = Selection.sl_nltok(Bool.and(Bool.not(False{}), M.not_cont(w)))
              +SP = LR.src.sp(M.row_lo(gs, 0n, 0n, None{}), M.row_nb(gs, 0n, 0n, Some{c2}, True{}), 1n+i)
              +LHS = List.append(&2, Selection.SlTok, NL, List.append(&2, Selection.SlTok, SP, Nil{}))
              +TOKS = Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), True{}), 1n+i)
              %Equal.sym(Bool, Nat.is_le(R, r2), True{}, rc.le(0n, R, r2, e)) : {LHS == Selection.sl_rows.k(_, Selection.sl_row(M.Row{w, gs}, 1n+i, R, a, b, Bool.or(Nat.is_eq(R, r2), Selection.sl_tail_blank(rest, 2n+i, a, b))), Selection.sl_rows(rest, 2n+i, a, b)) : List<&2, Selection.SlTok>}
              %Equal.sym(Bool, Nat.is_eq(R, r2), True{}, rc.eq0(R, r2, e)) : {LHS == List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), Bool.or(_, Selection.sl_tail_blank(rest, 2n+i, a, b))), 1n+i)), Selection.sl_rows(rest, 2n+i, a, b)) : List<&2, Selection.SlTok>}
              %Equal.sym(List<&2, Selection.SlTok>, Selection.sl_rows(rest, 2n+i, a, b), Nil{}, rc.tail_out(rest, 1n+i, r1, c1, r2, c2, e)) : {LHS == List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), TOKS), _) : List<&2, Selection.SlTok>}
              %Equal.sym(List<&2, Selection.SlTok>, List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), TOKS), Nil{}), List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), List.append(&2, Selection.SlTok, TOKS, Nil{})), LS.ls.app_assoc(Selection.sl_nl(1n+i, w), TOKS, Nil{})) : {LHS == _ : List<&2, Selection.SlTok>}
              %rc.nl(w, i) : {LHS == List.append(&2, Selection.SlTok, _, List.append(&2, Selection.SlTok, TOKS, Nil{})) : List<&2, Selection.SlTok>}
              %rc.pe(gs, 1n+i, R, r1, c1, r2, c2, False{}, True{}, True{}, Nat.is_eq(r1, R), rc.nlt0(R, r2, e), rc.eq0(R, r2, e), rc.r1lt(i, r1), {==}, {==}, {==}, True{}) : {LHS == List.append(&2, Selection.SlTok, NL, List.append(&2, Selection.SlTok, _, Nil{})) : List<&2, Selection.SlTok>}
              {==}
            case 1n++j:
              +R = Nat.add(1n+i, r1)
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +T = M.rest_blank(rest, j, c2)
              +NL = Selection.sl_nltok(Bool.and(Bool.not(False{}), M.not_cont(w)))
              +SP = LR.src.sp(M.row_lo(gs, 0n, 0n, None{}), M.row_nb(gs, 0n, 0n, None{}, T), 1n+i)
              +MORE = Selection.sl_expand(M.copy.go(rest, 2n+i, j, None{}, c2, False{}))
              +LHS = List.append(&2, Selection.SlTok, NL, List.append(&2, Selection.SlTok, SP, MORE))
              +TOKS = Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), T), 1n+i)
              +TAIL = Selection.sl_rows(rest, 2n+i, a, b)
              %Equal.sym(Bool, Nat.is_le(R, r2), True{}, rc.le(1n+j, R, r2, e)) : {LHS == Selection.sl_rows.k(_, Selection.sl_row(M.Row{w, gs}, 1n+i, R, a, b, Bool.or(Nat.is_eq(R, r2), Selection.sl_tail_blank(rest, 2n+i, a, b))), TAIL) : List<&2, Selection.SlTok>}
              %Equal.sym(Bool, Nat.is_eq(R, r2), False{}, rc.ne(j, R, r2, e)) : {LHS == List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), Bool.or(_, Selection.sl_tail_blank(rest, 2n+i, a, b))), 1n+i)), TAIL) : List<&2, Selection.SlTok>}
              %rc.tail(rest, 1n+i, j, r1, c1, r2, c2, Equal.trans(Nat, Nat.add(j, Nat.add(2n+i, r1)), 1n+Nat.add(j, Nat.add(1n+i, r1)), r2, LS.ls.add_succ(j, Nat.add(1n+i, r1)), e)) : {LHS == List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, R, a, b), _), 1n+i)), TAIL) : List<&2, Selection.SlTok>}
              %Equal.sym(List<&2, Selection.SlTok>, List.append(&2, Selection.SlTok, List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), TOKS), TAIL), List.append(&2, Selection.SlTok, Selection.sl_nl(1n+i, w), List.append(&2, Selection.SlTok, TOKS, TAIL)), LS.ls.app_assoc(Selection.sl_nl(1n+i, w), TOKS, TAIL)) : {LHS == _ : List<&2, Selection.SlTok>}
              %rc.nl(w, i) : {LHS == List.append(&2, Selection.SlTok, _, List.append(&2, Selection.SlTok, TOKS, TAIL)) : List<&2, Selection.SlTok>}
              %rc.pe(gs, 1n+i, R, r1, c1, r2, c2, True{}, Nat.is_eq(R, r2), True{}, Nat.is_eq(r1, R), rc.lt(j, R, r2, e), {==}, rc.r1lt(i, r1), {==}, {==}, {==}, T) : {LHS == List.append(&2, Selection.SlTok, NL, List.append(&2, Selection.SlTok, _, TAIL)) : List<&2, Selection.SlTok>}
              %rc.w1(rest, 1n+i, j, r1, c1, r2, c2, Equal.trans(Nat, Nat.add(j, Nat.add(2n+i, r1)), 1n+Nat.add(j, Nat.add(1n+i, r1)), r2, LS.ls.add_succ(j, Nat.add(1n+i, r1)), e)) : {LHS == List.append(&2, Selection.SlTok, NL, List.append(&2, Selection.SlTok, SP, _)) : List<&2, Selection.SlTok>}
              {==}

# the first row of the range, k rows before the last
def rc.w0(rows: List<&2, M.Row>, k: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +e: {Nat.add(k, r1) == r2 : Nat}) -> {Selection.sl_expand(M.copy.go(rows, 0n, k, Some{c1}, c2, True{})) == Selection.sl_rows(rows, 0n, M.Cell{r1, c1}, M.Cell{r2, c2}) : List<&2, Selection.SlTok>}:
  match rows:
    case Nil{}:
      {==}
    case Con{row, +rest}:
      match row:
        case M.Row{+w, +gs}:
          match k:
            case 0n:
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +SP = LR.src.sp(M.row_lo(gs, 0n, 0n, Some{c1}), M.row_nb(gs, 0n, 0n, Some{c2}, True{}), 0n)
              +LHS = List.append(&2, Selection.SlTok, SP, Nil{})
              +TOKS = Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r1, a, b), True{}), 0n)
              %Equal.sym(Bool, Nat.is_le(r1, r2), True{}, rc.le(0n, r1, r2, e)) : {LHS == Selection.sl_rows.k(_, Selection.sl_row(M.Row{w, gs}, 0n, r1, a, b, Bool.or(Nat.is_eq(r1, r2), Selection.sl_tail_blank(rest, 1n, a, b))), Selection.sl_rows(rest, 1n, a, b)) : List<&2, Selection.SlTok>}
              %Equal.sym(Bool, Nat.is_eq(r1, r2), True{}, rc.eq0(r1, r2, e)) : {LHS == List.append(&2, Selection.SlTok, Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r1, a, b), Bool.or(_, Selection.sl_tail_blank(rest, 1n, a, b))), 0n), Selection.sl_rows(rest, 1n, a, b)) : List<&2, Selection.SlTok>}
              %Equal.sym(List<&2, Selection.SlTok>, Selection.sl_rows(rest, 1n, a, b), Nil{}, rc.tail_out(rest, 0n, r1, c1, r2, c2, e)) : {LHS == List.append(&2, Selection.SlTok, TOKS, _) : List<&2, Selection.SlTok>}
              %rc.pe(gs, 0n, r1, r1, c1, r2, c2, False{}, True{}, False{}, True{}, rc.nlt0(r1, r2, e), rc.eq0(r1, r2, e), LS.ls.lt_irrefl(r1), LS.ls.eq_refl(r1), {==}, {==}, True{}) : {LHS == List.append(&2, Selection.SlTok, _, Nil{}) : List<&2, Selection.SlTok>}
              {==}
            case 1n++j:
              +a = {M.Cell{r1, c1} : M.Cell}
              +b = {M.Cell{r2, c2} : M.Cell}
              +T = M.rest_blank(rest, j, c2)
              +SP = LR.src.sp(M.row_lo(gs, 0n, 0n, Some{c1}), M.row_nb(gs, 0n, 0n, None{}, T), 0n)
              +MORE = Selection.sl_expand(M.copy.go(rest, 1n, j, None{}, c2, False{}))
              +LHS = List.append(&2, Selection.SlTok, SP, MORE)
              +TOKS = Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r1, a, b), T), 0n)
              +TAIL = Selection.sl_rows(rest, 1n, a, b)
              %Equal.sym(Bool, Nat.is_le(r1, r2), True{}, rc.le(1n+j, r1, r2, e)) : {LHS == Selection.sl_rows.k(_, Selection.sl_row(M.Row{w, gs}, 0n, r1, a, b, Bool.or(Nat.is_eq(r1, r2), Selection.sl_tail_blank(rest, 1n, a, b))), TAIL) : List<&2, Selection.SlTok>}
              %Equal.sym(Bool, Nat.is_eq(r1, r2), False{}, rc.ne(j, r1, r2, e)) : {LHS == List.append(&2, Selection.SlTok, Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r1, a, b), Bool.or(_, Selection.sl_tail_blank(rest, 1n, a, b))), 0n), TAIL) : List<&2, Selection.SlTok>}
              %rc.tail(rest, 0n, j, r1, c1, r2, c2, Equal.trans(Nat, Nat.add(j, 1n+r1), 1n+Nat.add(j, r1), r2, LS.ls.add_succ(j, r1), e)) : {LHS == List.append(&2, Selection.SlTok, Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r1, a, b), _), 0n), TAIL) : List<&2, Selection.SlTok>}
              %rc.pe(gs, 0n, r1, r1, c1, r2, c2, True{}, Nat.is_eq(r1, r2), False{}, True{}, rc.lt(j, r1, r2, e), {==}, LS.ls.lt_irrefl(r1), LS.ls.eq_refl(r1), {==}, {==}, T) : {LHS == List.append(&2, Selection.SlTok, _, TAIL) : List<&2, Selection.SlTok>}
              %rc.w1(rest, 0n, j, r1, c1, r2, c2, Equal.trans(Nat, Nat.add(j, 1n+r1), 1n+Nat.add(j, r1), r2, LS.ls.add_succ(j, r1), e)) : {LHS == List.append(&2, Selection.SlTok, SP, _) : List<&2, Selection.SlTok>}
              {==}

def rc.copy.k(bl: Bool, rows: List<&2, M.Row>, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, eb: {Nat.is_lt(r2, r1) == bl : Bool}) -> {Selection.sl_expand(M.copy.rows(bl, rows, Nat.sub(r2, r1), c1, c2)) == Selection.sl_rows(rows, 0n, M.Cell{r1, c1}, M.Cell{r2, c2}) : List<&2, Selection.SlTok>}:
  match bl:
    case True{}:
      match rows:
        case Nil{}:
          {==}
        case Con{+row, +rest}:
          %Equal.sym(Bool, Nat.is_le(r1, r2), False{}, LS.ls.lt_not_le(r2, r1, eb)) : {Nil{} == Selection.sl_rows.k(_, Selection.sl_row(row, 0n, r1, M.Cell{r1, c1}, M.Cell{r2, c2}, Bool.or(Nat.is_eq(r1, r2), Selection.sl_tail_blank(rest, 1n, M.Cell{r1, c1}, M.Cell{r2, c2}))), Selection.sl_rows(rest, 1n, M.Cell{r1, c1}, M.Cell{r2, c2})) : List<&2, Selection.SlTok>}
          {==}
    case False{}:
      rc.w0(rows, Nat.sub(r2, r1), r1, c1, r2, c2, rc.sub_add(r1, r2, rc.nlt_le(r2, r1, eb)))

# the pieces of a range spell the spec's copy of it
def rc.copy(r: M.Rng, rows: List<&2, M.Row>) -> {Selection.sl_expand(M.copy(r, rows)) == Selection.sl_copy(r, rows) : List<&2, Selection.SlTok>}:
  match r:
    case M.Rng{a, b}:
      match a:
        case M.Cell{+r1, +c1}:
          match b:
            case M.Cell{+r2, +c2}:
              rc.copy.k(Nat.is_lt(r2, r1), rows, r1, c1, r2, c2, {==})

def Selection.sel_release_copies(m, last, rows):
  match m:
    case M.Idle{}:
      ({==}, {==})
    case M.Pressed{a}:
      ({==}, {==})
    case M.Selecting{a, h}:
      match a:
        case M.Cell{+ar, +ac}:
          match h:
            case M.Cell{+hr, +hc}:
              +o = M.order(M.Cell{ar, ac}, M.Cell{hr, hc})
              (Equal.cong(List<&2, Selection.SlTok>, Maybe<&2, List<&2, Selection.SlTok>>, xs => Some{xs}, Selection.sl_expand(M.copy(o, rows)), Selection.sl_copy(o, rows), rc.copy(o, rows)), {==})
    case M.Picked{r}:
      +g = r
      (Equal.cong(List<&2, Selection.SlTok>, Maybe<&2, List<&2, Selection.SlTok>>, xs => Some{xs}, Selection.sl_expand(M.copy(g, rows)), Selection.sl_copy(g, rows), rc.copy(g, rows)), {==})
    case M.Shown{r}:
      ({==}, {==})
