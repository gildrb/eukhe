# eukhe: the proof of LAW screen_ffi_exact
# The entry reads every input as the spec's reader does (each item reader
# is the spec's, so each list reader is) and answers what the spec
# decides: the model's run, pace, stack and paint are the spec's, spelled
# as the spec spells them.

import Base
import ../../bend/ffi_screen.bend as FSc
import ../../bend/screen.bend as Sc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/screen/interface.bend as Screen
import ../../laws/screen/requirement.bend as ScreenRequirement
import ./pace_reveal_formula.bend as PPaceRevealFormula

# The transcript
# --------------

def scx.one(g: Maybe<&2, Nat>, i: Nat, s: Sc.St, l: Nat) -> {Sc.edit.one(Sc.Blk{i, s, l}, g) == ScreenRequirement.sc_sp_change(g, i, s, l) : Sc.Blk}:
  match g:
    case None{}:
      match s:
        case Sc.Active{}:
          {==}
        case Sc.Final{}:
          {==}
        case Sc.Comm{}:
          {==}
    case Some{n}:
      match s:
        case Sc.Active{}:
          {==}
        case Sc.Final{}:
          {==}
        case Sc.Comm{}:
          {==}

def scx.edit_at(hit: Bool, +i: Nat, +s: Sc.St, +l: Nat, -rest: List<&2, Sc.Blk>, -x: Nat, +g: Maybe<&2, Nat>, ih: {Sc.edit(rest, x, g) == ScreenRequirement.sc_sp_edit(rest, x, g) : List<&2, Sc.Blk>}) -> {Sc.edit.go(Sc.Blk{i, s, l} <> rest, x, g, hit) == ScreenRequirement.sc_sp_edit.at(hit, g, i, s, l) <> ScreenRequirement.sc_sp_edit(rest, x, g) : List<&2, Sc.Blk>}:
  match hit:
    case True{}:
      %Equal.sym(Sc.Blk, Sc.edit.one(Sc.Blk{i, s, l}, g), ScreenRequirement.sc_sp_change(g, i, s, l), scx.one(g, i, s, l)) : {_ <> Sc.edit(rest, x, g) == ScreenRequirement.sc_sp_change(g, i, s, l) <> ScreenRequirement.sc_sp_edit(rest, x, g) : List<&2, Sc.Blk>}
      %Equal.sym(List<&2, Sc.Blk>, Sc.edit(rest, x, g), ScreenRequirement.sc_sp_edit(rest, x, g), ih) : {ScreenRequirement.sc_sp_change(g, i, s, l) <> _ == ScreenRequirement.sc_sp_change(g, i, s, l) <> ScreenRequirement.sc_sp_edit(rest, x, g) : List<&2, Sc.Blk>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Sc.Blk>, Sc.edit(rest, x, g), ScreenRequirement.sc_sp_edit(rest, x, g), ih) : {Sc.Blk{i, s, l} <> _ == Sc.Blk{i, s, l} <> ScreenRequirement.sc_sp_edit(rest, x, g) : List<&2, Sc.Blk>}
      {==}

def scx.edit(bs: List<&2, Sc.Blk>, +x: Nat, +g: Maybe<&2, Nat>) -> {Sc.edit(bs, x, g) == ScreenRequirement.sc_sp_edit(bs, x, g) : List<&2, Sc.Blk>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Sc.Blk{+i, +s, +l}:
          scx.edit_at(Nat.is_eq(i, x), i, s, l, rest, x, g, scx.edit(rest, x, g))

def scx.flush(bs: List<&2, Sc.Blk>) -> {Sc.flush(bs) == ScreenRequirement.sc_sp_flush(bs) : List<&2, Sc.Blk>}:
  match bs:
    case Nil{}:
      {==}
    case b <> +rest:
      match b:
        case Sc.Blk{i, s, l}:
          match s:
            case Sc.Comm{}:
              %Equal.sym(List<&2, Sc.Blk>, Sc.flush(rest), ScreenRequirement.sc_sp_flush(rest), scx.flush(rest)) : {Sc.Blk{i, Sc.Comm{}, l} <> _ == Sc.Blk{i, Sc.Comm{}, l} <> ScreenRequirement.sc_sp_flush(rest) : List<&2, Sc.Blk>}
              {==}
            case Sc.Final{}:
              %Equal.sym(List<&2, Sc.Blk>, Sc.flush(rest), ScreenRequirement.sc_sp_flush(rest), scx.flush(rest)) : {Sc.Blk{i, Sc.Comm{}, l} <> _ == Sc.Blk{i, Sc.Comm{}, l} <> ScreenRequirement.sc_sp_flush(rest) : List<&2, Sc.Blk>}
              {==}
            case Sc.Active{}:
              {==}

def scx.step(t: Sc.Tx, e: Sc.Ev) -> {Sc.step(t, e) == ScreenRequirement.sc_sp_step(t, e) : Sc.Tx}:
  match t:
    case Sc.Tx{+bs, +n, +w}:
      match e:
        case Sc.Open{}:
          {==}
        case Sc.Grow{+x, +k}:
          %Equal.sym(List<&2, Sc.Blk>, Sc.edit(bs, x, Some{k}), ScreenRequirement.sc_sp_edit(bs, x, Some{k}), scx.edit(bs, x, Some{k})) : {Sc.Tx{_, n, w} == Sc.Tx{ScreenRequirement.sc_sp_edit(bs, x, Some{k}), n, w} : Sc.Tx}
          {==}
        case Sc.Fin{+x}:
          %Equal.sym(List<&2, Sc.Blk>, Sc.edit(bs, x, None{}), ScreenRequirement.sc_sp_edit(bs, x, None{}), scx.edit(bs, x, None{})) : {Sc.Tx{_, n, w} == Sc.Tx{ScreenRequirement.sc_sp_edit(bs, x, None{}), n, w} : Sc.Tx}
          {==}
        case Sc.Flush{}:
          %Equal.sym(List<&2, Sc.Blk>, Sc.flush(bs), ScreenRequirement.sc_sp_flush(bs), scx.flush(bs)) : {Sc.Tx{_, n, w} == Sc.Tx{ScreenRequirement.sc_sp_flush(bs), n, w} : Sc.Tx}
          {==}
        case Sc.Resize{v}:
          {==}

def scx.run(es: List<&2, Sc.Ev>, +t: Sc.Tx) -> {Sc.run(es, t) == ScreenRequirement.sc_sp_run(es, t) : Sc.Tx}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %Equal.sym(Sc.Tx, Sc.step(t, e), ScreenRequirement.sc_sp_step(t, e), scx.step(t, e)) : {Sc.run(rest, _) == ScreenRequirement.sc_sp_run(rest, ScreenRequirement.sc_sp_step(t, e)) : Sc.Tx}
      scx.run(rest, ScreenRequirement.sc_sp_step(t, e))

# The stack
# ---------

def scx.stack(hs: List<&2, Nat>, +y: Nat, +rows: Nat) -> {Sc.vstack(hs, y, rows) == ScreenRequirement.sc_sp_stack(hs, y, rows) : List<&2, Sc.Rect>}:
  match hs:
    case Nil{}:
      {==}
    case +h <> +rest:
      %Equal.sym(List<&2, Sc.Rect>, Sc.vstack(rest, Nat.add(y, h), rows), ScreenRequirement.sc_sp_stack(rest, Nat.add(y, h), rows), scx.stack(rest, Nat.add(y, h), rows)) : {Sc.Rect{y, Nat.min(h, Nat.sub(rows, y))} <> _ == ScreenRequirement.sc_sp_stack(h <> rest, y, rows) : List<&2, Sc.Rect>}
      {==}

# The paint
# ---------

def scx.decide(ks: List<&2, Bool>) -> {FSc.paint.decide(ks) == ScreenRequirement.sc_sp_decide(ks) : Maybe<&2, Sc.Paint>}:
  match ks:
    case Nil{}:
      {==}
    case a <> r1:
      match a:
        case True{}:
          match r1:
            case Nil{}:
              {==}
            case b <> r2:
              match r2:
                case Nil{}:
                  {==}
                case c <> r3:
                  match r3:
                    case Nil{}:
                      {==}
                    case d <> r4:
                      {==}
        case False{}:
          match r1:
            case Nil{}:
              {==}
            case b <> r2:
              match b:
                case True{}:
                  match r2:
                    case Nil{}:
                      {==}
                    case c <> r3:
                      match r3:
                        case Nil{}:
                          {==}
                        case d <> r4:
                          {==}
                case False{}:
                  match r2:
                    case Nil{}:
                      {==}
                    case c <> r3:
                      match c:
                        case True{}:
                          match r3:
                            case Nil{}:
                              {==}
                            case d <> r4:
                              {==}
                        case False{}:
                          match r3:
                            case Nil{}:
                              {==}
                            case d <> r4:
                              {==}

def scx.put_step(m: Maybe<&2, Sc.Paint>) -> {FSc.put_step(m, SNil{}) == ScreenRequirement.sc_sp_put_step(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{p}:
      match p:
        case Sc.Put{f, full}:
          {==}
        case Sc.Fresh{f}:
          {==}
        case Sc.Kept{f}:
          {==}

def scx.paint_fit(b: Bool, +ks: List<&2, Bool>) -> {FSc.paint.reply.fit(b, ks) == ScreenRequirement.sc_sp_paint.fit(b, ks) : String}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Sc.Paint>, FSc.paint.decide(ks), ScreenRequirement.sc_sp_decide(ks), scx.decide(ks)) : {FSc.put_step(_, SNil{}) == ScreenRequirement.sc_sp_paint.fit(True{}, ks) : String}
      scx.put_step(ScreenRequirement.sc_sp_decide(ks))
    case False{}:
      {==}

# The spellings
# -------------

def scx.blk(b: Sc.Blk, -rest: String) -> {FSc.put_blk(b, rest) == ScreenRequirement.sc_sp_put_blk(b, rest) : String}:
  match b:
    case Sc.Blk{i, s, l}:
      match s:
        case Sc.Active{}:
          {==}
        case Sc.Final{}:
          {==}
        case Sc.Comm{}:
          {==}

def scx.rect(r: Sc.Rect, -rest: String) -> {FSc.put_rect(r, rest) == ScreenRequirement.sc_sp_put_rect(r, rest) : String}:
  match r:
    case Sc.Rect{y, h}:
      {==}

def scx.blks_go(xs: List<&2, Sc.Blk>, -rest: String) -> {Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, xs, rest) == (List.length(&2, Sc.Blk, xs), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, t, rest), (List.length(&2, Sc.Blk, t), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest)), scx.blks_go(t, rest)) : {Wr.put_list.step(~Sc.Blk, ~FSc.put_blk, x, _) == (1n+List.length(&2, Sc.Blk, t), ScreenRequirement.sc_sp_put_blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest))) : Nat & String}
      %Equal.sym(String, FSc.put_blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest)), ScreenRequirement.sc_sp_put_blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest)), scx.blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest))) : {(1n+List.length(&2, Sc.Blk, t), _) == (1n+List.length(&2, Sc.Blk, t), ScreenRequirement.sc_sp_put_blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest))) : Nat & String}
      {==}

def scx.blks_go_sp(xs: List<&2, Sc.Blk>, -rest: String) -> {Wr.put_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest) == (List.length(&2, Sc.Blk, xs), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest), (List.length(&2, Sc.Blk, t), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest)), scx.blks_go_sp(t, rest)) : {Wr.put_list.step(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, x, _) == (1n+List.length(&2, Sc.Blk, t), ScreenRequirement.sc_sp_put_blk(x, LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, t, rest))) : Nat & String}
      {==}

def scx.blks(+xs: List<&2, Sc.Blk>, +rest: String) -> {Wr.put_list(~Sc.Blk, ~FSc.put_blk, xs, rest) == Wr.put_list(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~FSc.put_blk, xs, rest), (List.length(&2, Sc.Blk, xs), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest)), scx.blks_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest), (List.length(&2, Sc.Blk, xs), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest)), scx.blks_go_sp(xs, rest)) : {Wr.put_list.fin((List.length(&2, Sc.Blk, xs), LawsBase.wire_put_items(~Sc.Blk, ~ScreenRequirement.sc_sp_put_blk, xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

def scx.rects_go(xs: List<&2, Sc.Rect>, -rest: String) -> {Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, xs, rest) == (List.length(&2, Sc.Rect, xs), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, t, rest), (List.length(&2, Sc.Rect, t), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest)), scx.rects_go(t, rest)) : {Wr.put_list.step(~Sc.Rect, ~FSc.put_rect, x, _) == (1n+List.length(&2, Sc.Rect, t), ScreenRequirement.sc_sp_put_rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest))) : Nat & String}
      %Equal.sym(String, FSc.put_rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest)), ScreenRequirement.sc_sp_put_rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest)), scx.rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest))) : {(1n+List.length(&2, Sc.Rect, t), _) == (1n+List.length(&2, Sc.Rect, t), ScreenRequirement.sc_sp_put_rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest))) : Nat & String}
      {==}

def scx.rects_go_sp(xs: List<&2, Sc.Rect>, -rest: String) -> {Wr.put_list.go(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest) == (List.length(&2, Sc.Rect, xs), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest), (List.length(&2, Sc.Rect, t), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest)), scx.rects_go_sp(t, rest)) : {Wr.put_list.step(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, x, _) == (1n+List.length(&2, Sc.Rect, t), ScreenRequirement.sc_sp_put_rect(x, LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, t, rest))) : Nat & String}
      {==}

def scx.rects(+xs: List<&2, Sc.Rect>, +rest: String) -> {Wr.put_list(~Sc.Rect, ~FSc.put_rect, xs, rest) == Wr.put_list(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~FSc.put_rect, xs, rest), (List.length(&2, Sc.Rect, xs), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest)), scx.rects_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest), (List.length(&2, Sc.Rect, xs), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest)), scx.rects_go_sp(xs, rest)) : {Wr.put_list.fin((List.length(&2, Sc.Rect, xs), LawsBase.wire_put_items(~Sc.Rect, ~ScreenRequirement.sc_sp_put_rect, xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

def scx.tx(t: Sc.Tx) -> {FSc.put_tx(t, SNil{}) == ScreenRequirement.sc_sp_put_tx(t) : String}:
  match t:
    case Sc.Tx{+bs, +n, +w}:
      scx.blks(bs, Wr.put_nat(n, Wr.put_nat(w, "")))

def scx.answer(q: FSc.Req) -> {FSc.answer(q) == ScreenRequirement.sc_sp_answer(q) : String}:
  match q:
    case FSc.ReqRun{+t, +es}:
      %Equal.sym(Sc.Tx, Sc.run(es, t), ScreenRequirement.sc_sp_run(es, t), scx.run(es, t)) : {FSc.put_tx(_, SNil{}) == ScreenRequirement.sc_sp_answer(FSc.ReqRun{t, es}) : String}
      scx.tx(ScreenRequirement.sc_sp_run(es, t))
    case FSc.ReqPace{+min, +k, p, +n}:
      match p:
        case Sc.Pace{+r, +s}:
          %Equal.sym(Nat, Sc.reveal(min, k, Nat.sub(Nat.add(r, n), s)), Nat.min(Nat.sub(Nat.add(r, n), s), Nat.max(min, Nat.div(Nat.sub(Nat.add(r, n), s), 1n+k))), Screen.pace_reveal_formula(min, k, Nat.sub(Nat.add(r, n), s))) : {Wr.put_nat(Nat.add(r, n), Wr.put_nat(Nat.add(s, _), SNil{})) == ScreenRequirement.sc_sp_answer(FSc.ReqPace{min, k, Sc.Pace{r, s}, n}) : String}
          {==}
    case FSc.ReqStack{+hs, +y, +rows}:
      %Equal.sym(List<&2, Sc.Rect>, Sc.vstack(hs, y, rows), ScreenRequirement.sc_sp_stack(hs, y, rows), scx.stack(hs, y, rows)) : {Wr.put_list(~Sc.Rect, ~FSc.put_rect, _, SNil{}) == ScreenRequirement.sc_sp_answer(FSc.ReqStack{hs, y, rows}) : String}
      scx.rects(ScreenRequirement.sc_sp_stack(hs, y, rows), "")
    case FSc.ReqPaint{+ks}:
      scx.paint_fit(Nat.is_le(List.length(&2, Bool, ks), 3n), ks)

# The reader
# ----------

def scx.st_tag(n: Nat, s: String) -> {FSc.get_st.tag(n, s) == ScreenRequirement.sc_sp_st.tag(n, s) : Wr.Dec<Sc.St>}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def scx.st(r: Wr.Dec<Nat>) -> {FSc.get_st.of(r) == ScreenRequirement.sc_sp_st.of(r) : Wr.Dec<Sc.St>}:
  match r:
    case Wr.Got{n, s}:
      scx.st_tag(n, s)
    case Wr.Bad{}:
      {==}

def scx.blk_len(i: Nat, st: Sc.St, r: Wr.Dec<Nat>) -> {FSc.get_blk.len(i, st, r) == ScreenRequirement.sc_sp_blk.len(i, st, r) : Wr.Dec<Sc.Blk>}:
  match r:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.blk_st(i: Nat, r: Wr.Dec<Sc.St>) -> {FSc.get_blk.st(i, r) == ScreenRequirement.sc_sp_blk.st(i, r) : Wr.Dec<Sc.Blk>}:
  match r:
    case Wr.Got{st, s}:
      scx.blk_len(i, st, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.blk_id(r: Wr.Dec<Nat>) -> {FSc.get_blk.id(r) == ScreenRequirement.sc_sp_blk.id(r) : Wr.Dec<Sc.Blk>}:
  match r:
    case Wr.Got{+i, +s}:
      %Equal.sym(Wr.Dec<Sc.St>, FSc.get_st.of(Wr.get_nat(s)), ScreenRequirement.sc_sp_st.of(Wr.get_nat(s)), scx.st(Wr.get_nat(s))) : {FSc.get_blk.st(i, _) == ScreenRequirement.sc_sp_blk.id(Wr.Got{i, s}) : Wr.Dec<Sc.Blk>}
      scx.blk_st(i, ScreenRequirement.sc_sp_st.of(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def scx.blk_r(s: String) -> {FSc.get_blk(s) == ScreenRequirement.sc_sp_blk(s) : Wr.Dec<Sc.Blk>}:
  scx.blk_id(Wr.get_nat(s))

def scx.ev_one(r: Wr.Dec<Nat>) -> {FSc.get_ev.one(r) == ScreenRequirement.sc_sp_ev.one(r) : Wr.Dec<Sc.Ev>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.ev_w(r: Wr.Dec<Nat>) -> {FSc.get_ev.w(r) == ScreenRequirement.sc_sp_ev.w(r) : Wr.Dec<Sc.Ev>}:
  match r:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.ev_n(x: Nat, r: Wr.Dec<Nat>) -> {FSc.get_ev.n(x, r) == ScreenRequirement.sc_sp_ev.n(x, r) : Wr.Dec<Sc.Ev>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.ev_x(r: Wr.Dec<Nat>) -> {FSc.get_ev.x(r) == ScreenRequirement.sc_sp_ev.x(r) : Wr.Dec<Sc.Ev>}:
  match r:
    case Wr.Got{x, s}:
      scx.ev_n(x, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.ev_tag(n: Nat, s: String) -> {FSc.get_ev.tag(n, s) == ScreenRequirement.sc_sp_ev.tag(n, s) : Wr.Dec<Sc.Ev>}:
  match n:
    case 0n:
      {==}
    case 1n:
      scx.ev_x(Wr.get_nat(s))
    case 2n:
      scx.ev_one(Wr.get_nat(s))
    case 3n:
      {==}
    case 4n:
      scx.ev_w(Wr.get_nat(s))
    case 5n+p:
      {==}

def scx.ev_of(r: Wr.Dec<Nat>) -> {FSc.get_ev.of(r) == ScreenRequirement.sc_sp_ev.of(r) : Wr.Dec<Sc.Ev>}:
  match r:
    case Wr.Got{n, s}:
      scx.ev_tag(n, s)
    case Wr.Bad{}:
      {==}

def scx.ev_r(s: String) -> {FSc.get_ev(s) == ScreenRequirement.sc_sp_ev(s) : Wr.Dec<Sc.Ev>}:
  scx.ev_of(Wr.get_nat(s))

def scx.blks_r_go(n: Nat, cur: Wr.Dec<Sc.Blk>) -> {Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, n, cur) == Wr.get_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, n, cur) : Wr.Dec<List<&2, Sc.Blk>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Sc.Blk>, FSc.get_blk(r), ScreenRequirement.sc_sp_blk(r), scx.blk_r(r)) : {Wr.get_list.cons(Sc.Blk, x, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, k, _)) == Wr.get_list.cons(Sc.Blk, x, Wr.get_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, k, ScreenRequirement.sc_sp_blk(r))) : Wr.Dec<List<&2, Sc.Blk>>}
      %Equal.sym(Wr.Dec<List<&2, Sc.Blk>>, Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, k, ScreenRequirement.sc_sp_blk(r)), Wr.get_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, k, ScreenRequirement.sc_sp_blk(r)), scx.blks_r_go(k, ScreenRequirement.sc_sp_blk(r))) : {Wr.get_list.cons(Sc.Blk, x, _) == Wr.get_list.cons(Sc.Blk, x, Wr.get_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, k, ScreenRequirement.sc_sp_blk(r))) : Wr.Dec<List<&2, Sc.Blk>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def scx.blks_r_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, d) == Wr.get_list.start(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, d) : Wr.Dec<List<&2, Sc.Blk>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Sc.Blk>, FSc.get_blk(s), ScreenRequirement.sc_sp_blk(s), scx.blk_r(s)) : {Wr.get_list.go(~Sc.Blk, ~FSc.get_blk, m, _) == Wr.get_list.go(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, m, ScreenRequirement.sc_sp_blk(s)) : Wr.Dec<List<&2, Sc.Blk>>}
          scx.blks_r_go(m, ScreenRequirement.sc_sp_blk(s))
    case Wr.Bad{}:
      {==}

def scx.evs_r_go(n: Nat, cur: Wr.Dec<Sc.Ev>) -> {Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, n, cur) == Wr.get_list.go(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, n, cur) : Wr.Dec<List<&2, Sc.Ev>>}:
  match n cur:
    case 0n Wr.Got{x, r}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+k Wr.Got{+x, +r}:
      %Equal.sym(Wr.Dec<Sc.Ev>, FSc.get_ev(r), ScreenRequirement.sc_sp_ev(r), scx.ev_r(r)) : {Wr.get_list.cons(Sc.Ev, x, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, k, _)) == Wr.get_list.cons(Sc.Ev, x, Wr.get_list.go(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, k, ScreenRequirement.sc_sp_ev(r))) : Wr.Dec<List<&2, Sc.Ev>>}
      %Equal.sym(Wr.Dec<List<&2, Sc.Ev>>, Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, k, ScreenRequirement.sc_sp_ev(r)), Wr.get_list.go(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, k, ScreenRequirement.sc_sp_ev(r)), scx.evs_r_go(k, ScreenRequirement.sc_sp_ev(r))) : {Wr.get_list.cons(Sc.Ev, x, _) == Wr.get_list.cons(Sc.Ev, x, Wr.get_list.go(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, k, ScreenRequirement.sc_sp_ev(r))) : Wr.Dec<List<&2, Sc.Ev>>}
      {==}
    case 1n+k Wr.Bad{}:
      {==}

def scx.evs_r_start(d: Wr.Dec<Nat>) -> {Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, d) == Wr.get_list.start(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, d) : Wr.Dec<List<&2, Sc.Ev>>}:
  match d:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Sc.Ev>, FSc.get_ev(s), ScreenRequirement.sc_sp_ev(s), scx.ev_r(s)) : {Wr.get_list.go(~Sc.Ev, ~FSc.get_ev, m, _) == Wr.get_list.go(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, m, ScreenRequirement.sc_sp_ev(s)) : Wr.Dec<List<&2, Sc.Ev>>}
          scx.evs_r_go(m, ScreenRequirement.sc_sp_ev(s))
    case Wr.Bad{}:
      {==}

def scx.run_es(t: Sc.Tx, r: Wr.Dec<List<&2, Sc.Ev>>) -> {FSc.get_run.es(t, r) == ScreenRequirement.sc_sp_run.es(t, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.run_w(+bs: List<&2, Sc.Blk>, +n: Nat, r: Wr.Dec<Nat>) -> {FSc.get_run(FSc.get_tx.w(bs, n, r)) == ScreenRequirement.sc_sp_run.w(bs, n, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{+w, +s}:
      %Equal.sym(Wr.Dec<List<&2, Sc.Ev>>, Wr.get_list.start(~Sc.Ev, ~FSc.get_ev, Wr.get_nat(s)), Wr.get_list.start(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, Wr.get_nat(s)), scx.evs_r_start(Wr.get_nat(s))) : {FSc.get_run.es(Sc.Tx{bs, n, w}, _) == ScreenRequirement.sc_sp_run.w(bs, n, Wr.Got{w, s}) : Wr.Dec<FSc.Req>}
      scx.run_es(Sc.Tx{bs, n, w}, Wr.get_list(~Sc.Ev, ~ScreenRequirement.sc_sp_ev, s))
    case Wr.Bad{}:
      {==}

def scx.run_n(+bs: List<&2, Sc.Blk>, r: Wr.Dec<Nat>) -> {FSc.get_run(FSc.get_tx.n(bs, r)) == ScreenRequirement.sc_sp_run.n(bs, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{n, s}:
      scx.run_w(bs, n, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.run_bs(r: Wr.Dec<List<&2, Sc.Blk>>) -> {FSc.get_run(FSc.get_tx.bs(r)) == ScreenRequirement.sc_sp_run.bs(r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{bs, s}:
      scx.run_n(bs, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.pace_n(min: Nat, k: Nat, rv: Nat, sh: Nat, r: Wr.Dec<Nat>) -> {FSc.get_pacereq.n(min, k, Sc.Pace{rv, sh}, r) == ScreenRequirement.sc_sp_pacereq.n(min, k, rv, sh, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.pace_sh(min: Nat, k: Nat, rv: Nat, r: Wr.Dec<Nat>) -> {FSc.get_pacereq.p(min, k, FSc.get_pace.s(rv, r)) == ScreenRequirement.sc_sp_pacereq.sh(min, k, rv, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{sh, s}:
      scx.pace_n(min, k, rv, sh, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.pace_rv(min: Nat, k: Nat, r: Wr.Dec<Nat>) -> {FSc.get_pacereq.p(min, k, FSc.get_pace.r(r)) == ScreenRequirement.sc_sp_pacereq.rv(min, k, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{rv, s}:
      scx.pace_sh(min, k, rv, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.pace_k(min: Nat, r: Wr.Dec<Nat>) -> {FSc.get_pacereq.k(min, r) == ScreenRequirement.sc_sp_pacereq.k(min, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{k, s}:
      scx.pace_rv(min, k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.pace(r: Wr.Dec<Nat>) -> {FSc.get_pacereq(r) == ScreenRequirement.sc_sp_pacereq(r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{min, s}:
      scx.pace_k(min, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.stack_rows(hs: List<&2, Nat>, y: Nat, r: Wr.Dec<Nat>) -> {FSc.get_stack.rows(hs, y, r) == ScreenRequirement.sc_sp_stack.rows(hs, y, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{rows, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.stack_y(hs: List<&2, Nat>, r: Wr.Dec<Nat>) -> {FSc.get_stack.y(hs, r) == ScreenRequirement.sc_sp_stack.y(hs, r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{y, s}:
      scx.stack_rows(hs, y, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.stack_hs(r: Wr.Dec<List<&2, Nat>>) -> {FSc.get_stack(r) == ScreenRequirement.sc_sp_stack.hs(r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{hs, s}:
      scx.stack_y(hs, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def scx.paint_r(r: Wr.Dec<List<&2, Bool>>) -> {FSc.get_paint(r) == ScreenRequirement.sc_sp_paintreq(r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{ks, s}:
      {==}
    case Wr.Bad{}:
      {==}

def scx.req_tag(n: Nat, +s: String) -> {FSc.get_req.tag(n, s) == ScreenRequirement.sc_sp_req.tag(n, s) : Wr.Dec<FSc.Req>}:
  match n:
    case 0n:
      %Equal.sym(Wr.Dec<List<&2, Sc.Blk>>, Wr.get_list.start(~Sc.Blk, ~FSc.get_blk, Wr.get_nat(s)), Wr.get_list.start(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, Wr.get_nat(s)), scx.blks_r_start(Wr.get_nat(s))) : {FSc.get_run(FSc.get_tx.bs(_)) == ScreenRequirement.sc_sp_req.tag(0n, s) : Wr.Dec<FSc.Req>}
      scx.run_bs(Wr.get_list(~Sc.Blk, ~ScreenRequirement.sc_sp_blk, s))
    case 1n:
      scx.pace(Wr.get_nat(s))
    case 2n:
      scx.stack_hs(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n:
      scx.paint_r(Wr.get_list(~Bool, ~Wr.get_bool, s))
    case 4n+p:
      {==}

def scx.req_of(r: Wr.Dec<Nat>) -> {FSc.get_req.of(r) == ScreenRequirement.sc_sp_req.of(r) : Wr.Dec<FSc.Req>}:
  match r:
    case Wr.Got{n, s}:
      scx.req_tag(n, s)
    case Wr.Bad{}:
      {==}

# The entry
# ---------

def scx.whole(+q: FSc.Req, b: Bool) -> {FSc.ffi.whole(q, b) == ScreenRequirement.sc_sp.whole(q, b) : String}:
  match b:
    case True{}:
      scx.answer(q)
    case False{}:
      {==}

def scx.of(r: Wr.Dec<FSc.Req>) -> {FSc.ffi.of(r) == ScreenRequirement.sc_sp.of(r) : String}:
  match r:
    case Wr.Got{q, s}:
      scx.whole(q, Wr.end(s))
    case Wr.Bad{}:
      {==}

def ScreenRequirement.screen_ffi_exact(s):
  %Equal.sym(Wr.Dec<FSc.Req>, FSc.get_req.of(Wr.get_nat(s)), ScreenRequirement.sc_sp_req.of(Wr.get_nat(s)), scx.req_of(Wr.get_nat(s))) : {FSc.ffi.of(_) == ScreenRequirement.sc_spec(s) : String}
  scx.of(ScreenRequirement.sc_sp_req(s))
