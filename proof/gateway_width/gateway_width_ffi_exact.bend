# eukhe: the proof of LAW gateway_width_ffi_exact
# The entry reads every input as the spec's reader does (the flat
# decoder agrees with the spec's front-to-back reading) and answers the
# spec's layout (the model's widths and pads on a measured table are the
# spec's).

import Base
import ../../bend/ffi_gateway_width.bend as FGw
import ../../bend/gateway_width.bend as Gw
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/gateway_width.bend as GatewayWidth
import ../base/list.bend as LList
import ../base/nat.bend as LNat
import ./base/pads.bend as LPads

# The reader
# ----------

# the lists the end of the input reads to, with the items cur before it
def gx.start(cur: List<&2, Nat>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  match cur:
    case Nil{}:
      Some{Nil{}}
    case c <> t:
      None{}

# what a suffix that decodes to m reads to, with the items cur before it
def gx.fin(cur: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  match m:
    case None{}:
      None{}
    case Some{st}:
      match st:
        case Fl.Start{}:
          gx.start(cur)
        case Fl.Mid{o, d}:
          Some{List.append(&2, Nat, cur, o) <> d}

def gx.start_app(cur: List<&2, Nat>, -x: Nat) -> {gx.start(List.append(&2, Nat, cur, [x])) == None{} : Maybe<&2, List<&2, List<&2, Nat>>>}:
  match cur:
    case Nil{}:
      {==}
    case c <> t:
      {==}

def gx.rows_zero(+cur: List<&2, Nat>, m: Maybe<&2, Fl.St>) -> {GatewayWidth.gw_sp_rows.cons(cur, gx.fin(Nil{}, m)) == gx.fin(cur, Fl.step(0n, m)) : Maybe<&2, List<&2, List<&2, Nat>>>}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      match st:
        case Fl.Start{}:
          %Equal.sym(List<&2, Nat>, List.append(&2, Nat, cur, Nil{}), cur, LList.pd.app_nil(Nat, cur)) : {Some{cur <> Nil{}} == Some{_ <> Nil{}} : Maybe<&2, List<&2, List<&2, Nat>>>}
          {==}
        case Fl.Mid{+o, +d}:
          %Equal.sym(List<&2, Nat>, List.append(&2, Nat, cur, Nil{}), cur, LList.pd.app_nil(Nat, cur)) : {Some{cur <> o <> d} == Some{_ <> o <> d} : Maybe<&2, List<&2, List<&2, Nat>>>}
          {==}

def gx.rows_item(+cur: List<&2, Nat>, +x: Nat, m: Maybe<&2, Fl.St>) -> {gx.fin(List.append(&2, Nat, cur, [x]), m) == gx.fin(cur, Fl.step(1n+x, m)) : Maybe<&2, List<&2, List<&2, Nat>>>}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      match st:
        case Fl.Start{}:
          gx.start_app(cur, x)
        case Fl.Mid{+o, +d}:
          %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.append(&2, Nat, cur, [x]), o), List.append(&2, Nat, cur, x <> o), LList.pd.app_assoc(Nat, cur, [x], o)) : {Some{_ <> d} == Some{List.append(&2, Nat, cur, x <> o) <> d} : Maybe<&2, List<&2, List<&2, Nat>>>}
          {==}

def gx.rows(ns: List<&2, Nat>, +cur: List<&2, Nat>) -> {GatewayWidth.gw_sp_rows(ns, cur) == gx.fin(cur, Fl.fold(ns)) : Maybe<&2, List<&2, List<&2, Nat>>>}:
  match ns:
    case Nil{}:
      match cur:
        case Nil{}:
          {==}
        case c <> t:
          {==}
    case n <> +rest:
      match n:
        case 0n:
          %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, GatewayWidth.gw_sp_rows(rest, Nil{}), gx.fin(Nil{}, Fl.fold(rest)), gx.rows(rest, Nil{})) : {GatewayWidth.gw_sp_rows.cons(cur, _) == gx.fin(cur, Fl.step(0n, Fl.fold(rest))) : Maybe<&2, List<&2, List<&2, Nat>>>}
          gx.rows_zero(cur, Fl.fold(rest))
        case 1n++x:
          %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, GatewayWidth.gw_sp_rows(rest, List.append(&2, Nat, cur, [x])), gx.fin(List.append(&2, Nat, cur, [x]), Fl.fold(rest)), gx.rows(rest, List.append(&2, Nat, cur, [x]))) : {_ == gx.fin(cur, Fl.step(1n+x, Fl.fold(rest))) : Maybe<&2, List<&2, List<&2, Nat>>>}
          gx.rows_item(cur, x, Fl.fold(rest))

def gx.unflat_fin(m: Maybe<&2, Fl.St>) -> {gx.fin(Nil{}, m) == Fl.unflat.fin(m) : Maybe<&2, List<&2, List<&2, Nat>>>}:
  match m:
    case None{}:
      {==}
    case Some{st}:
      match st:
        case Fl.Start{}:
          {==}
        case Fl.Mid{o, d}:
          {==}

def gx.unflat(+ns: List<&2, Nat>) -> {GatewayWidth.gw_sp_rows(ns, Nil{}) == Fl.unflat(ns) : Maybe<&2, List<&2, List<&2, Nat>>>}:
  Equal.trans(Maybe<&2, List<&2, List<&2, Nat>>>, GatewayWidth.gw_sp_rows(ns, Nil{}), gx.fin(Nil{}, Fl.fold(ns)), Fl.unflat(ns), gx.rows(ns, Nil{}), gx.unflat_fin(Fl.fold(ns)))

def gx.read_of(m: Maybe<&2, List<&2, List<&2, Nat>>>, s: String) -> {FGw.get_req.of(m, s) == GatewayWidth.gw_sp_read.of(m, s) : Wr.Dec<List<&2, List<&2, Nat>>>}:
  match m:
    case Some{rows}:
      {==}
    case None{}:
      {==}

def gx.read_ns(r: Wr.Dec<List<&2, Nat>>) -> {FGw.get_req.ns(r) == GatewayWidth.gw_sp_read.ns(r) : Wr.Dec<List<&2, List<&2, Nat>>>}:
  match r:
    case Wr.Got{+ns, +s}:
      %gx.unflat(ns) : {FGw.get_req.of(_, s) == GatewayWidth.gw_sp_read.of(GatewayWidth.gw_sp_rows(ns, Nil{}), s) : Wr.Dec<List<&2, List<&2, Nat>>>}
      gx.read_of(GatewayWidth.gw_sp_rows(ns, Nil{}), s)
    case Wr.Bad{}:
      {==}

# The layout
# ----------

def gx.cell(r: List<&2, Nat>, +i: Nat) -> {Gw.get.w(FGw.cells(r), Gw.Display{}, i) == GatewayWidth.gw_sp_cell(r, i) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> rest:
      match i:
        case 0n:
          LNat.add_zero(w)
        case 1n+p:
          gx.cell(rest, p)

def gx.colw(rows: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.col.w(FGw.table(rows), Gw.Display{}, i) == GatewayWidth.gw_sp_colw(rows, i) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %Equal.sym(Nat, Gw.get.w(FGw.cells(r), Gw.Display{}, i), GatewayWidth.gw_sp_cell(r, i), gx.cell(r, i)) : {Nat.max(_, Gw.col.w(FGw.table(rest), Gw.Display{}, i)) == GatewayWidth.gw_sp_colw(r <> rest, i) : Nat}
      %Equal.sym(Nat, Gw.col.w(FGw.table(rest), Gw.Display{}, i), GatewayWidth.gw_sp_colw(rest, i), gx.colw(rest, i)) : {Nat.max(GatewayWidth.gw_sp_cell(r, i), _) == GatewayWidth.gw_sp_colw(r <> rest, i) : Nat}
      {==}

def gx.len(r: List<&2, Nat>) -> {List.length(&2, List<&2, Nat>, FGw.cells(r)) == List.length(&2, Nat, r) : Nat}:
  match r:
    case Nil{}:
      {==}
    case w <> +rest:
      %Equal.sym(Nat, List.length(&2, List<&2, Nat>, FGw.cells(rest)), List.length(&2, Nat, rest), gx.len(rest)) : {1n+_ == 1n+List.length(&2, Nat, rest) : Nat}
      {==}

def gx.cols(rows: List<&2, List<&2, Nat>>) -> {Gw.cols(FGw.table(rows)) == GatewayWidth.gw_sp_cols(rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case +r <> +rest:
      %Equal.sym(Nat, List.length(&2, List<&2, Nat>, FGw.cells(r)), List.length(&2, Nat, r), gx.len(r)) : {Nat.max(_, Gw.cols(FGw.table(rest))) == GatewayWidth.gw_sp_cols(r <> rest) : Nat}
      %Equal.sym(Nat, Gw.cols(FGw.table(rest)), GatewayWidth.gw_sp_cols(rest), gx.cols(rest)) : {Nat.max(List.length(&2, Nat, r), _) == GatewayWidth.gw_sp_cols(r <> rest) : Nat}
      {==}

def gx.widths(k: Nat, +rows: List<&2, List<&2, Nat>>, +i: Nat) -> {Gw.widths(k, Gw.Display{}, FGw.table(rows), i) == GatewayWidth.gw_sp_widths(k, rows, i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Gw.col.w(FGw.table(rows), Gw.Display{}, i), GatewayWidth.gw_sp_colw(rows, i), gx.colw(rows, i)) : {_ <> Gw.widths(p, Gw.Display{}, FGw.table(rows), 1n+i) == GatewayWidth.gw_sp_widths(1n+p, rows, i) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Gw.widths(p, Gw.Display{}, FGw.table(rows), 1n+i), GatewayWidth.gw_sp_widths(p, rows, 1n+i), gx.widths(p, rows, 1n+i)) : {GatewayWidth.gw_sp_colw(rows, i) <> _ == GatewayWidth.gw_sp_widths(1n+p, rows, i) : List<&2, Nat>}
      {==}

def gx.pads(k: Nat, +rows: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +i: Nat) -> {LPads.gwp.pads(k, FGw.table(rows), FGw.cells(r), i) == GatewayWidth.gw_sp_pads(k, rows, r, i) : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Gw.col.w(FGw.table(rows), Gw.Display{}, i), GatewayWidth.gw_sp_colw(rows, i), gx.colw(rows, i)) : {Nat.sub(_, Gw.get.w(FGw.cells(r), Gw.Display{}, i)) <> LPads.gwp.pads(p, FGw.table(rows), FGw.cells(r), 1n+i) == GatewayWidth.gw_sp_pads(1n+p, rows, r, i) : List<&2, Nat>}
      %Equal.sym(Nat, Gw.get.w(FGw.cells(r), Gw.Display{}, i), GatewayWidth.gw_sp_cell(r, i), gx.cell(r, i)) : {Nat.sub(GatewayWidth.gw_sp_colw(rows, i), _) <> LPads.gwp.pads(p, FGw.table(rows), FGw.cells(r), 1n+i) == GatewayWidth.gw_sp_pads(1n+p, rows, r, i) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, LPads.gwp.pads(p, FGw.table(rows), FGw.cells(r), 1n+i), GatewayWidth.gw_sp_pads(p, rows, r, 1n+i), gx.pads(p, rows, r, 1n+i)) : {Nat.sub(GatewayWidth.gw_sp_colw(rows, i), GatewayWidth.gw_sp_cell(r, i)) <> _ == GatewayWidth.gw_sp_pads(1n+p, rows, r, i) : List<&2, Nat>}
      {==}

def gx.pads_all(rs: List<&2, List<&2, Nat>>, +k: Nat, +rows: List<&2, List<&2, Nat>>) -> {LPads.gwp.pads_all(FGw.table(rs), k, FGw.table(rows)) == GatewayWidth.gw_sp_pads_all(rs, k, rows) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %Equal.sym(List<&2, Nat>, LPads.gwp.pads(k, FGw.table(rows), FGw.cells(r), 0n), GatewayWidth.gw_sp_pads(k, rows, r, 0n), gx.pads(k, rows, r, 0n)) : {_ <> LPads.gwp.pads_all(FGw.table(rest), k, FGw.table(rows)) == GatewayWidth.gw_sp_pads_all(r <> rest, k, rows) : List<&2, List<&2, Nat>>}
      %Equal.sym(List<&2, List<&2, Nat>>, LPads.gwp.pads_all(FGw.table(rest), k, FGw.table(rows)), GatewayWidth.gw_sp_pads_all(rest, k, rows), gx.pads_all(rest, k, rows)) : {GatewayWidth.gw_sp_pads(k, rows, r, 0n) <> _ == GatewayWidth.gw_sp_pads_all(r <> rest, k, rows) : List<&2, List<&2, Nat>>}
      {==}

def gx.one(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == List.append(&2, Nat, GatewayWidth.gw_sp_marked(xs), rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(List<&2, Nat>, Fl.one(t, rest), List.append(&2, Nat, GatewayWidth.gw_sp_marked(t), rest), gx.one(t, rest)) : {{1n+x : Nat} <> _ == List.append(&2, Nat, GatewayWidth.gw_sp_marked(x <> t), rest) : List<&2, Nat>}
      {==}

def gx.flat(xss: List<&2, List<&2, Nat>>) -> {Fl.flat(xss) == GatewayWidth.gw_sp_flat(xss) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      %Equal.sym(List<&2, Nat>, Fl.one(xs, Fl.flat(rest)), List.append(&2, Nat, GatewayWidth.gw_sp_marked(xs), Fl.flat(rest)), gx.one(xs, Fl.flat(rest))) : {_ == GatewayWidth.gw_sp_flat(xs <> rest) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, Fl.flat(rest), GatewayWidth.gw_sp_flat(rest), gx.flat(rest)) : {List.append(&2, Nat, GatewayWidth.gw_sp_marked(xs), _) == GatewayWidth.gw_sp_flat(xs <> rest) : List<&2, Nat>}
      {==}

def gx.reply(+rows: List<&2, List<&2, Nat>>) -> {FGw.put_lay(Gw.layout(FGw.table(rows)), "") == GatewayWidth.gw_sp_reply(rows) : String}:
  %Equal.sym(List<&2, List<&2, Nat>>, Gw.pads.all(FGw.table(rows), Gw.widths(Gw.cols(FGw.table(rows)), Gw.Display{}, FGw.table(rows), 0n)), LPads.gwp.pads_all(FGw.table(rows), Nat.sub(Gw.cols(FGw.table(rows)), 1n), FGw.table(rows)), LPads.gwp.all(FGw.table(rows), Gw.cols(FGw.table(rows)), FGw.table(rows))) : {FGw.put_ns(Gw.widths(Gw.cols(FGw.table(rows)), Gw.Display{}, FGw.table(rows), 0n), FGw.put_ns(Fl.flat(_), "")) == GatewayWidth.gw_sp_reply(rows) : String}
  %Equal.sym(List<&2, Nat>, Fl.flat(LPads.gwp.pads_all(FGw.table(rows), Nat.sub(Gw.cols(FGw.table(rows)), 1n), FGw.table(rows))), GatewayWidth.gw_sp_flat(LPads.gwp.pads_all(FGw.table(rows), Nat.sub(Gw.cols(FGw.table(rows)), 1n), FGw.table(rows))), gx.flat(LPads.gwp.pads_all(FGw.table(rows), Nat.sub(Gw.cols(FGw.table(rows)), 1n), FGw.table(rows)))) : {FGw.put_ns(Gw.widths(Gw.cols(FGw.table(rows)), Gw.Display{}, FGw.table(rows), 0n), FGw.put_ns(_, "")) == GatewayWidth.gw_sp_reply(rows) : String}
  %Equal.sym(List<&2, List<&2, Nat>>, LPads.gwp.pads_all(FGw.table(rows), Nat.sub(Gw.cols(FGw.table(rows)), 1n), FGw.table(rows)), GatewayWidth.gw_sp_pads_all(rows, Nat.sub(Gw.cols(FGw.table(rows)), 1n), rows), gx.pads_all(rows, Nat.sub(Gw.cols(FGw.table(rows)), 1n), rows)) : {FGw.put_ns(Gw.widths(Gw.cols(FGw.table(rows)), Gw.Display{}, FGw.table(rows), 0n), FGw.put_ns(GatewayWidth.gw_sp_flat(_), "")) == GatewayWidth.gw_sp_reply(rows) : String}
  %Equal.sym(Nat, Gw.cols(FGw.table(rows)), GatewayWidth.gw_sp_cols(rows), gx.cols(rows)) : {FGw.put_ns(Gw.widths(_, Gw.Display{}, FGw.table(rows), 0n), FGw.put_ns(GatewayWidth.gw_sp_flat(GatewayWidth.gw_sp_pads_all(rows, Nat.sub(_, 1n), rows)), "")) == GatewayWidth.gw_sp_reply(rows) : String}
  %Equal.sym(List<&2, Nat>, Gw.widths(GatewayWidth.gw_sp_cols(rows), Gw.Display{}, FGw.table(rows), 0n), GatewayWidth.gw_sp_widths(GatewayWidth.gw_sp_cols(rows), rows, 0n), gx.widths(GatewayWidth.gw_sp_cols(rows), rows, 0n)) : {FGw.put_ns(_, FGw.put_ns(GatewayWidth.gw_sp_flat(GatewayWidth.gw_sp_pads_all(rows, Nat.sub(GatewayWidth.gw_sp_cols(rows), 1n), rows)), "")) == GatewayWidth.gw_sp_reply(rows) : String}
  {==}

# The entry
# ---------

def gx.end(b: Bool, +rows: List<&2, List<&2, Nat>>) -> {FGw.reply(b, rows) == GatewayWidth.gw_sp.end(b, rows) : String}:
  match b:
    case True{}:
      gx.reply(rows)
    case False{}:
      {==}

def gx.run(r: Wr.Dec<List<&2, List<&2, Nat>>>) -> {FGw.answer(r) == GatewayWidth.gw_sp.run(r) : String}:
  match r:
    case Wr.Got{rows, s}:
      gx.end(Wr.end(s), rows)
    case Wr.Bad{}:
      {==}

def GatewayWidth.gateway_width_ffi_exact(s):
  %Equal.sym(Wr.Dec<List<&2, List<&2, Nat>>>, FGw.get_req.ns(Wr.get_list(~Nat, ~Wr.get_nat, s)), GatewayWidth.gw_sp_read.ns(Wr.get_list(~Nat, ~Wr.get_nat, s)), gx.read_ns(Wr.get_list(~Nat, ~Wr.get_nat, s))) : {FGw.answer(_) == GatewayWidth.gw_spec(s) : String}
  gx.run(GatewayWidth.gw_sp_read(s))
