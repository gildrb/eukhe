# eukhe: lemmas the entry proofs of area command share: the entry's own
# encoders write what the spec spellers of laws/command/entry.bend spell
# (ce_req, ce_table, ...), and the entry's answer to a request is the
# spelled reply of the model (ce_run).

import Base
import ../../../bend/command.bend as Cmd
import ../../../bend/ffi_command.bend as FCmd
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/command/entry.bend as Command
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../command_ffi_round_trip.bend as PCommandFfiRoundTrip

# ---- the encoders spell the spec ----

# a list of strings
def ce_strs(+xs: List<&2, String>, +rest: String) -> {FCmd.put_strs(xs, rest) == LawsBase.wire_spell_strs(xs, rest) : String}:
  Wire.wire_strs_spells(xs, rest)

# an entry: its path, its aliases, three Bools
def ce_ent(e: FCmd.EntW, +rest: String) -> {FCmd.put_ent(e, rest) == Command.cmd_spell_ent(e, rest) : String}:
  match e:
    case FCmd.EntW{+p, +a, +r, +f, +g}:
      +b = Wr.put_bool(r, Wr.put_bool(f, Wr.put_bool(g, rest)))
      Equal.trans(String, FCmd.put_strs(p, FCmd.put_strs(a, b)), FCmd.put_strs(p, LawsBase.wire_spell_strs(a, b)), LawsBase.wire_spell_strs(p, LawsBase.wire_spell_strs(a, b)),
        Equal.cong(String, String, z => FCmd.put_strs(p, z), FCmd.put_strs(a, b), LawsBase.wire_spell_strs(a, b), ce_strs(a, b)),
        ce_strs(p, LawsBase.wire_spell_strs(a, b)))

# the entries of a table, then rest
def ce_ents(t: List<&2, FCmd.EntW>, +rest: String) -> {PCommandFfiRoundTrip.cfr_es_items(t, rest) == Command.cmd_spell_ents(t, rest) : String}:
  match t:
    case Nil{}:
      {==}
    case Con{+e, +more}:
      Equal.trans(String, FCmd.put_ent(e, PCommandFfiRoundTrip.cfr_es_items(more, rest)), FCmd.put_ent(e, Command.cmd_spell_ents(more, rest)), Command.cmd_spell_ent(e, Command.cmd_spell_ents(more, rest)),
        Equal.cong(String, String, z => FCmd.put_ent(e, z), PCommandFfiRoundTrip.cfr_es_items(more, rest), Command.cmd_spell_ents(more, rest), ce_ents(more, rest)),
        ce_ent(e, Command.cmd_spell_ents(more, rest)))

# a table: its count, then its entries
def ce_table(+t: List<&2, FCmd.EntW>, +rest: String) -> {FCmd.put_table(t, rest) == Command.cmd_spell_table(t, rest) : String}:
  Equal.trans(String, FCmd.put_table(t, rest), Wr.put_nat(List.length(&2, FCmd.EntW, t), PCommandFfiRoundTrip.cfr_es_items(t, rest)), Wr.put_nat(List.length(&2, FCmd.EntW, t), Command.cmd_spell_ents(t, rest)),
    PCommandFfiRoundTrip.cfr_es_put(t, rest),
    Equal.cong(String, String, z => Wr.put_nat(List.length(&2, FCmd.EntW, t), z), PCommandFfiRoundTrip.cfr_es_items(t, rest), Command.cmd_spell_ents(t, rest), ce_ents(t, rest)))

# a row
def ce_sel(x: Cmd.Sel, -rest: String) -> {FCmd.put_sel(x, rest) == Command.cmd_spell_sel(x, rest) : String}:
  match x:
    case Cmd.NoRow{}:
      {==}
    case Cmd.Row{i}:
      {==}

# a row, then a key
def ce_sel_press(x: Cmd.Sel, k: Cmd.Press, -rest: String) -> {FCmd.put_sel(x, FCmd.put_press(k, rest)) == Command.cmd_spell_sel(x, Command.cmd_spell_press(k, rest)) : String}:
  match x k:
    case Cmd.NoRow{} Cmd.Tab{}:
      {==}
    case Cmd.NoRow{} Cmd.Enter{}:
      {==}
    case Cmd.Row{i} Cmd.Tab{}:
      {==}
    case Cmd.Row{i} Cmd.Enter{}:
      {==}

# a question
def ce_query(q: FCmd.Query, -rest: String) -> {FCmd.put_query(q, rest) == Command.cmd_spell_query(q, rest) : String}:
  match q:
    case FCmd.QResolve{l}:
      {==}
    case FCmd.QMenu{l}:
      {==}
    case FCmd.QKey{+l, +x, +k}:
      Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(l, z)), FCmd.put_sel(x, FCmd.put_press(k, rest)), Command.cmd_spell_sel(x, Command.cmd_spell_press(k, rest)), ce_sel_press(x, k, rest))

# a request: its table, then its question
def ce_req(r: FCmd.Req, +rest: String) -> {FCmd.put_req(r, rest) == Command.cmd_spell_req(r, rest) : String}:
  match r:
    case FCmd.Req{+t, +q}:
      Equal.trans(String, FCmd.put_table(t, FCmd.put_query(q, rest)), FCmd.put_table(t, Command.cmd_spell_query(q, rest)), Command.cmd_spell_table(t, Command.cmd_spell_query(q, rest)),
        Equal.cong(String, String, z => FCmd.put_table(t, z), FCmd.put_query(q, rest), Command.cmd_spell_query(q, rest), ce_query(q, rest)),
        ce_table(t, Command.cmd_spell_query(q, rest)))

# ---- the model's answer, spelled ----

def ce_codes(s: String) -> {FCmd.codes(s) == Command.cmd_codes(s) : List<&2, Nat>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => U32.to_nat(Char.to_u32(c)) <> z, FCmd.codes(r), Command.cmd_codes(r), ce_codes(r))

def ce_text(ns: List<&2, Nat>) -> {FCmd.text(ns) == Command.cmd_text(ns) : String}:
  match ns:
    case Nil{}:
      {==}
    case Con{n, +r}:
      Equal.cong(String, String, z => SCon{Chr{U32.from_nat(n)}, z}, FCmd.text(r), Command.cmd_text(r), ce_text(r))

def ce_texts(ps: List<&2, List<&2, Nat>>) -> {FCmd.texts(ps) == Command.cmd_texts(ps) : List<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(String, FCmd.text(x), Command.cmd_text(x), ce_text(x)) : {_ <> FCmd.texts(r) == Command.cmd_texts(x <> r) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => Command.cmd_text(x) <> z, FCmd.texts(r), Command.cmd_texts(r), ce_texts(r))

def ce_names(xs: List<&2, String>) -> {FCmd.names(xs) == Command.cmd_name_codes(xs) : List<&2, List<&2, Nat>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(List<&2, Nat>, FCmd.codes(x), Command.cmd_codes(x), ce_codes(x)) : {_ <> FCmd.names(r) == Command.cmd_name_codes(x <> r) : List<&2, List<&2, Nat>>}
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => Command.cmd_codes(x) <> z, FCmd.names(r), Command.cmd_name_codes(r), ce_names(r))

# the entry reads a table as the spec's model table
def ce_model_table(t: List<&2, FCmd.EntW>) -> {FCmd.ents(t) == Command.cmd_model_table(t) : List<&2, Cmd.Ent>}:
  match t:
    case Nil{}:
      {==}
    case Con{e, +rest}:
      match e:
        case FCmd.EntW{+p, +a, +r, +f, +g}:
          %Equal.sym(List<&2, List<&2, Nat>>, FCmd.names(p), Command.cmd_name_codes(p), ce_names(p)) : {Cmd.Ent{_, FCmd.names(a), r, f, g} <> FCmd.ents(rest) == Command.cmd_model_table(FCmd.EntW{p, a, r, f, g} <> rest) : List<&2, Cmd.Ent>}
          %Equal.sym(List<&2, List<&2, Nat>>, FCmd.names(a), Command.cmd_name_codes(a), ce_names(a)) : {Cmd.Ent{Command.cmd_name_codes(p), _, r, f, g} <> FCmd.ents(rest) == Command.cmd_model_table(FCmd.EntW{p, a, r, f, g} <> rest) : List<&2, Cmd.Ent>}
          Equal.cong(List<&2, Cmd.Ent>, List<&2, Cmd.Ent>, z => Cmd.Ent{Command.cmd_name_codes(p), Command.cmd_name_codes(a), r, f, g} <> z, FCmd.ents(rest), Command.cmd_model_table(rest), ce_model_table(rest))

def ce_res(x: Cmd.Res) -> {FCmd.put_res(FCmd.res_w(x), "") == Command.cmd_spell_res(x) : String}:
  match x:
    case Cmd.Runs{+p, +a}:
      %Equal.sym(List<&2, String>, FCmd.texts(p), Command.cmd_texts(p), ce_texts(p)) : {Wr.put_nat(0n, FCmd.put_strs(_, Wr.put_str(FCmd.text(a), ""))) == Command.cmd_spell_res(Cmd.Runs{p, a}) : String}
      %Equal.sym(String, FCmd.text(a), Command.cmd_text(a), ce_text(a)) : {Wr.put_nat(0n, FCmd.put_strs(Command.cmd_texts(p), Wr.put_str(_, ""))) == Command.cmd_spell_res(Cmd.Runs{p, a}) : String}
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FCmd.put_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(a), "")), LawsBase.wire_spell_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(a), "")), ce_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(a), "")))
    case Cmd.Opens{+p}:
      %Equal.sym(List<&2, String>, FCmd.texts(p), Command.cmd_texts(p), ce_texts(p)) : {Wr.put_nat(1n, FCmd.put_strs(_, "")) == Command.cmd_spell_res(Cmd.Opens{p}) : String}
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCmd.put_strs(Command.cmd_texts(p), ""), LawsBase.wire_spell_strs(Command.cmd_texts(p), ""), ce_strs(Command.cmd_texts(p), ""))
    case Cmd.Unknown{+p, +w}:
      %Equal.sym(List<&2, String>, FCmd.texts(p), Command.cmd_texts(p), ce_texts(p)) : {Wr.put_nat(2n, FCmd.put_strs(_, Wr.put_str(FCmd.text(w), ""))) == Command.cmd_spell_res(Cmd.Unknown{p, w}) : String}
      %Equal.sym(String, FCmd.text(w), Command.cmd_text(w), ce_text(w)) : {Wr.put_nat(2n, FCmd.put_strs(Command.cmd_texts(p), Wr.put_str(_, ""))) == Command.cmd_spell_res(Cmd.Unknown{p, w}) : String}
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FCmd.put_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(w), "")), LawsBase.wire_spell_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(w), "")), ce_strs(Command.cmd_texts(p), Wr.put_str(Command.cmd_text(w), "")))
    case Cmd.NoCmd{}:
      {==}

def ce_menu(m: Cmd.Menu) -> {FCmd.put_menu(FCmd.menu_w(m), "") == Command.cmd_spell_menu(m) : String}:
  match m:
    case Cmd.Names{}:
      {==}
    case Cmd.Kids{+p, +xs}:
      %Equal.sym(List<&2, String>, FCmd.texts(p), Command.cmd_texts(p), ce_texts(p)) : {Wr.put_nat(1n, FCmd.put_strs(_, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))) == Command.cmd_spell_menu(Cmd.Kids{p, xs}) : String}
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""), LawsBase.wire_spell_nats(xs, ""), Wire.wire_nats_spells(xs, "")) : {Wr.put_nat(1n, FCmd.put_strs(Command.cmd_texts(p), _)) == Command.cmd_spell_menu(Cmd.Kids{p, xs}) : String}
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FCmd.put_strs(Command.cmd_texts(p), LawsBase.wire_spell_nats(xs, "")), LawsBase.wire_spell_strs(Command.cmd_texts(p), LawsBase.wire_spell_nats(xs, "")), ce_strs(Command.cmd_texts(p), LawsBase.wire_spell_nats(xs, "")))
    case Cmd.Shut{}:
      {==}

def ce_out(o: Cmd.Out) -> {FCmd.put_out(FCmd.out_w(o), "") == Command.cmd_spell_out(o) : String}:
  match o:
    case Cmd.Out{+l, +a, +b}:
      %Equal.sym(String, FCmd.text(l), Command.cmd_text(l), ce_text(l)) : {Wr.put_str(_, Wr.put_bool(a, Wr.put_bool(b, ""))) == Command.cmd_spell_out(Cmd.Out{l, a, b}) : String}
      {==}

# the answer to a question about the model table t
def ce_answer(+t: List<&2, Cmd.Ent>, q: FCmd.Query) -> {FCmd.answer(t, q) == Command.cmd_spell_answer(t, q) : String}:
  match q:
    case FCmd.QResolve{+l}:
      %Equal.sym(List<&2, Nat>, FCmd.codes(l), Command.cmd_codes(l), ce_codes(l)) : {FCmd.put_res(FCmd.res_w(Cmd.resolve(t, _)), "") == Command.cmd_spell_answer(t, FCmd.QResolve{l}) : String}
      ce_res(Cmd.resolve(t, Command.cmd_codes(l)))
    case FCmd.QMenu{+l}:
      %Equal.sym(List<&2, Nat>, FCmd.codes(l), Command.cmd_codes(l), ce_codes(l)) : {FCmd.put_menu(FCmd.menu_w(Cmd.menu(t, _)), "") == Command.cmd_spell_answer(t, FCmd.QMenu{l}) : String}
      ce_menu(Cmd.menu(t, Command.cmd_codes(l)))
    case FCmd.QKey{+l, +x, +k}:
      %Equal.sym(List<&2, Nat>, FCmd.codes(l), Command.cmd_codes(l), ce_codes(l)) : {FCmd.put_out(FCmd.out_w(Cmd.key(t, _, x, k)), "") == Command.cmd_spell_answer(t, FCmd.QKey{l, x, k}) : String}
      ce_out(Cmd.key(t, Command.cmd_codes(l), x, k))

# the entry's answer to a request is the spelled reply of the model
def ce_run(r: FCmd.Req) -> {FCmd.ffi.run(r) == Command.cmd_spell_reply(r) : String}:
  match r:
    case FCmd.Req{+t, +q}:
      %Equal.sym(List<&2, Cmd.Ent>, FCmd.ents(t), Command.cmd_model_table(t), ce_model_table(t)) : {FCmd.answer(_, q) == Command.cmd_spell_reply(FCmd.Req{t, q}) : String}
      ce_answer(Command.cmd_model_table(t), q)
