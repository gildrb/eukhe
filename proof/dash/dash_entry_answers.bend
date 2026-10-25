# eukhe: the proof of LAW dash_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (dash_entry_reads), so the entry answers the code's choice; each choice
# is the spec's (dash_token_spec, dash_stored_spec, dash_keep_spec) and
# each reply encoder is the spec's spelling (da.*: case by case).

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/dash.bend as Dash
import ./dash_token_spec.bend as PDashTokenSpec
import ./dash_stored_spec.bend as PDashStoredSpec
import ./dash_keep_spec.bend as PDashKeepSpec
import ./dash_entry_reads.bend as PDashEntryReads

def da.shown(x: Da.Shown) -> {FDa.put_shown(x) == Dash.sp_w_token(x) : String}:
  match x:
    case Da.Hex{bs}:
      {==}
    case Da.Blank{}:
      {==}
    case Da.Junk{}:
      {==}

def da.stored(m: Maybe<&2, List<&2, Nat>>) -> {FDa.put_stored(m) == Dash.sp_w_stored(m) : String}:
  match m:
    case Some{bs}:
      {==}
    case None{}:
      {==}

def da.keep(k: Da.Keep) -> {FDa.keep.tag(k) == Dash.sp_w_keep(k) : Nat}:
  match k:
    case Da.Mint{}:
      {==}
    case Da.Reuse{}:
      {==}
    case Da.Restrict{}:
      {==}
    case Da.Unreadable{}:
      {==}
    case Da.Tokenless{}:
      {==}

def da.reply(q: FDa.Req) -> {FDa.answer(q) == Dash.sp_w_reply(q) : String}:
  match q:
    case FDa.QToken{+t}:
      %Equal.sym(Da.Shown, Da.shown(t), Dash.sp_shown(t), Dash.dash_token_spec(t)) : {FDa.put_shown(_) == Dash.sp_w_token(Dash.sp_shown(t)) : String}
      da.shown(Dash.sp_shown(t))
    case FDa.QStored{+f}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)) : {FDa.put_stored(_) == Dash.sp_w_stored(Dash.sp_stored(f)) : String}
      da.stored(Dash.sp_stored(f))
    case FDa.QKeep{+o, +f, +m}:
      %Equal.sym(Da.Keep, Da.keep(o, f, m), Dash.sp_keep(o, f, m), Dash.dash_keep_spec(o, f, m)) : {Wr.put_nat(FDa.keep.tag(_), "") == Wr.put_nat(Dash.sp_w_keep(Dash.sp_keep(o, f, m)), "") : String}
      %da.keep(Dash.sp_keep(o, f, m)) : {Wr.put_nat(FDa.keep.tag(Dash.sp_keep(o, f, m)), "") == Wr.put_nat(_, "") : String}
      {==}

def Dash.dash_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FDa.Req>, FDa.get_req(Dash.sp_w_req(q, "")), Wr.Got{q, ""}, Dash.dash_entry_reads(q, "", h)) : {FDa.ffi.got(_) == Dash.sp_w_reply(q) : String}
  da.reply(q)
