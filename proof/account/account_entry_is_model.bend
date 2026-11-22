# eukhe: the proof of LAW account_entry_is_model
#
# PROOF: a list of Nats that fits reads back whole (Wire.wire_list_round_trip)
# with nothing left; its Nats parse back to the request
# (account_entry_parses); the reply is the spec's spelling (LA.acb.reply).

import Base
import ../../bend/account.bend as Ac
import ../../bend/ffi_account.bend as FAc
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/account.bend as Account
import ../base/wire.bend as LWire
import ./account_entry_parses.bend as PAccountEntryParses
import ./base.bend as LA

def Account.account_entry_is_model(x, h):
  %Equal.sym(Wr.Dec<List<&2, Nat>>, FAc.get_req(Account.ac_req(x, "")), Wr.Got{Account.ac_nats(x), ""}, Wire.wire_list_round_trip(Account.ac_nats(x), "", h)) : {FAc.ffi.got(_) == Account.ac_reply(Ac.choose(x)) : String}
  %Equal.sym(Maybe<&2, Ac.In>, FAc.parse(Account.ac_nats(x)), Some{x}, Account.account_entry_parses(x)) : {FAc.ffi.parsed(_) == Account.ac_reply(Ac.choose(x)) : String}
  LA.acb.reply(Ac.choose(x))
