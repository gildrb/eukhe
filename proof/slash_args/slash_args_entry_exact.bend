# eukhe: the proof of LAW slash_args_entry_exact
#
# PROOF: the tag decoded is spelled (wire_nat_exact), so is the text with its length within the wire (dcw.str); a value is answered only for tags 0-3 with nothing left (sax.top).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/ffi_slash_args.bend as FSa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/slash_args/model.bend as SlashArgs
import ../../laws/slash_args/entry.bend as SlashArgsEntry
import ./base/entry.bend as LE

def SlashArgsEntry.slash_args_entry_exact(s, ok):
  LE.sax.top(s, Wr.get_nat(s), {==}, ok)
