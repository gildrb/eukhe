# eukhe: the laws of area theme_entry: the theme entry
# (bend/ffi_theme.bend) as a whole, for every input string. The entry's
# other laws are in laws/theme.bend (section "The compiled entry"); this
# file pins what they leave free: an input the spec reader reads whole
# that the speller never writes, or a request that does not fit the wire.

import Base
import ../bend/ffi_theme.bend as FTh
import ../spec/theme/read.bend as Tr
import ../spec/theme/wire.bend as Tw

# the answer to the input s: the error form unless s is exactly one
# request (Tr.read, from the wire primitives), else the rules' decision
# spelled as Tw.answer spells it. Every model function Tw.answer reads is
# pinned for all its inputs: TPalette.parse by theme_parse_rejected and
# theme_parse_painted (TReader.read by the theme_read_* laws), TChoice.pick
# by theme_pick_res, theme_pick_cause, theme_pick_quiet, theme_pick_broken
# and theme_pick_clashes, TBundled.table by theme_tables_spec.
def th_entry.of(m: Maybe<&2, FTh.Req>) -> String:
  match m:
    case None{}:
      Tr.refused()
    case Some{r}:
      Tw.answer(r)

def th_entry(s: String) -> String:
  th_entry.of(Tr.read(s))

# LAW theme_ffi_total (R6): every input string is answered as the spec entry answers it: the error form unless it reads as exactly one request, else that request's decision
# EXCLUDES: an input theme_ffi_answers and theme_ffi_malformed_exact leave
#   free (a request spelled in a way the speller never writes but the
#   reader reads, one that does not fit the wire) answered otherwise
law theme_ffi_total:
  for +s: String
  {FTh.ffi(s) == th_entry(s) : String}
