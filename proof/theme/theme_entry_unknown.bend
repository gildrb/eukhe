# eukhe: the proof of LAW theme_entry_unknown

import Base
import ../../laws/theme.bend as Theme

# Reading a file
# --------------
# The entries read in order and the first that does not read stops the
# file; every entry reads, so the entries are their colors; the missing
# list is the rule's absent list; then the export backgrounds decide.

def Theme.theme_entry_unknown(vars, k, j):
  {==}
