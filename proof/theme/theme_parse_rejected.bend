# eukhe: the proof of LAW theme_parse_rejected

import Base
import ../../bend/theme.bend as T
import ../../LAWS.bend as Laws

# Completion
# ----------

def Laws.theme_parse_rejected(f, x, h):
  %Equal.sym(T.Read, T.read(f), T.Failed{x}, h) : {T.parse.of(_) == T.Rejected{x} : T.Parsed}
  {==}
