# eukhe: the proof of LAW theme_parse_rejected

import Base
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme.bend as Theme

# Completion
# ----------

def Theme.theme_parse_rejected(f, x, h):
  %Equal.sym(TReader.Read, TReader.read(f), TReader.Failed{x}, h) : {TPalette.parse.of(_) == TPalette.Rejected{x} : TPalette.Parsed}
  {==}
