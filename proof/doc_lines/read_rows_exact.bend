# eukhe: the proof of LAW read_rows_exact: an empty text computes; read's
# rows of any other text are grep's (LAW grep_line_is_read_line), which
# are the spec's (LAW grep_rows_exact)

import Base
import ../../bend/doc_lines.bend as Dl
import ../../laws/doc_lines.bend as DocLines
import ./grep_line_is_read_line.bend as PGrepLineIsReadLine
import ./grep_rows_exact.bend as PGrepRowsExact

def DocLines.read_rows_exact(bs):
  match bs:
    case Nil{}:
      {==}
    case +b <> +rest:
      Equal.trans(List<&2, List<&2, Dl.B>>, Dl.read_rows(b <> rest), Dl.grep_rows(b <> rest), DocLines.lines.ReadRows(b <> rest), Equal.sym(List<&2, List<&2, Dl.B>>, Dl.grep_rows(b <> rest), Dl.read_rows(b <> rest), DocLines.grep_line_is_read_line(b, rest)), DocLines.grep_rows_exact(b <> rest))
