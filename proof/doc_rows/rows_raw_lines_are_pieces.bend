# eukhe: the proof of LAW rows_raw_lines_are_pieces

import Base
import ../../laws/doc_rows.bend as DocRows
import ../base/doc_lines/proj.bend as LProj

def DocRows.rows_raw_lines_are_pieces(bs):
  LProj.dlp.raw(bs)
