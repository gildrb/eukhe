# eukhe: the proof of LAW rows_gate_names_the_refusal
#
# PROOF: every raw, utf8, utf16 and nul: a read that goes on contradicts
# the premise; for the others both sides compute equal.

import Base
import ../../bend/doc_rows.bend as Dr
import ../../laws/doc_rows.bend as DocRows

def rgn.BD(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# True is not False
def rgn.absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : rgn.BD(_, G)
  Unit{}

def rgn.go(utf8: Bool, utf16: Bool, nul: Bool, refused: {DocRows.rows.Goes(Dr.gate(False{}, utf8, utf16, nul)) == False{} : Bool}) -> {DocRows.rows.IsBinary(Dr.gate(False{}, utf8, utf16, nul)) == Bool.and(nul, Bool.not(Bool.and(utf16, Bool.not(utf8)))) : Bool}:
  match utf8:
    case True{}:
      match utf16:
        case True{}:
          match nul:
            case True{}:
              {==}
            case False{}:
              rgn.absurd({DocRows.rows.IsBinary(Dr.Go{}) == Bool.and(False{}, Bool.not(Bool.and(True{}, Bool.not(True{})))) : Bool}, refused)
        case False{}:
          match nul:
            case True{}:
              {==}
            case False{}:
              rgn.absurd({DocRows.rows.IsBinary(Dr.Go{}) == Bool.and(False{}, Bool.not(Bool.and(False{}, Bool.not(True{})))) : Bool}, refused)
    case False{}:
      match utf16:
        case True{}:
          match nul:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match nul:
            case True{}:
              {==}
            case False{}:
              {==}

def DocRows.rows_gate_names_the_refusal(raw, utf8, utf16, nul, refused):
  match raw:
    case True{}:
      rgn.absurd({DocRows.rows.IsBinary(Dr.gate(True{}, utf8, utf16, nul)) == Bool.and(nul, Bool.not(Bool.and(utf16, Bool.not(utf8)))) : Bool}, refused)
    case False{}:
      rgn.go(utf8, utf16, nul, refused)
