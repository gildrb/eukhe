# eukhe: the proof of LAW search_note_count_exact: the account is the
# count of each class (LAW grep_account_exact); each notice reads its
# class's counter

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./grep_account_exact.bend as PGrepAccountExact

def snc.why(+os: List<&2, Sr.Out>, w: Sr.Reason) -> {Sr.Note.count(Sr.Count{DocSearch.ds_n(os, 0n), DocSearch.ds_n(os, 1n), DocSearch.ds_n(os, 2n), DocSearch.ds_n(os, 3n), DocSearch.ds_n(os, 4n), DocSearch.ds_n(os, 5n), DocSearch.ds_n(os, 6n), DocSearch.ds_n(os, 7n), DocSearch.ds_n(os, 8n), DocSearch.ds_partials(os)}, Sr.NSkip{w}) == DocSearch.ds_note_n(os, Sr.NSkip{w}) : Nat}:
  match w:
    case Sr.Binary{}:
      {==}
    case Sr.Unreadable{}:
      {==}
    case Sr.Excluded{}:
      {==}
    case Sr.Link{}:
      {==}
    case Sr.Broken{}:
      {==}

def snc.count(+os: List<&2, Sr.Out>, n: Sr.Note) -> {Sr.Note.count(Sr.Count{DocSearch.ds_n(os, 0n), DocSearch.ds_n(os, 1n), DocSearch.ds_n(os, 2n), DocSearch.ds_n(os, 3n), DocSearch.ds_n(os, 4n), DocSearch.ds_n(os, 5n), DocSearch.ds_n(os, 6n), DocSearch.ds_n(os, 7n), DocSearch.ds_n(os, 8n), DocSearch.ds_partials(os)}, n) == DocSearch.ds_note_n(os, n) : Nat}:
  match n:
    case Sr.NSkip{w}:
      snc.why(os, w)
    case Sr.NPartial{}:
      {==}
    case Sr.NUnsearched{}:
      {==}

def DocSearch.search_note_count_exact(os, n):
  %Equal.sym(Sr.Count, Sr.account(os), Sr.Count{DocSearch.ds_n(os, 0n), DocSearch.ds_n(os, 1n), DocSearch.ds_n(os, 2n), DocSearch.ds_n(os, 3n), DocSearch.ds_n(os, 4n), DocSearch.ds_n(os, 5n), DocSearch.ds_n(os, 6n), DocSearch.ds_n(os, 7n), DocSearch.ds_n(os, 8n), DocSearch.ds_partials(os)}, DocSearch.grep_account_exact(os)) : {Sr.Note.count(_, n) == DocSearch.ds_note_n(os, n) : Nat}
  snc.count(os, n)
