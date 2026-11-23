# eukhe.com's Neovim: the proof of LAW start_file
# ===============================================
#
# Vim.start shows file 0; Vim.real keeps it or falls back to file 0
# (either way file 0), and Vim.fit (Win.settle) keeps what the window
# shows.

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/buffers.bend as BuffersLaws

def StartFile.pick(b: Bool) -> {S.Win.tgt(Bool.pick(T.Win, b, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n})) == T.File{0n} : T.Tgt}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def BuffersLaws.start_file(fs, rows, cols):
  StartFile.pick(Nat.is_lt(0n, Nat.max(B.Files.len(B.Files.some(fs, Nil{})), 1n)))
