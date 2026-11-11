# eukhe.com's Neovim: the laws of examples
# ========================================
#
# The terms are in base.bend; LAWS.bend lists the requirements.

import Base
import ../../vim/types.bend as T
import ../../vim/vim.bend as V
import ./base.bend as Laws

# Laws
# ----

# LAW start_example: the start on a 10 x 40 screen: the first file's
# first character, right of a 6-cell gutter (2 signs, 4 numbers).
law start_example:
  {Laws.Example.start() == True{} : Bool}
