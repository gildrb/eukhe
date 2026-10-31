# eukhe.com's Neovim: the proofs
# ==============================
#
# Each law of LAWS.bend is proven in its own file in proof/, from the
# lemmas in proof/base.bend. `bend PROOF.bend --verdict` checks them all.

import Base
import ./LAWS.bend as Laws
