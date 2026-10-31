# eukhe.com's Neovim: the proofs
# ==============================
#
# Each law of LAWS.bend is proven in its own file in proof/, from the
# lemmas in proof/base.bend and proof/base/. `bend PROOF.bend --verdict`
# checks them all. proof/README.md lists the laws still open and the
# lemmas their proofs need.

import Base
import ./LAWS.bend as Laws
import ./proof/screen/cursor_ok.bend as CursorOk
import ./proof/screen/cursor_on_text.bend as CursorOnText
import ./proof/screen/fits.bend as Fits
import ./proof/screen/edges.bend as Edges
import ./proof/screen/cmdline_cursor.bend as CmdlineCursor
import ./proof/screen/scrolloff.bend as Scrolloff
import ./proof/screen/scrolloff_any.bend as ScrolloffAny
import ./proof/buffers/start_file.bend as StartFile
import ./proof/example/start_example.bend as StartExample
