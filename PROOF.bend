# eukhe.com's Neovim: the proofs
# ==============================
#
# Each law of laws/vim/ is proven in its own file in proof/vim/, from the
# lemmas in proof/base.bend and proof/base/. `bend PROOF.bend --verdict`
# checks them all. proof/README.md lists the laws still open and the
# lemmas their proofs need.

import Base
import ./LAWS.bend as Laws
import ./proof/vim/screen/cursor_ok.bend as CursorOk
import ./proof/vim/screen/cursor_on_text.bend as CursorOnText
import ./proof/vim/screen/fits.bend as Fits
import ./proof/vim/screen/edges.bend as Edges
import ./proof/vim/screen/cmdline_cursor.bend as CmdlineCursor
import ./proof/vim/screen/scrolloff.bend as Scrolloff
import ./proof/vim/screen/scrolloff_any.bend as ScrolloffAny
import ./proof/vim/buffers/start_file.bend as StartFile
import ./proof/vim/buffers/real_buffer.bend as RealBuffer
import ./proof/vim/example/start_example.bend as StartExample
import ./proof/vim/ex/colon.bend as Colon
import ./proof/vim/ex/ex_line.bend as ExLine
import ./proof/vim/mouse/click.bend as Click
import ./proof/vim/host/honest.bend as Honest
import ./proof/vim/host/urls.bend as Urls
import ./proof/vim/esc/esc_closes.bend as EscCloses
import ./proof/vim/esc/oil_close.bend as OilClose
import ./proof/vim/esc/esc_keeps.bend as EscKeeps
import ./proof/vim/esc/esc_idle.bend as EscIdle
import ./proof/vim/oil/up_entry.bend as OilUpEntry
import ./proof/vim/oil/parent.bend as OilParent
import ./proof/vim/oil/open.bend as OilOpen
import ./proof/vim/oil/back.bend as OilBack
import ./proof/vim/oil/listing.bend as OilListing
import ./proof/vim/motion/key_j.bend as KeyJ
import ./proof/vim/motion/key_k.bend as KeyK
import ./proof/vim/motion/key_gg.bend as KeyGg
import ./proof/vim/motion/key_G.bend as KeyBigG
import ./proof/vim/motion/key_0.bend as KeyZero
import ./proof/vim/motion/key_dollar.bend as KeyDollar
import ./proof/vim/motion/key_h.bend as KeyH
import ./proof/vim/motion/key_l.bend as KeyL
import ./proof/vim/motion/col_j.bend as ColJ
import ./proof/vim/motion/col_k.bend as ColK
import ./proof/vim/motion/col_gg.bend as ColGg
import ./proof/vim/motion/col_G.bend as ColBigG
import ./proof/vim/motion/j_view.bend as JView
