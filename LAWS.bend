# eukhe.com's Neovim: the laws
# ============================
#
# Each law is a claim about the editor's shipped entry (vim/vim.bend):
# Vim.init (the files and the screen size), Vim.step (one event: a key, a
# click, the wheel, a new size) and Vim.frame (what the screen shows),
# Vim.lines (an Oil listing). The host paints Frame and runs Act; it
# decides nothing. A law over `evs` holds after EVERY sequence of events
# from the start, for every set of files and every screen size.
# PROOF.bend proves every law; `bend PROOF.bend --verdict` checks them.
#
# Requirements
#
# R1 The cursor is always on one cell of the screen: on a character of a line (or column 0 of an empty line) in the text rows, on the command line while typing a command, or inside the picker's float. Never between rows, never past a line's end, never off screen; after any sequence of events.
# R2 Motions behave as Neovim's: j k move one line (no further than the first and last), h l one character within the line, 0 and $ to the line's first and last character, gg and G to the first and last line; Esc returns to normal mode from anything.
# R3 'scrolloff' 8 (as much of it as the window holds): the cursor keeps that many lines above and below it on screen, unless the buffer ends first.
# R4 The screen fits: rows x cols cells from the last size event (at least 3 x 12); the number column one entry per text row, each exactly the gutter wide; the statusline exactly cols cells; search hits and the scrollbar inside the text rows; a float inside the screen, each of its rows exactly its width.
# R5 A click on a text cell puts the cursor on that line (the last line when below the text) and on that column (the line's last character when past its end).
# R6 Oil never traps: every listing starts with "../"; "-" goes to the parent folder (at the root it stays); Ctrl-c in a listing (normal mode) returns to a file; "-" from a file opens its folder with the cursor on the file's entry.
# R7 The host never does anything the files did not ask for: the only text ever copied is the install command, and every URL opened appears in a file.
# A1 Every character of a file takes one cell (the site's font is monospace, every glyph checked at build); files hold no wide characters.
# A2 A file with no lines shows one empty line, as Neovim does; past the last file, the window shows one empty line.
# A3 The motion laws (R2, R5) hold from normal mode: after an Esc, which closes a picker, cancels a command line and drops a count or a waiting key.
# A4 j, k, gg and G keep the column ('nostartofline'): a cursor short of its line's end stays on that column, or on the new line's last character when the line is shorter; a cursor at its line's end stays at least as far right.
# R8 The window always shows a real buffer: one of the files, a folder of their paths, or the root; the start shows the first file; Esc never changes what the window shows.
# A6 A click while a command line or picker is open is free (Neovim's command-line mouse is not modeled).
# A5 After Esc the command line may still show the last message or search, as in Neovim; while a command line or a picker is open, the window behind it is not checked for 'scrolloff'.

import Base
import ./laws/vim/screen.bend as ScreenLaws
import ./laws/vim/motion.bend as MotionLaws
import ./laws/vim/mouse.bend as MouseLaws
import ./laws/vim/oil.bend as OilLaws
import ./laws/vim/host.bend as HostLaws
import ./laws/vim/buffers.bend as BuffersLaws
import ./laws/vim/esc.bend as EscLaws
import ./laws/vim/ex.bend as ExLaws
import ./laws/vim/example.bend as ExampleLaws
