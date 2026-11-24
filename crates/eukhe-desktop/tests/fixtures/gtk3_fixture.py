"""GTK 3 fixture window for the Linux live tests: a menu bar, a button, an
entry and labels that show what reached them."""

import gi

gi.require_version("Gtk", "3.0")
from gi.repository import Gtk  # noqa: E402

# Focusing the entry keeps its caret instead of selecting all its text.
Gtk.Settings.get_default().set_property("gtk-entry-select-on-focus", False)

window = Gtk.Window(title="eukhe fixture")
window.set_default_size(420, 260)
window.connect("destroy", Gtk.main_quit)
box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=6)

bar = Gtk.MenuBar()
file_item = Gtk.MenuItem(label="File")
menu = Gtk.Menu()
file_item.set_submenu(menu)
open_item = Gtk.MenuItem(label="Open…")
wrap_item = Gtk.CheckMenuItem(label="Wrap")
menu.append(open_item)
menu.append(Gtk.SeparatorMenuItem())
menu.append(wrap_item)
bar.append(file_item)
box.pack_start(bar, False, False, 0)

clicks = Gtk.Label(label="clicks 0")
button = Gtk.Button(label="Press me")
entry = Gtk.Entry()
echo = Gtk.Label(label="entry ")
opened = Gtk.Label(label="menu none")
for widget in (button, clicks, entry, echo, opened):
    box.pack_start(widget, False, False, 0)

count = 0


def on_clicked(_button):
    global count
    count += 1
    clicks.set_text(f"clicks {count}")


button.connect("clicked", on_clicked)
entry.connect("changed", lambda edited: echo.set_text("entry " + edited.get_text()))
open_item.connect("activate", lambda _item: opened.set_text("menu Open"))

window.add(box)
window.show_all()
Gtk.main()
