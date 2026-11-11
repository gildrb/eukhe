# eukhe: the proof of LAW tokens_names_exact

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def Tokens.tokens_names_exact(t):
  match t:
    case Tk.Bg{}:
      {==}
    case Tk.Sidebar{}:
      {==}
    case Tk.Raised{}:
      {==}
    case Tk.Surface{}:
      {==}
    case Tk.Hover{}:
      {==}
    case Tk.Primary{}:
      {==}
    case Tk.Secondary{}:
      {==}
    case Tk.Tertiary{}:
      {==}
    case Tk.Hairline{}:
      {==}
    case Tk.Scrim{}:
      {==}
    case Tk.Danger{}:
      {==}
    case Tk.Selection{}:
      {==}
    case Tk.Scrollbar{}:
      {==}
    case Tk.ShadowNear{}:
      {==}
    case Tk.ShadowFar{}:
      {==}
    case Tk.ShadowDrawer{}:
      {==}
    case Tk.ShadowLatest{}:
      {==}
