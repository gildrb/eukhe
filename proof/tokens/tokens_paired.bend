# eukhe: the proof of LAW tokens_paired

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

# The palette
# -----------

def pt.paired_light(t: Tk.Tone) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(Tk.Light{}))) == True{} : Bool}:
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

def pt.paired_dark(t: Tk.Tone) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(Tk.Dark{}))) == True{} : Bool}:
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

def tokens_paired(t: Tk.Tone, m: Tk.Mode) -> {Maybe.is_some(&2, Tk.Col, Tk.find(t, Tk.palette(m))) == True{} : Bool}:
  match m:
    case Tk.Light{}:
      pt.paired_light(t)
    case Tk.Dark{}:
      pt.paired_dark(t)

# (T2) Dashboard tokens

def Tokens.tokens_paired(t, m):
  tokens_paired(t, m)
