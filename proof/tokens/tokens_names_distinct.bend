# eukhe: the proof of LAW tokens_names_distinct
# A reader of the keys (tnd.key: the keys of lightPalette in
# tokens.stylex.ts) takes every tone's key back to the tone (tnd.inv, by
# cases), so tones with one key are one tone.

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tnd.key.at(hit: Bool, t: Tk.Tone, later: Maybe<&2, Tk.Tone>) -> Maybe<&2, Tk.Tone>:
  match hit:
    case True{}:
      Some{t}
    case False{}:
      later

def tnd.key(+s: String) -> Maybe<&2, Tk.Tone>:
  tnd.key.at(String.eq(s, "bg"), Tk.Bg{}, tnd.key.at(String.eq(s, "sidebar"), Tk.Sidebar{}, tnd.key.at(String.eq(s, "raised"), Tk.Raised{}, tnd.key.at(String.eq(s, "surface"), Tk.Surface{}, tnd.key.at(String.eq(s, "hover"), Tk.Hover{}, tnd.key.at(String.eq(s, "primary"), Tk.Primary{}, tnd.key.at(String.eq(s, "secondary"), Tk.Secondary{}, tnd.key.at(String.eq(s, "tertiary"), Tk.Tertiary{}, tnd.key.at(String.eq(s, "hairline"), Tk.Hairline{}, tnd.key.at(String.eq(s, "scrim"), Tk.Scrim{}, tnd.key.at(String.eq(s, "danger"), Tk.Danger{}, tnd.key.at(String.eq(s, "selection"), Tk.Selection{}, tnd.key.at(String.eq(s, "scrollbar"), Tk.Scrollbar{}, tnd.key.at(String.eq(s, "shadowNear"), Tk.ShadowNear{}, tnd.key.at(String.eq(s, "shadowFar"), Tk.ShadowFar{}, tnd.key.at(String.eq(s, "shadowDrawer"), Tk.ShadowDrawer{}, tnd.key.at(String.eq(s, "shadowLatest"), Tk.ShadowLatest{}, None{})))))))))))))))))

def tnd.inv(t: Tk.Tone) -> {tnd.key(Tk.Tone.name(t)) == Some{t} : Maybe<&2, Tk.Tone>}:
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

def Tokens.tokens_names_distinct(a, b, same):
  +e = Equal.trans(Maybe<&2, Tk.Tone>, Some{a}, tnd.key(Tk.Tone.name(b)), Some{b}, Equal.trans(Maybe<&2, Tk.Tone>, Some{a}, tnd.key(Tk.Tone.name(a)), tnd.key(Tk.Tone.name(b)), Equal.sym(Maybe<&2, Tk.Tone>, tnd.key(Tk.Tone.name(a)), Some{a}, tnd.inv(a)), Equal.cong(String, Maybe<&2, Tk.Tone>, z => tnd.key(z), Tk.Tone.name(a), Tk.Tone.name(b), same)), tnd.inv(b))
  Equal.cong(Maybe<&2, Tk.Tone>, Tk.Tone, o => Maybe.default(&2, Tk.Tone, o, a), Some{a}, Some{b}, e)
