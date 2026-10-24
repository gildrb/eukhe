# eukhe: the proof of LAW tokens_find_exact
# Induction on the entries; two tones are equal exactly when their places
# are (tfe.eq, by cases).

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tfe.eq(k: Tk.Tone, t: Tk.Tone) -> {Tk.Tone.eq(k, t) == Nat.is_eq(Tokens.idx_spec(k), Tokens.idx_spec(t)) : Bool}:
  match k:
    case Tk.Bg{}:
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
    case Tk.Sidebar{}:
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
    case Tk.Raised{}:
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
    case Tk.Surface{}:
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
    case Tk.Hover{}:
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
    case Tk.Primary{}:
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
    case Tk.Secondary{}:
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
    case Tk.Tertiary{}:
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
    case Tk.Hairline{}:
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
    case Tk.Scrim{}:
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
    case Tk.Danger{}:
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
    case Tk.Selection{}:
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
    case Tk.Scrollbar{}:
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
    case Tk.ShadowNear{}:
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
    case Tk.ShadowFar{}:
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
    case Tk.ShadowDrawer{}:
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
    case Tk.ShadowLatest{}:
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

def tfe.at(b: Bool, -c: Tk.Col, -later: Maybe<&2, Tk.Col>) -> {Maybe.or(&2, Tk.Col, Tk.hit(b, c), later) == Tokens.find_spec.at(b, c, later) : Maybe<&2, Tk.Col>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tfe.go(+t: Tk.Tone, xs: List<&2, Tk.Entry>) -> {Tk.find(t, xs) == Tokens.find_spec(t, xs) : Maybe<&2, Tk.Col>}:
  match xs:
    case Nil{}:
      {==}
    case Tk.Entry{+k, +c} <> +rest:
      %Equal.sym(Maybe<&2, Tk.Col>, Tk.find(t, rest), Tokens.find_spec(t, rest), tfe.go(t, rest)) : {Maybe.or(&2, Tk.Col, Tk.hit(Tk.Tone.eq(k, t), c), _) == Tokens.find_spec(t, Tk.Entry{k, c} <> rest) : Maybe<&2, Tk.Col>}
      %Equal.sym(Bool, Tk.Tone.eq(k, t), Nat.is_eq(Tokens.idx_spec(k), Tokens.idx_spec(t)), tfe.eq(k, t)) : {Maybe.or(&2, Tk.Col, Tk.hit(_, c), Tokens.find_spec(t, rest)) == Tokens.find_spec(t, Tk.Entry{k, c} <> rest) : Maybe<&2, Tk.Col>}
      tfe.at(Nat.is_eq(Tokens.idx_spec(k), Tokens.idx_spec(t)), c, Tokens.find_spec(t, rest))

def Tokens.tokens_find_exact(t, xs):
  tfe.go(t, xs)
