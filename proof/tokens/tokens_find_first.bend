# eukhe: the proof of LAW tokens_find_first
# Induction on the entries before t's: each has another tone, so the
# code's tone test (Tone.eq, equal to tone_same by cases: tff.eq) misses
# it; at t's entry the test hits (tff.here, by cases).

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tff.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def tff.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tff.BD(_, A, Unit)
  Unit{}

def tff.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tff.absurdF({False{} == True{} : Bool}, h)

def tff.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tff.absurdF({b == True{} : Bool}, h)

def tff.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      tff.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def tff.eq(k: Tk.Tone, t: Tk.Tone) -> {Tk.Tone.eq(k, t) == Tokens.tone_same(k, t) : Bool}:
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

def tff.here(t: Tk.Tone, -c: Tk.Col, -post: List<&2, Tk.Entry>) -> {Tk.find(t, Tk.Entry{t, c} <> post) == Some{c} : Maybe<&2, Tk.Col>}:
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

def tff.go(+t: Tk.Tone, +pre: List<&2, Tk.Entry>, +c: Tk.Col, +post: List<&2, Tk.Entry>, +no: {Tokens.absent(t, pre) == True{} : Bool}) -> {Tk.find(t, List.append(&2, Tk.Entry, pre, Tk.Entry{t, c} <> post)) == Some{c} : Maybe<&2, Tk.Col>}:
  match pre:
    case Nil{}:
      tff.here(t, c, post)
    case Con{e, rest}:
      match e:
        case Tk.Entry{+k, d}:
          +ne = tff.not_true(Tokens.tone_same(k, t), tff.and_l(Bool.not(Tokens.tone_same(k, t)), Tokens.absent(t, rest), no))
          +neq = Equal.trans(Bool, Tk.Tone.eq(k, t), Tokens.tone_same(k, t), False{}, tff.eq(k, t), ne)
          %Equal.sym(Bool, Tk.Tone.eq(k, t), False{}, neq) : {Maybe.or(&2, Tk.Col, Tk.hit(_, d), Tk.find(t, List.append(&2, Tk.Entry, rest, Tk.Entry{t, c} <> post))) == Some{c} : Maybe<&2, Tk.Col>}
          tff.go(t, rest, c, post, tff.and_r(Bool.not(Tokens.tone_same(k, t)), Tokens.absent(t, rest), no))

def Tokens.tokens_find_first(t, pre, c, post, no):
  tff.go(t, pre, c, post, no)
