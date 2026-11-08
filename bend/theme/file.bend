# theme: the theme file data: values, JSON values, variables, entries, resolved files, and why a value or file is invalid
#
# theme: the theme rules of crates/eukhe-theme (the one theme file
# validator and the one theme name resolver of the terminal UI and the
# HTML export); laws in laws/theme.bend (T1).
# The Rust crate decodes the JSON and reads the files; every decision on
# what it read is here: `parse` (a file's palette, or the error the user
# sees) and `pick` (the theme a name resolves to, and the warnings).
#
# A token is its index in crates/eukhe-theme/src/token.rs `Token::ALL`:
#   0 accent 1 border 2 borderAccent 3 borderMuted 4 success 5 error
#   6 warning 7 muted 8 dim 9 text 10 thinkingText 11 userMessageText
#   12 customMessageText 13 customMessageLabel 14 refinementHeader 15 refinementSummary 16 toolTitle 17 toolOutput
#   18 mdBody 19 mdHeading 20 mdLink 21 mdLinkUrl 22 mdCode 23 mdCodeBlock
#   24 mdCodeBlockBorder 25 mdQuote 26 mdQuoteBorder 27 mdHr 28 mdListBullet 29 toolDiffAdded
#   30 toolDiffRemoved 31 toolDiffText 32 toolDiffContext 33 syntaxComment 34 syntaxKeyword 35 syntaxFunction
#   36 syntaxVariable 37 syntaxString 38 syntaxNumber 39 syntaxType 40 syntaxOperator 41 syntaxPunctuation
#   42 effortLow 43 effortHigh 44 contextHigh 45 liftLight 46 liftDark
#   47 bashMode 48 selectedBg 49 userMessageBg 50 customMessageBg 51 toolPendingBg 52 toolSuccessBg
#   53 toolErrorBg 54 toolDiffAddedBg 55 toolDiffRemovedBg 56 toolPanelBg 57 background 58 foreground
# 48..57 are surfaces (the terminal default there is the background); the
# others are ink (the terminal default there is the foreground).

import Base
import ../color.bend as Co

# Theme files
# -----------

# a color after variable resolution: the terminal default (""), an
# xterm-256 index, or #rrggbb
type Val is Data:
  Dflt{}
  Idx{i: U32}
  Hex{c: Co.Rgb}

# a JSON value of a theme file, as the rule reads it: a string, with the
# index of the variable of that name in the file's variables when there is
# one; a number, as JSON writes it; anything else (null, a bool, an array,
# an object), as JSON writes it
type Json is Data:
  JStr{s: String, at: Maybe<&2, Nat>}
  JNum{text: String}
  JOther{text: String}

type Var is Data:
  Var{name: String, val: Json}

# a color entry: its key, the token the key names (None: no token), its
# value
type REnt is Data:
  REnt{key: String, t: Maybe<&2, U32>, val: Json}

# a theme file: its name, its variables and colors (each in key order),
# and its export page, card and info backgrounds
type RFile is Data:
  RFile{name: String, vars: List<&2, Var>, cols: List<&2, REnt>, page: Maybe<&2, Json>, card: Maybe<&2, Json>, info: Maybe<&2, Json>}

type Ent is Data:
  Ent{t: U32, v: Val}

# a file after variable resolution: its colors and the export page, card
# and info backgrounds it sets (None: unset, or set to "")
type Th is Data:
  Th{name: String, cols: List<&2, Ent>, page: Maybe<&2, Co.Rgb>, card: Maybe<&2, Co.Rgb>, info: Maybe<&2, Co.Rgb>}

# Errors
# ------

# why a value is no color: a variable met twice on its chain, a variable
# that does not exist, a malformed #rrggbb, any other value that is no
# color
type Why is Data:
  Circular{name: String}
  NotFound{name: String}
  BadHex{text: String}
  BadValue{text: String}

# the export backgrounds
type Surf is Data:
  OnPage{}
  OnCard{}
  OnInfo{}

# why a theme file is invalid: a color key that names no token, a color
# whose value is no color, the required tokens it does not write (in token
# order), an export background whose value is no color
type Fault is Data:
  Unknown{key: String}
  InColor{key: String, why: Why}
  Missing{ts: List<&2, U32>}
  InExport{at: Surf, why: Why}
