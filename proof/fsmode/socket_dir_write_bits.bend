# eukhe: the proof of LAW socket_dir_write_bits
# The entry answers the spelled request with the laws' reply
# (fsmode_ffi_answers): a dir of this uid is refused exactly when the
# write bit test wbit(m, 16) or wbit(m, 2) holds. For m = 64 h + c the
# test reads only c (sw.w16, sw.w2: Nat.divmod.go counts 64 h in whole
# rounds of 16 and of 2, adding 4 h and 32 h to the quotient, which keeps
# its parity), and for c = 8 g + o with g, o below 8 the 64 cases compute
# to the POSIX digit table (sw.digits).

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LA
import ./fsmode_ffi_answers.bend as PFsmodeFfiAnswers

# The quotient's growth
# ---------------------

# d plus 4 h (sw.q4) and plus 32 h (sw.q32), the h on top
def sw.q4(h: Nat, d: Nat) -> Nat:
  match h:
    case 0n:
      d
    case 1n++j:
      4n+sw.q4(j, d)

def sw.q32(h: Nat, d: Nat) -> Nat:
  match h:
    case 0n:
      d
    case 1n++j:
      32n+sw.q32(j, d)

def sw.q4_succ(h: Nat, -d: Nat) -> {sw.q4(h, 1n+d) == 1n+sw.q4(h, d) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.cong(Nat, Nat, z => 4n+z, sw.q4(j, 1n+d), 1n+sw.q4(j, d), sw.q4_succ(j, d))

def sw.q32_succ(h: Nat, -d: Nat) -> {sw.q32(h, 1n+d) == 1n+sw.q32(h, d) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.cong(Nat, Nat, z => 32n+z, sw.q32(j, 1n+d), 1n+sw.q32(j, d), sw.q32_succ(j, d))

def sw.q4_four(h: Nat, -d: Nat) -> {sw.q4(h, 4n+d) == 4n+sw.q4(h, d) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.cong(Nat, Nat, z => 4n+z, sw.q4(j, 4n+d), 4n+sw.q4(j, d), sw.q4_four(j, d))

def sw.q32_more(h: Nat, -d: Nat) -> {sw.q32(h, 32n+d) == 32n+sw.q32(h, d) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.cong(Nat, Nat, z => 32n+z, sw.q32(j, 32n+d), 32n+sw.q32(j, d), sw.q32_more(j, d))

# Nat.divmod.go over 64 h then c
# ------------------------------

# by 16: 64 more counted are 4 more rounds
def sw.go16(h: Nat, +c: Nat, +d: Nat) -> {Nat.divmod.go(Nat.add(Nat.mul(h, 64n), c), 15n, d, 0n) == Nat.divmod.go(c, 15n, sw.q4(h, d), 0n) : Nat & Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(j, 64n), c), 15n, 4n+d, 0n), Nat.divmod.go(c, 15n, sw.q4(j, 4n+d), 0n), Nat.divmod.go(c, 15n, 4n+sw.q4(j, d), 0n),
        sw.go16(j, c, 4n+d),
        Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(c, 15n, z, 0n), sw.q4(j, 4n+d), 4n+sw.q4(j, d), sw.q4_four(j, d)))

# by 2: 64 more counted are 32 more rounds
def sw.go2(h: Nat, +c: Nat, +d: Nat) -> {Nat.divmod.go(Nat.add(Nat.mul(h, 64n), c), 1n, d, 0n) == Nat.divmod.go(c, 1n, sw.q32(h, d), 0n) : Nat & Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.trans(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(j, 64n), c), 1n, 32n+d, 0n), Nat.divmod.go(c, 1n, sw.q32(j, 32n+d), 0n), Nat.divmod.go(c, 1n, 32n+sw.q32(j, d), 0n),
        sw.go2(j, c, 32n+d),
        Equal.cong(Nat, Nat & Nat, z => Nat.divmod.go(c, 1n, z, 0n), sw.q32(j, 32n+d), 32n+sw.q32(j, d), sw.q32_more(j, d)))

# the quotient grows by what the accumulator starts with
def sw.fst4(n: Nat, +m: Nat, +h: Nat, +d: Nat, +r: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, sw.q4(h, d), r)) == sw.q4(h, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          %sw.q4_succ(h, d) : {Pair.fst(Nat, Nat, Nat.divmod.go(np, r, _, 0n)) == sw.q4(h, Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) : Nat}
          sw.fst4(np, r, h, 1n+d, 0n)
        case 1n++mp:
          sw.fst4(np, mp, h, d, 1n+r)

def sw.fst32(n: Nat, +m: Nat, +h: Nat, +d: Nat, +r: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, sw.q32(h, d), r)) == sw.q32(h, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          %sw.q32_succ(h, d) : {Pair.fst(Nat, Nat, Nat.divmod.go(np, r, _, 0n)) == sw.q32(h, Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n))) : Nat}
          sw.fst32(np, r, h, 1n+d, 0n)
        case 1n++mp:
          sw.fst32(np, mp, h, d, 1n+r)

# the remainder never reads the quotient
def sw.snd(n: Nat, +m: Nat, +d: Nat, +e: Nat, +r: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, e, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++np:
      match m:
        case 0n:
          sw.snd(np, r, 1n+d, 1n+e, 0n)
        case 1n++mp:
          sw.snd(np, mp, d, e, 1n+r)

# 4 h and 32 h are even: the parity is the parity of the rest
def sw.par4(h: Nat, +x: Nat, +e: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(sw.q4(h, x), 1n, e, 0n)) == Pair.snd(Nat, Nat, Nat.divmod.go(x, 1n, e, 0n)) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(sw.q4(j, x), 1n, 2n+e, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(sw.q4(j, x), 1n, e, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, 1n, e, 0n)),
        sw.snd(sw.q4(j, x), 1n, 2n+e, e, 0n),
        sw.par4(j, x, e))

def sw.par32(h: Nat, +x: Nat, +e: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(sw.q32(h, x), 1n, e, 0n)) == Pair.snd(Nat, Nat, Nat.divmod.go(x, 1n, e, 0n)) : Nat}:
  match h:
    case 0n:
      {==}
    case 1n++j:
      Equal.trans(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(sw.q32(j, x), 1n, 16n+e, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(sw.q32(j, x), 1n, e, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(x, 1n, e, 0n)),
        sw.snd(sw.q32(j, x), 1n, 16n+e, e, 0n),
        sw.par32(j, x, e))

# The write bits read only the low six bits
# -----------------------------------------

def sw.w16(+h: Nat, +c: Nat) -> {Fsmode.wbit(c, 16n) == Fsmode.wbit(Nat.add(Nat.mul(h, 64n), c), 16n) : Bool}:
  +y = {Pair.fst(Nat, Nat, Nat.divmod.go(c, 15n, 0n, 0n)) : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(h, 64n), c), 15n, 0n, 0n), Nat.divmod.go(c, 15n, sw.q4(h, 0n), 0n), sw.go16(h, c, 0n)) : {Fsmode.wbit(c, 16n) == Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Pair.fst(Nat, Nat, _), 1n, 0n, 0n)), 1n) : Bool}
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(c, 15n, sw.q4(h, 0n), 0n)), sw.q4(h, y), sw.fst4(c, 15n, h, 0n, 0n)) : {Fsmode.wbit(c, 16n) == Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(_, 1n, 0n, 0n)), 1n) : Bool}
  %Equal.sym(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(sw.q4(h, y), 1n, 0n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(y, 1n, 0n, 0n)), sw.par4(h, y, 0n)) : {Fsmode.wbit(c, 16n) == Nat.is_eq(_, 1n) : Bool}
  {==}

def sw.w2(+h: Nat, +c: Nat) -> {Fsmode.wbit(c, 2n) == Fsmode.wbit(Nat.add(Nat.mul(h, 64n), c), 2n) : Bool}:
  +y = {Pair.fst(Nat, Nat, Nat.divmod.go(c, 1n, 0n, 0n)) : Nat}
  %Equal.sym(Nat & Nat, Nat.divmod.go(Nat.add(Nat.mul(h, 64n), c), 1n, 0n, 0n), Nat.divmod.go(c, 1n, sw.q32(h, 0n), 0n), sw.go2(h, c, 0n)) : {Fsmode.wbit(c, 2n) == Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(Pair.fst(Nat, Nat, _), 1n, 0n, 0n)), 1n) : Bool}
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(c, 1n, sw.q32(h, 0n), 0n)), sw.q32(h, y), sw.fst32(c, 1n, h, 0n, 0n)) : {Fsmode.wbit(c, 2n) == Nat.is_eq(Pair.snd(Nat, Nat, Nat.divmod.go(_, 1n, 0n, 0n)), 1n) : Bool}
  %Equal.sym(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(sw.q32(h, y), 1n, 0n, 0n)), Pair.snd(Nat, Nat, Nat.divmod.go(y, 1n, 0n, 0n)), sw.par32(h, y, 0n)) : {Fsmode.wbit(c, 2n) == Nat.is_eq(_, 1n) : Bool}
  {==}

# The digit table
# ---------------

# a digit past 7 is excluded by its premise
def sw.big(-G: Type, q: Nat, e: {Nat.is_lt(8n+q, 8n) == True{} : Bool}) -> G:
  match q:
    case 0n:
      LA.fsmode.pf.absurdF(G, e)
    case 1n+r:
      LA.fsmode.pf.absurdF(G, e)

# for octal digits g and o, the write test of 8 g + o is the POSIX table
def sw.digits(g: Nat, o: Nat, gd: {Nat.is_lt(g, 8n) == True{} : Bool}, od: {Nat.is_lt(o, 8n) == True{} : Bool}) -> {Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(g, 8n), o), 16n), Fsmode.wbit(Nat.add(Nat.mul(g, 8n), o), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(g), Fsmode.writes(o))) : String}:
  match g:
    case 0n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(0n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(0n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(0n), Fsmode.writes(8n+q))) : String}, q, od)
    case 1n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(1n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(1n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(1n), Fsmode.writes(8n+q))) : String}, q, od)
    case 2n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(2n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(2n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(2n), Fsmode.writes(8n+q))) : String}, q, od)
    case 3n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(3n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(3n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(3n), Fsmode.writes(8n+q))) : String}, q, od)
    case 4n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(4n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(4n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(4n), Fsmode.writes(8n+q))) : String}, q, od)
    case 5n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(5n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(5n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(5n), Fsmode.writes(8n+q))) : String}, q, od)
    case 6n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(6n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(6n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(6n), Fsmode.writes(8n+q))) : String}, q, od)
    case 7n:
      match o:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n:
          {==}
        case 6n:
          {==}
        case 7n:
          {==}
        case 8n+q:
          sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(7n, 8n), 8n+q), 16n), Fsmode.wbit(Nat.add(Nat.mul(7n, 8n), 8n+q), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(7n), Fsmode.writes(8n+q))) : String}, q, od)
    case 8n+p:
      sw.big({Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(Nat.add(Nat.mul(8n+p, 8n), o), 16n), Fsmode.wbit(Nat.add(Nat.mul(8n+p, 8n), o), 2n))) == Fsmode.write_reply(Bool.or(Fsmode.writes(8n+p), Fsmode.writes(o))) : String}, p, gd)

# Nat.is_eq(u, u)
def sw.eq_refl(u: Nat) -> {Nat.is_eq(u, u) == True{} : Bool}:
  match u:
    case 0n:
      {==}
    case 1n+p:
      sw.eq_refl(p)

def Fsmode.socket_dir_write_bits(u, h, g, o, gd, od, fits):
  +c = {Nat.add(Nat.mul(g, 8n), o) : Nat}
  +a = {Fs.AskDir{Fs.Dir{}, u, u, Fsmode.perm(h, g, o)} : Fs.Ask}
  +w = {Fsmode.write_reply(Bool.or(Fsmode.writes(g), Fsmode.writes(o))) : String}
  %Equal.sym(String, FFs.ffi(Fsmode.spell_ask(a)), Fsmode.spell_answer(a), Fsmode.fsmode_ffi_answers(a, fits)) : {_ == w : String}
  %Equal.sym(Bool, Nat.is_eq(u, u), True{}, sw.eq_refl(u)) : {Fsmode.dir_reply.dir(_, Bool.or(Fsmode.wbit(Fsmode.perm(h, g, o), 16n), Fsmode.wbit(Fsmode.perm(h, g, o), 2n))) == w : String}
  %sw.w16(h, c) : {Fsmode.dir_reply.dir(True{}, Bool.or(_, Fsmode.wbit(Nat.add(Nat.mul(h, 64n), c), 2n))) == w : String}
  %sw.w2(h, c) : {Fsmode.dir_reply.dir(True{}, Bool.or(Fsmode.wbit(c, 16n), _)) == w : String}
  sw.digits(g, o, gd, od)
