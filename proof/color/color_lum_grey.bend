# eukhe: the proof of LAW color_lum_grey: the three weighted terms of a gray
# sum to 10000 times its linear value at every leaf of lin's table (a
# closed check per part, cl.table), so at lin(c) for every c (cl.lin, a
# walk of the table)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl

def lumg.t0() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t0()) == True{} : Bool}:
  {==}

def lumg.t1() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t1()) == True{} : Bool}:
  {==}

def lumg.t2() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t2()) == True{} : Bool}:
  {==}

def lumg.t3() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t3()) == True{} : Bool}:
  {==}

def lumg.t4() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t4()) == True{} : Bool}:
  {==}

def lumg.t5() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t5()) == True{} : Bool}:
  {==}

def lumg.t6() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t6()) == True{} : Bool}:
  {==}

def lumg.t7() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t7()) == True{} : Bool}:
  {==}

def lumg.t8() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t8()) == True{} : Bool}:
  {==}

def lumg.t9() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t9()) == True{} : Bool}:
  {==}

def lumg.t10() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t10()) == True{} : Bool}:
  {==}

def lumg.t11() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t11()) == True{} : Bool}:
  {==}

def lumg.t12() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t12()) == True{} : Bool}:
  {==}

def lumg.t13() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t13()) == True{} : Bool}:
  {==}

def lumg.t14() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t14()) == True{} : Bool}:
  {==}

def lumg.t15() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.t15()) == True{} : Bool}:
  {==}

# every leaf of lin's table, part by part
def lumg.all() -> {LCl.cl.all(LCl.ClGrey{}, Co.lin.table()) == True{} : Bool}:
  LCl.cl.table(LCl.ClGrey{}, lumg.t0(), lumg.t1(), lumg.t2(), lumg.t3(), lumg.t4(), lumg.t5(), lumg.t6(), lumg.t7(), lumg.t8(), lumg.t9(), lumg.t10(), lumg.t11(), lumg.t12(), lumg.t13(), lumg.t14(), lumg.t15())

def Color.color_lum_grey(c):
  LCl.cl.eq((2126 * Co.lin(c) + 7152 * Co.lin(c) + 722 * Co.lin(c) : U32), (10000 * Co.lin(c) : U32), LCl.cl.lin(LCl.ClGrey{}, c, {==}, lumg.all()))
