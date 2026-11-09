# eukhe: the proof of LAW color_lum_order: blue alone at most red alone at
# most green alone, at every leaf of lin's table (a closed check per part,
# cl.table), so at lin(c) for every c (cl.lin, a walk of the table)

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl

def lumo.t0() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t0()) == True{} : Bool}:
  {==}

def lumo.t1() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t1()) == True{} : Bool}:
  {==}

def lumo.t2() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t2()) == True{} : Bool}:
  {==}

def lumo.t3() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t3()) == True{} : Bool}:
  {==}

def lumo.t4() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t4()) == True{} : Bool}:
  {==}

def lumo.t5() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t5()) == True{} : Bool}:
  {==}

def lumo.t6() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t6()) == True{} : Bool}:
  {==}

def lumo.t7() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t7()) == True{} : Bool}:
  {==}

def lumo.t8() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t8()) == True{} : Bool}:
  {==}

def lumo.t9() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t9()) == True{} : Bool}:
  {==}

def lumo.t10() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t10()) == True{} : Bool}:
  {==}

def lumo.t11() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t11()) == True{} : Bool}:
  {==}

def lumo.t12() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t12()) == True{} : Bool}:
  {==}

def lumo.t13() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t13()) == True{} : Bool}:
  {==}

def lumo.t14() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t14()) == True{} : Bool}:
  {==}

def lumo.t15() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.t15()) == True{} : Bool}:
  {==}

# every leaf of lin's table, part by part
def lumo.all() -> {LCl.cl.all(LCl.ClOrder{}, Co.lin.table()) == True{} : Bool}:
  LCl.cl.table(LCl.ClOrder{}, lumo.t0(), lumo.t1(), lumo.t2(), lumo.t3(), lumo.t4(), lumo.t5(), lumo.t6(), lumo.t7(), lumo.t8(), lumo.t9(), lumo.t10(), lumo.t11(), lumo.t12(), lumo.t13(), lumo.t14(), lumo.t15())

def Color.color_lum_order(c):
  LCl.cl.lin(LCl.ClOrder{}, c, {==}, lumo.all())
