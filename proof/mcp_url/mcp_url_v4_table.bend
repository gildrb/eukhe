# eukhe: the proof of LAW mcp_url_v4_table
#
# PROOF: each octet's spelling reads as that octet, holds no bracket,
# uppercase letter or `.`, and starts and ends with a digit (LO.mvo.of,
# per octet), so the quad reads as itself, is no localhost name and splits
# into its four octets; the model's ranges then answer as R4's blocks for
# every pair of first octets (LTB.mvt.tab, per pair that matters).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT
import ./mcp_url_v4_table/octet.bend as LO
import ./mcp_url_v4_table/table.bend as LTB

def mvm.go(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ha: {Nat.is_le(a, 255n) == True{} : Bool}, hb: {Nat.is_le(b, 255n) == True{} : Bool}, fa: LO.mvo.OF(a), fb: LO.mvo.OF(b), fc: LO.mvo.OF(c), fd: LO.mvo.OF(d)) -> {Mu.refused(McpUrl.mu_quad(a, b, c, d)) == McpUrl.mu_v4_reserved(a, b) : Bool}:
  (a1, ar1) = fa
  (a2, ar2) = ar1
  (a3, ar3) = ar2
  (a4, ar4) = ar3
  (a5, ar5) = ar4
  (a6, ar6) = ar5
  (a7, a8) = ar6
  (b1, br1) = fb
  (b2, br2) = br1
  (b3, br3) = br2
  (b4, br4) = br3
  (b5, br5) = br4
  (b6, br6) = br5
  (b7, b8) = br6
  (c1, cr1) = fc
  (c2, cr2) = cr1
  (c3, cr3) = cr2
  (c4, cr4) = cr3
  (c5, cr5) = cr4
  (c6, cr6) = cr5
  (c7, c8) = cr6
  (d1, dr1) = fd
  (d2, dr2) = dr1
  (d3, dr3) = dr2
  (d4, dr4) = dr3
  (d5, dr5) = dr4
  (d6, dr6) = dr5
  (d7, d8) = dr6
  +A = Nat.show(a)
  +B = Nat.show(b)
  +C = Nat.show(c)
  +D = Nat.show(d)
  +Y3 = String.append(C, SCon{'.', D})
  +Y2 = String.append(B, SCon{'.', Y3})
  +h = String.append(A, SCon{'.', Y2})
  +z3 = Equal.trans(String, Mu.drop_close(Y3), String.append(C, SCon{'.', Mu.drop_close(D)}), Y3, LT.mt.dca(C, SCon{'.', D}, {==}), Equal.cong(String, String, z => String.append(C, SCon{'.', z}), Mu.drop_close(D), D, d3))
  +z2 = Equal.trans(String, Mu.drop_close(Y2), String.append(B, SCon{'.', Mu.drop_close(Y3)}), Y2, LT.mt.dca(B, SCon{'.', Y3}, {==}), Equal.cong(String, String, z => String.append(B, SCon{'.', z}), Mu.drop_close(Y3), Y3, z3))
  +z1 = Equal.trans(String, Mu.drop_close(h), String.append(A, SCon{'.', Mu.drop_close(Y2)}), h, LT.mt.dca(A, SCon{'.', Y2}, {==}), Equal.cong(String, String, z => String.append(A, SCon{'.', z}), Mu.drop_close(Y2), Y2, z2))
  +l3 = Equal.trans(String, String.to_lower(Y3), String.append(String.to_lower(C), SCon{'.', String.to_lower(D)}), Y3, LT.mt.tl_app(C, SCon{'.', D}), Equal.trans(String, String.append(String.to_lower(C), SCon{'.', String.to_lower(D)}), String.append(C, SCon{'.', String.to_lower(D)}), Y3, Equal.cong(String, String, z => String.append(z, SCon{'.', String.to_lower(D)}), String.to_lower(C), C, c4), Equal.cong(String, String, z => String.append(C, SCon{'.', z}), String.to_lower(D), D, d4)))
  +l2 = Equal.trans(String, String.to_lower(Y2), String.append(String.to_lower(B), SCon{'.', String.to_lower(Y3)}), Y2, LT.mt.tl_app(B, SCon{'.', Y3}), Equal.trans(String, String.append(String.to_lower(B), SCon{'.', String.to_lower(Y3)}), String.append(B, SCon{'.', String.to_lower(Y3)}), Y2, Equal.cong(String, String, z => String.append(z, SCon{'.', String.to_lower(Y3)}), String.to_lower(B), B, b4), Equal.cong(String, String, z => String.append(B, SCon{'.', z}), String.to_lower(Y3), Y3, l3)))
  +l1 = Equal.trans(String, String.to_lower(h), String.append(String.to_lower(A), SCon{'.', String.to_lower(Y2)}), h, LT.mt.tl_app(A, SCon{'.', Y2}), Equal.trans(String, String.append(String.to_lower(A), SCon{'.', String.to_lower(Y2)}), String.append(A, SCon{'.', String.to_lower(Y2)}), h, Equal.cong(String, String, z => String.append(z, SCon{'.', String.to_lower(Y2)}), String.to_lower(A), A, a4), Equal.cong(String, String, z => String.append(A, SCon{'.', z}), String.to_lower(Y2), Y2, l2)))
  +EB = Equal.trans(String, Mu.bare(h), String.to_lower(Mu.drop_close(h)), h, Equal.cong(String, String, z => String.to_lower(Mu.drop_close(z)), Mu.drop_open(h), h, a2(SCon{'.', Y2})), Equal.trans(String, String.to_lower(Mu.drop_close(h)), String.to_lower(h), h, Equal.cong(String, String, z => String.to_lower(z), Mu.drop_close(h), h, z1), l1))
  +acc1 = {SCon{'.', String.reverse.go(A, SNil{})} : String}
  +acc2 = {SCon{'.', String.reverse.go(B, acc1)} : String}
  +acc3 = {SCon{'.', String.reverse.go(C, acc2)} : String}
  +RV = Equal.trans(String, String.reverse.go(h, SNil{}), String.reverse.go(Y2, acc1), String.reverse.go(D, acc3), LT.mt.rev_app(A, SCon{'.', Y2}, SNil{}), Equal.trans(String, String.reverse.go(Y2, acc1), String.reverse.go(Y3, acc2), String.reverse.go(D, acc3), LT.mt.rev_app(B, SCon{'.', Y3}, acc1), LT.mt.rev_app(C, SCon{'.', D}, acc2)))
  +SP3 = Equal.trans(List<&2, String>, String.split(Y3, '.'), C <> String.split(D, '.'), [C, D], c7(D), Equal.cong(List<&2, String>, List<&2, String>, z => C <> z, String.split(D, '.'), [D], d8))
  +SP2 = Equal.trans(List<&2, String>, String.split(Y2, '.'), B <> String.split(Y3, '.'), [B, C, D], b7(Y3), Equal.cong(List<&2, String>, List<&2, String>, z => B <> z, String.split(Y3, '.'), [C, D], SP3))
  +SP = Equal.trans(List<&2, String>, String.split(h, '.'), A <> String.split(Y2, '.'), [A, B, C, D], a7(Y2), Equal.cong(List<&2, String>, List<&2, String>, z => A <> z, String.split(Y2, '.'), [B, C, D], SP2))
  %Equal.sym(String, Mu.bare(h), h, EB) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Bool, String.eq(h, "localhost"), False{}, a5(SCon{'.', Y2})) : {Mu.refused.at(Bool.or(_, String.ends_with(h, ".localhost")), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(String, String.reverse.go(h, SNil{}), String.reverse.go(D, acc3), RV) : {Mu.refused.at(Bool.or(False{}, String.starts_with(_, String.reverse(".localhost"))), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Bool, String.starts_with(String.reverse.go(D, acc3), String.reverse(".localhost")), False{}, d6(acc3)) : {Mu.refused.at(Bool.or(False{}, _), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(List<&2, String>, String.split(h, '.'), [A, B, C, D], SP) : {Mu.after_v4(Mu.v4.parts(_), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Mu.Part, Mu.part(A), Mu.POct{Mu.dec(A, 0)}, a1) : {Mu.after_v4(Mu.quad(_, Mu.part(B), Mu.part(C), Mu.part(D)), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Mu.Part, Mu.part(B), Mu.POct{Mu.dec(B, 0)}, b1) : {Mu.after_v4(Mu.quad(Mu.POct{Mu.dec(A, 0)}, _, Mu.part(C), Mu.part(D)), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Mu.Part, Mu.part(C), Mu.POct{Mu.dec(C, 0)}, c1) : {Mu.after_v4(Mu.quad(Mu.POct{Mu.dec(A, 0)}, Mu.POct{Mu.dec(B, 0)}, _, Mu.part(D)), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  %Equal.sym(Mu.Part, Mu.part(D), Mu.POct{Mu.dec(D, 0)}, d1) : {Mu.after_v4(Mu.quad(Mu.POct{Mu.dec(A, 0)}, Mu.POct{Mu.dec(B, 0)}, Mu.POct{Mu.dec(C, 0)}, _), h) == McpUrl.mu_v4_reserved(a, b) : Bool}
  LTB.mvt.tab(a, b, ha, hb)

def McpUrl.mcp_url_v4_table(a, b, c, d, oct):
  +o0 = oct
  +o1 = LT.mt.and_r(Nat.is_le(a, 255n), Bool.and(Nat.is_le(b, 255n), Bool.and(Nat.is_le(c, 255n), Nat.is_le(d, 255n))), o0)
  +o2 = LT.mt.and_r(Nat.is_le(b, 255n), Bool.and(Nat.is_le(c, 255n), Nat.is_le(d, 255n)), o1)
  +ha = LT.mt.and_l(Nat.is_le(a, 255n), Bool.and(Nat.is_le(b, 255n), Bool.and(Nat.is_le(c, 255n), Nat.is_le(d, 255n))), o0)
  +hb = LT.mt.and_l(Nat.is_le(b, 255n), Bool.and(Nat.is_le(c, 255n), Nat.is_le(d, 255n)), o1)
  +hc = LT.mt.and_l(Nat.is_le(c, 255n), Nat.is_le(d, 255n), o2)
  +hd = LT.mt.and_r(Nat.is_le(c, 255n), Nat.is_le(d, 255n), o2)
  mvm.go(a, b, c, d, ha, hb, LO.mvo.of(a, ha), LO.mvo.of(b, hb), LO.mvo.of(c, hc), LO.mvo.of(d, hd))
