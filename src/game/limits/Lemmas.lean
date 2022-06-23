import game.limits.bounded_if_convergent
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith


namespace xena -- hide

local notation `|`x`|` := abs x

lemma mul_le_mul_left1 {a b c : ℝ} (hanonneg : 0 ≤ a) (hbc : b ≤ c) :
  a * b ≤ a * c :=
begin
  have fact1 : 0 ≤ c - b,
  linarith,
  have fact2 : 0 ≤ a * (c - b),
  exact mul_nonneg hanonneg fact1,
  have fact3 : 0 ≤ a * c - a * b,
  linarith,
  have fact4 : a * b ≤ a * c,
  linarith,
  tauto,
end


lemma mul_le_mul_right1 {a b c : ℝ} (hanonneg : 0 ≤ a) (hbc : b ≤ c) :
  b * a ≤ c * a :=
begin
  have f1 : 0 ≤ c - b,
  linarith,
  have f2 : 0 ≤ (c - b) * a,
  exact mul_nonneg f1 hanonneg,
  have f3 : 0 ≤ c * a - b * a,
  linarith,
  have f4 : b * a ≤ c * a,
  linarith,
  tauto,
end

lemma add_le_add_right {a b c d : ℝ} (h1 : b ≤ c) (h2 : a ≤ d) : a + b ≤ c + d := 
begin
  linarith,
end

lemma add_le_add_left {a b c : ℝ} (h : b ≤ c) : a + b ≤ a + c := 
begin
  have f1 : 0 ≤ c - b, linarith,
  have f2 : 0 ≤ (a + c) - (a + b), ring,
  exact f1,
  linarith,
end

lemma le_if_mul_le_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : a ≤ b) (hc : 0 ≤ c) : a ≤ b → a * c ≤ b * c :=
begin
  intro h,
  exact mul_le_mul_right1 hc hb,
end

lemma mul_div_mul_self {a b c : ℝ} (ha : 0 < a) (hc : 0 < c) : (b * a) / (c * a) = b / c := 
begin
  have f1 : 0 < a * c,
  exact mul_pos ha hc,
  have f2 : (a * b) / (a * c) = (a / (a * c)) * (b / (a * c)),
  sorry,
  sorry,
end

lemma eps_by_2_div_pos {ε b: ℝ} (he : 0 < ε) (hb : 0 < b) : 0 < ε / (2 * b) :=
begin
  have L : 0 < 2 * b,
  linarith,
  exact div_pos he L,
end

lemma pos_mul_pos_add_pos_mul_pos_le {a b c d e f : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) 
(he : 0 ≤ e) (hf : 0 ≤ f) (hbe : b ≤ e) (hcf : c ≤ f) :
a * b + c * d ≤ a * e + f * d :=
begin
  have L1 : a ≤ a,
  linarith,
  have L2 : a * b ≤ a * e,
  exact mul_le_mul_left1 ha hbe,
  have L3 : d ≤ d,
  linarith,
  have L4 : c * d ≤ f * d,
  exact mul_le_mul_right1 hd hcf,
  linarith,
end

lemma so_obvious {a b c d : ℝ} (hb : 0 < b) (hc : 0 < c) : a * b + c * d < a * b + b + d * c + c :=
begin 
  linarith,
end

lemma pos_mul_pos_add_pos_mul_pos_le2 {a b c d e  : ℝ} (hb : 0 ≤ b) (he : a ≤ e)  :
a * b + c * d ≤ e * b + c * d :=
begin
  have L1 : b ≤ b,
  linarith,
  have L2 : a * b ≤ e * b,
  exact mul_le_mul_right1 hb he,
  linarith,
end

lemma lt_imp_le {a b : ℝ} (h : a < b) : a ≤ b :=
begin
  linarith,
end

end xena -- hide


/- 
set f := ε / (2 * (|R| + 1)) with hfdef,
have hf : 0 < f,
  have G : 0 ≤ |R|,
  
  have J := abs_nonneg R,
  exact J,
  have Z : 0 < 2 * (|R| + 1),
  linarith,
  have S : 0 < (1 / (2 * (|R| + 1))),
  have I := one_div_pos_of_pos Z,
  exact I,
  have V : 0 < ε * (1 / (2 * (|R| + 1))),
  exact mul_pos hε S,
  rw hfdef,
  have W : ε * (1 / (2 * (|R| + 1))) = ε / (2 * (|R| + 1)),
  ring,
  rw W at V,
  exact V,
  have hε2R : 0<(ε/(2*(|R|+1))),
  rw hfdef at hf,
  exact hf,
  have P1 := ha (ε/(2*(|R|+1))) hε2R, 
  cases P1 with N1 hN1,

  set e := ε / (2 * (M + 1)) with hedef,
  have he : 0 < e,
  have O : 0 ≤ M,
  have J := abs_nonneg (a 1),
  exact le_trans J O,
  have B : 0 < 2 * (M + 1),
  linarith,
  have C : 0 < (1 / (2 * (M + 1))),
  have I := one_div_pos_of_pos B,
  exact I,
  have V : 0 < ε * (1 / (2 * (M + 1))),
  exact mul_pos hε C,
  rw hedef,
  have W : ε * (1 / (2 * (M + 1))) = ε / (2 * (M + 1)),
  ring,
  rw W at V,
  exact V,
  have hε2M : 0<(ε/(2*(M+1))),
  rw hedef at he,
  exact he,
  have P2 := hb (ε/(2*(M+1))) hε2M,

  set f := ε / (2 * (M + 1)) with hfdef,
  have hf : 0 < f,
  have G : 0 ≤ M,
  have K := hM 1,
  have J := abs_nonneg (a 1),
  exact le_trans J K,
  have Z : 0 < 2 * (M + 1),
  linarith,
  have S : 0 < (1 / (2 * (M + 1))),
  have I := one_div_pos_of_pos Z,
  exact I,
  have V : 0 < ε * (1 / (2 * (M + 1))),
  exact mul_pos hε S,
  rw hfdef,
  have W : ε * (1 / (2 * (M + 1))) = ε / (2 * (M + 1)),
  ring,
  rw W at V,
  exact V,
  have hε2M : 0<(ε/(2*(M+1))),
  rw hfdef at hf,
  exact hf,
  have P1 := ha (ε/(2*(M+1))) hε2M, 
  cases P1 with N1 hN1,

  set e := ε / (2 * (|R| + 1)) with hedef,
  have he : 0 < e,
  have O : 0 ≤ |R|,
  have J := abs_nonneg R,
  exact J,
  have B : 0 < 2 * (|R| + 1),
  linarith,
  have C : 0 < (1 / (2 * (|R| + 1))),
  have I := one_div_pos_of_pos B,
  exact I,
  have V : 0 < ε * (1 / (2 * (|R| + 1))),
  exact mul_pos hε C,
  rw hedef,
  have W : ε * (1 / (2 * (|R| + 1))) = ε / (2 * (|R| + 1)),
  ring,
  rw W at V,
  exact V,
  have hε2R : 0<(ε/(2*(|R|+1))),
  rw hedef at he,
  exact he,
  have P2 := hb (ε/(2*(|R|+1))) hε2R,
-/