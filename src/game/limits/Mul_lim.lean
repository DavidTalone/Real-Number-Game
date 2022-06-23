import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import game.limits.bounded_if_convergent
import data.real.basic
import tactic.linarith


namespace xena -- hide

local notation `|`x`|` := abs x



lemma lim_prod (a : ℕ → ℝ) (b : ℕ → ℝ) (L  R  : ℝ)
    (ha : is_limit a L) (hb : is_limit b R ) : 
    is_limit ( λ n, (a n) * (b n) ) (L * R) :=
begin
  intro ε,
  intro j,
  have P := bounded_if_convergent,
  unfold is_bounded at P,
  unfold is_bound at P,
  unfold is_convergent at P,
  
  --have R : ∃c : ℝ
  have Q : ∃α : ℝ, is_limit a α := exists.intro L ha,
  have T := P a Q,
  cases T with d hd,
  set e := ε / (2 * (|R| + 1)) with hedef,
  set f := ε / (2 * (d + 1)) with hfdef,
  have hf : 0 < f,
  have G : 0 ≤ d,
  have K := hd 1,
  have J := abs_nonneg (a 1),
  exact le_trans J K,
  have Z : 0 < 2 * (d + 1),
  linarith,
  have S : 0 < (1 / (2 * (d + 1))),
  have I := one_div_pos_of_pos Z,
  exact I,
  have V : 0 < ε * (1 / (2 * (d + 1))),
  exact mul_pos j S,
  rw hfdef,
  have W : ε * (1 / (2 * (d + 1))) = ε / (2 * (d + 1)),
  ring,
  rw W at V,
  exact V,
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
  exact mul_pos j C,
  rw hedef,
  have W : ε * (1 / (2 * (|R| + 1))) = ε / (2 * (|R| + 1)),
  ring,
  rw W at V,
  exact V,
  have Ha := ha e he,
  have Hb := hb f hf,
  cases Ha with N1 hy,
  cases Hb with N2 ht,
  let N := max N1 N2,
  use N,
  intros n hn,
  unfold,
  have D : a n * b n - L * R = a n * b n - a n * R + a n * R - L * R,
  ring,
  rw D,
  have V : a n * b n - a n * R + a n * R - L * R = a n * (b n - R) + (a n - L) * R,
  ring,
  rw V,
  have A : |a n * (b n - R) + R * (a n - L)| ≤ |a n * (b n - R)| + |R * (a n - L)|,
  exact abs_add _ _,
  have C : |a n * (b n - R)| + |R * (a n - L)| ≤ |a n| * |b n - R| + |R| * |a n - L|,
  rw abs_mul _ _, rw abs_mul _ _,
  --have E : |a n| * |b n - R| + |R| * |a n - L| < |a n| * f + |R| * e,
  --rw hedef, rw hfdef,
  have B : (|R| * ε) / (2 * (|R| + 1)) < (|R| * ε) / (2 * (|R| + 1)) + (ε / (2 * (|R| + 1))),
  have G : (|R| * ε) / (2 * (|R| + 1)) = |R| * e,
  rw hedef,
  ring,
  rw G,
  rw ← hedef,
  linarith,
  have R : (|R| * ε) / (2 * (|R| + 1)) + (ε / (2 * (|R| + 1))) = ((|R| + 1) * ε) / (2 * (|R| + 1)),
  have G : (|R| * ε) / (2 * (|R| + 1)) = |R| * e,
  rw hedef,
  ring,
  rw G,
  rw ← hedef,
  rw right_distrib,
  rw hedef,
  rw left_distrib,
  
  tidy,
  ring,
  
  have Y : ((|R| + 1) * ε) / (2 * (|R| + 1)) = ε / 2,
  have K : (ε * (|R| + 1)) / (2 * (|R| + 1)) = ε / 2,
  set v := |R| + 1,
  have D : ε * v / (2 * v) = ε / (2 * v) * v, 
  ring,
  rw D,
  clear P A C V,
  
  sorry,
  sorry,
  sorry,
  
  
  

end

/-
set e := ε / (2)  with hedef,
  have he : 0 < e,
  linarith,
  have Ha := ha e he,
  have Hb := hb e he,
  cases Ha with d hd,
  cases Hb with t ht,
-/



end xena -- hide