import game.sup_inf.level03
import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 4 
-/

/-
A generalization of the result in the previous level.
-/

-- begin hide
-- these three helper results to go in sidebar
lemma two_real_ne_zero : (2:ℝ) ≠ 0 :=
begin
    intro, linarith,
end

lemma avg_lt_max {mn mx: ℝ} (H : mn < mx) : (mn+mx) / 2 < mx :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_real_ne_zero)],
  simp [H,mul_two],
end

lemma min_lt_avg {mn mx: ℝ} (H : mn < mx) : mn < (mn+mx) / 2 :=
begin
  apply (mul_lt_mul_right (show (0:ℝ)<2, by norm_num)).1,
  rw [div_mul_cancel _ (two_real_ne_zero)],
  simp [H,mul_two],
end
-- end hide

/- Lemma
A more general version of the previous level...
-/
lemma lub_open (y : ℝ) : is_lub {x : ℝ | x < y} y :=
begin
  split,
  intro h,
  intro j,
  exact le_of_lt j,
  intro h,
  intro j,
  refine le_of_not_gt _,
  intro k,
  let c := (h+y)/2,
  have H2 := j c,
  have H : c ∈ {x : ℝ  | x < y},
  exact avg_lt_max k,
  have G := H2 H,
  have P : h < c := min_lt_avg k,
  exact not_lt.2 G P,
end

end xena -- hide

