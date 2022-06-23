import game.order.level08
import game.order.level02
open real

namespace xena -- hide



lemma abs_fix_iff_nonneg (a : ℝ) : 0 ≤ a ↔ |a| = a :=
begin
  split,
  exact abs_of_nonneg,
  intro h,
  rcases lt_trichotomy a 0 with han | haz | hap,
  swap,
  rw haz,
  rw abs at h,
  rw max_eq_right at h,
  by_contradiction,
  push_neg at a_1,
  have g : a = 0,
  linarith,
  linarith,
  linarith,
  linarith,
end

lemma abs_prod_eq_prod_iff_prod_nonneg (a b : ℝ) : 0 ≤ a * b ↔ abs a * abs b = a * b  :=
begin
  have g2 : |a * b| = |a| * |b|,
  exact abs_mul _ _,
  rw ← g2,
  exact abs_fix_iff_nonneg (a * b),
end

end xena -- hide