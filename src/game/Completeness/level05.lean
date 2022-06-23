import data.real.basic

import tactic.suggest


import game.Completeness.level01

noncomputable theory
open_locale classical

def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

theorem helper_lemma (x y : ℝ) (H : x < y) : x < (x + y) / 2 ∧ (x + y) / 2 < y :=
begin
  have two_ge_zero : (2 : ℝ) ≥ 0 := by norm_num,
  split,
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [mul_two,div_mul_cancel],
    apply add_lt_add_left H,
    norm_num},
  { apply lt_of_mul_lt_mul_right _ two_ge_zero,
    rw [div_mul_cancel,mul_two],
    apply add_lt_add_right H,
    norm_num,
  },
end


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

example (a b : ℝ) (h : a < b): is_sup (set.Ioo a b) b :=
begin
  unfold is_sup,
  split,
  intro t,
  intro j,
  rw set.Ioo at j,
  cases j with d hd,
  exact le_of_lt hd,

  intro t,
  intro j,
  apply le_of_not_gt,
  intro k,
  rcases lt_trichotomy a t with han | haz | hap,
  have L : t + t < b + t, linarith, ring at L,
  have L1 : (t + b) / 2 < b, linarith,
  have P : t + b < b + b, linarith, ring at P,
  have P1 : t < (t + b) / 2, linarith,
  have s : a < (t + b) / 2, linarith,
  
  have avgIn : a < (t + b) / 2 ∧ (t + b) / 2 < b,
  split,
  exact s, exact L1,

  have R : ((t + b) / 2) ∈ set.Ioo a b,
  split,
  exact s,
  exact L1,
  unfold upper_bound at j,
  revert j,
  contrapose!,
  intro q,
  use ((t + b) / 2),
  split,
  exact R,
  exact P1,

  have L : a + a < a + b, linarith, ring at L,
  have L1 : a < (a + b) / 2, linarith,
  have P : a + b < b + b, linarith, ring at P,
  have P1 : (a + b) / 2 < b, linarith,
  have s : a < (a + b) / 2, linarith,
  
  have avgIn : a < (a + b) / 2 ∧ (a + b) / 2 < b,
  split,
  exact s, exact P1,

  have R : ((a + b) / 2) ∈ set.Ioo a b,
  split,
  exact s,
  exact P1,
  

  unfold upper_bound at j,
  revert j,
  contrapose!,
  intro q,
  use ((a + b) / 2),
  split,
  exact R,
  rw ← haz,
  exact s,

  have L : a + a < a + b, linarith, ring at L,
  have L1 : a < (a + b) / 2, linarith,
  have P : a + b < b + b, linarith, ring at P,
  have P1 : (a + b) / 2 < b, linarith,
  have W : t < (a + b) / 2, linarith,

  have R : ((a + b) / 2) ∈ set.Ioo a b,
  split,
  exact L1,
  exact P1,
  unfold upper_bound at j,
  revert j,
  contrapose!,
  intro q,
  use ((a + b) / 2),
  split,
  exact R,
  exact W,
end