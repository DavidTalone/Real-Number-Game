import game.max.level08 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 4 : Max

## Level 9

We've done `max_le_iff`; here is `le_max_iff`. 
-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then $a\leq\max(b,c)$ iff ($a\leq b$ or $a\leq c$).
-/

theorem le_max_iff {a b c : ℝ} : a ≤ max b c ↔ a ≤ b ∨ a ≤ c :=
begin
  split,
  intro h,
  cases le_total b c with hbc hcb,
  rw max_eq_right at h,
  right,
  exact h,
  exact hbc,
  rw max_eq_left at h,
  left,
  exact h,
  exact hcb,
  intro j,
  cases j with d hd,
  apply le_trans d,
  apply le_max_left,
  apply le_trans hd,
  apply le_max_right,

end

end xena --hide
