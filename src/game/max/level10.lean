import game.max.level09 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter 4 : Max

## Level 10

And finally `lt_max_iff`. 
-/

/- Lemma
If $a$, $b$, $c$ are real numbers,
then $a<\max(b,c)$ iff ($a<b$ or $a<c$).
-/

theorem lt_max_iff {a b c : ℝ} : a < max b c ↔ a < b ∨ a < c :=
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
  apply lt_of_lt_of_le d,
  apply le_max_left,
  apply lt_of_lt_of_le hd,
  apply le_max_right,
end

end xena --hide
