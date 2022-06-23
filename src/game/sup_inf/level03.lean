import game.sup_inf.level02
import data.real.basic

namespace xena -- hide

/-
# Chapter 3 : Sup and Inf

## Level 3
-/

/- 
This level asks you to prove what the supremum of a given open set is.
-/

definition reals_lt_59 := {x : ℝ | x < 59}

-- begin hide
-- The next result must be placed in the sidebar axioms.
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
-- end hide

/- Lemma
The LUB of...
-/
lemma lub_of_open_set : is_lub reals_lt_59 59 := 
begin
  split,
  intro h,
  intro j,
  exact le_of_lt j,

  intro h,
  intro j,
  apply le_of_not_gt,
  intro k,
  let s := (h + 59) / 2,
  have H1 : h < s := (helper_lemma _ _ k).1,
  have H2 : s < 59 := (helper_lemma _ _ k).2,
  unfold is_upper_bound at j,
  have H1' := j s H2,
  exact not_le_of_lt H1 H1',
end 

end xena -- hide







/-
split,
  { intros s Hs,
    exact le_of_lt Hs,
  },
  { intros y Hy,
    apply le_of_not_gt,
    intro H,
    let s := (y + 59) / 2,
    have H1 : y < s := (helper_lemma _ _ H).1,
    have H2 : s < 59 := (helper_lemma _ _ H).2,
--    unfold is_upper_bound at Hy,
    have H1' := Hy s H2,
    exact not_le_of_lt H1 H1', --of_not_gt
  }
-/