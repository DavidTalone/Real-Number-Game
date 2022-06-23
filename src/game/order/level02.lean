import data.real.basic
import game.order.level01

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 2

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
-/

/- Hint : The definition of the absolute value in mathlib:
definition abs {α : Type u} [decidable_linear_ordered_add_comm_group α] (a : α) : α := max a (-a)
-/

/-
For ease of use, a notation can be wrapped around that definition as below.
-/

/- Hint : Cases, Cases, Cases!
-/

notation `|` x `|` := abs x

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|ab| = |a||b|$$.
-/
theorem abs_prod (a b : ℝ) : |a * b| = |a| * |b| :=
begin
    rcases lt_trichotomy a 0 with han | haz | hap,
    swap,
    have h : a * b = 0, norm_num,
    left,
    exact haz,
    rw h,
    rw haz,
    norm_num,
    rcases lt_trichotomy b 0 with hbn | hbz | hbp,
    swap,
    have h : a * b = 0, norm_num,
    right,
    exact hbz,
    rw h,
    rw hbz,
    norm_num,
    have h1 : 0 < a * b, exact mul_pos_of_neg_of_neg han hbn,
    have h2 : | a * b | = a * b, exact abs_of_pos h1,
    have h3 : | a | = - a, exact abs_of_neg han,
    have h4 : | b | = - b, exact abs_of_neg hbn,
    rw h2, rw h3, rw h4,
    norm_num,
    have h1 : a * b < 0, exact mul_neg_of_neg_of_pos han hbp,
    have h2 : | a * b | = - (a * b), exact abs_of_neg h1,
    have h3 : | a | = - a, exact abs_of_neg han,
    have h4 : | b | = b, exact abs_of_pos hbp,
    rw h2, rw h3, rw h4,
    norm_num,
    rcases lt_trichotomy b 0 with hbn | hbz | hbp,
    swap,
    have h : a * b = 0, norm_num,
    right,
    exact hbz,
    rw h,
    rw hbz,
    norm_num,
    have h1 : a * b < 0, exact mul_neg_of_pos_of_neg hap hbn,
    have h2 : | a * b | = - (a * b), exact abs_of_neg h1,
    have h3 : | a | = a, exact abs_of_pos hap,
    have h4 : | b | = - b, exact abs_of_neg hbn,
    rw [h2,h3,h4],
    norm_num,
    have h1 : 0 < a * b, exact mul_pos hap hbp,
    have h2 : | a * b | = a * b, exact abs_of_pos h1,
    have h3 : | a | = a, exact abs_of_pos hap,
    have h4 : | b | = b, exact abs_of_pos hbp,
    rw [h2,h3,h4],
end

end xena --hide

