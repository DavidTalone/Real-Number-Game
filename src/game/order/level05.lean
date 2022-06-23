import game.order.level04
import game.order.H

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 5

Another well-known property of the absolute value.
-/

notation `|` x `|` := abs x -- hide


/-
Hint: negate abs_le_if_pos_neg_le
-/

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$| |a| - |b| | ≤ |a - b|$$.
-/
theorem abs_of_sub_le_abs (a b : ℝ) : | |a| - |b| | ≤ |a - b| :=
begin
    have h1 : a = (a - b) + b,
    norm_num,
    have h2 : | a | = | (a - b) + b |,
    norm_num,
    have h3 : | (a - b) + b | ≤ |a - b| + |b|,
    exact abs_add _ _,
    rw ← h2 at h3,
    have h4 : | a | - | b | ≤ | a - b |,
    linarith,
    have k1 : b = (b - a) + a,
    norm_num,
    have k2 : | b | = | (b - a) + a |,
    norm_num,
    have k3 : | (b - a) + a | ≤ |b - a| + |a|,
    exact abs_add _ _,
    rw ← k2 at k3,
    have k4 : | b | - | a | ≤ | b - a |,
    linarith,
    clear h1 h2 h3 k1 k2 k3,
    have h := eq.symm (abs_neg (a-b)),
    have h2 : -(a - b) = b - a,
    norm_num,
    rw h2 at h,
    rw ← h at k4,
    have H := abs_le_if_pos_neg_le (|a| - |b|) (|a - b|),
    apply H,
    have G := abs_le_if_pos_neg_le(|b| - |a|) (|b - a|),
    norm_num,
    split,
    exact h4,
    exact k4,
end

end xena --hide
