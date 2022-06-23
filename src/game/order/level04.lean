import game.order.level03

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 4

This level invites you to work out a property of the absolute value.
In Lean the absolute value of $x$ is denoted by `abs x`. 
For ease of use, a notation can be used around that definition as below.
Feel free to use the triangle inequality on the real numbers,

`abs_add : ∀ (a b : ?M_1), |a + b| ≤ |a| + |b|`

together with the `linarith` and `norm_num` tactics.
-/

/- Hint : a - b = a + (-b)
-/

notation `|` x `|` := abs x

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$| a - b| ≤ |a| + |b|$$.
-/
theorem abs_sub_le_sum_abs (a b : ℝ) : |a - b| ≤ |a| + |b| :=
begin
    have h : a - b = a + (-b),
    linarith,
    rw h,
    have g := abs_add a (-b),
    have j : abs (-b) = abs b,
    norm_num,
    rw j at g,
    exact g,
end

end xena --hide











/-
have H : a - b = a + (-b), linarith,
    rw H, 
    have G := abs_add a (-b),
    have F : abs (-b) = abs b, norm_num,
    rw F at G, exact G, done
-/