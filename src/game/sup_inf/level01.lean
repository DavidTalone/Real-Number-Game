import game.order.level09
import data.real.basic -- imports the real numbers ℝ

namespace xena -- hide

-- World name : Sup and Inf

/-
# Chapter 3 : Sup and Inf

## Level 1 : Upper bounds
-/

/-
Let $X$ be a set of real numbers.

We say a real number $b$ is an *upper bound* for $X$ if every $x \in X$ is at most $b$.
-/

definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 

/-
Here is an easy fact about upper bounds, which we shall prove below: 
If $X \subseteq Y$ are two sets of reals, and $b$ is an upper bound for $Y$, 
then it's also an upper bound for $X$.

You can prove this easily in Lean using the `change` tactic. 
-/

/- Lemma
If $X \subseteq Y$ are two sets of reals, and $b$ is an upper bound for $Y$, 
then it's also an upper bound for $X$.
-/
lemma upper_bounds_mono (X Y : set ℝ) (h1 : X ⊆ Y) (b : ℝ) : is_upper_bound Y b → is_upper_bound X b :=
begin
  intro h,
  intro j,
  intro k,
  apply h,
  change ∀j, j ∈ X → j ∈ Y at h1,
  apply h1,
  exact k,
end

end xena -- hide

