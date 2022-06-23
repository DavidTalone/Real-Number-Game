import game.order.level06
import data.real.irrational

open real

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 7

Prove by example that there exist pairs of real numbers
$a$ and $b$ such that $a \in \mathbb{R} \setminus \mathbb{Q}$, 
$b \in \mathbb{R} \setminus \mathbb{Q}$,
but their sum $a + b$ is a rational number, $(a+b) \in \mathbb{Q}$.
You may use this result in the Lean mathlib library:

`irrational_sqrt_two : irrational (sqrt 2)`

-/

/- Axiom : irrational_sqrt_two : irrational (sqrt 2) 

theorem irrational_neg_iff : irrational (-x) ↔ irrational x 

.2 after irrational_neg_iff gives the left side of the biconditional

existsi in this case brings up 0 to the rational numbers.
-/

/- Lemma
Not true that for any $a$, $b$, irrational numbers, the sum is 
also an irrational number.
-/
theorem not_sum_irrational : 
    ¬ ( ∀ (a b : ℝ), irrational a →  irrational b → irrational (a+b) ) :=
begin
  intro h,
  have H := h (sqrt 2) (-sqrt 2),
  have H3 := H irrational_sqrt_two (irrational_neg_iff.2 irrational_sqrt_two),
  apply H3,
  existsi (0 : ℚ),
  simp,
end

end xena -- hide

