import game.limits.bounded_if_convergent -- hide
import game.limits.Blockus_time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import data.real.basic -- hide
import tactic.linarith -- hide

namespace xena -- hide

/-
# Chapter 7 : Limits

## Level 2

These next two proofs will be used in proving some proofs in a few levels and make those 
proofs much easier to solve.

In this proof you will be showing that if you have a positive real number a, and two other
real numbers b and c, that if b ≤ c then a * b ≤ a * c. 

-/


lemma mul_le_mul_left1 {a b c : ℝ} (h1 : 0 ≤ a) (h2 : b ≤ c) : a * b ≤ a * c := 
begin 
have f1 : 0 ≤ c -b, linarith, 
have f2 : 0 ≤ a * (c-b), exact mul_nonneg h1 f1,
have f3 : 0 ≤ a * c - a * b, linarith, 
linarith, 
end 

end xena -- hide