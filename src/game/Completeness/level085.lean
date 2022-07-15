import game.sup_inf.level01
import game.sup_inf.level02
import data.real.basic
import game.limits.Blockus_Time
import game.Completeness.Bruh2
import tactic

namespace xena -- hide
/-
# Chapter 7 : Limits

## Level 14


Prove that for a non-empty set S that is bounded above with a supremum (x) 
and for a positive real number epsilon, 
if epsilon is positive, then (x - ε) is not an upperbound of S.  
-/

lemma generate_element {x : ℝ}{S : set ℝ} {h1 : S ≠ ∅} (h2 : is_lub S x) (ε : ℝ) : (0 < ε)→ ¬ (is_upper_bound S (x-ε)) :=
begin
intro h,
unfold is_lub at h2,
cases h2 with h2l h2r,
have Q := h2r(x-ε),
by_contradiction,
have R := Q(h),
linarith,
end   

end xena
