import game.limits.bounded_if_convergent
import game.limits.Blockus_time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import game.limits.Lemmas -- hide
import tactic.linarith

namespace xena -- hide

/-
# Chapter 7 : Limits

## Level 11


As you can tell by the name of this lemma this proof is really annoying because it should be 
so obvious but lean is not aware of it. It shouldn't be that hard to prove but you will likely
use it in lim_recip.
-/



lemma soul_sucking_deep_sadness {ε a : ℝ} (h : 0 < ε) (ha : a ≠ 0): (1 / a) * (a * ε) = ε :=
begin 
simp, rw ← mul_assoc, rw inv_mul_cancel, linarith, exact ha, 
end 



end xena -- hide 