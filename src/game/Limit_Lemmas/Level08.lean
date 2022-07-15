import game.limits.bounded_if_convergent -- hide
import game.limits.Lemmas -- hide
import game.limits.Blockus_time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import data.real.basic -- hide
import tactic.linarith -- hide

namespace xena -- hide

/-
# Chapter 7 : Limits

## Level 10



This lemma will help in dealing with obvious math roadblocks that Lean sometimes 
does not comprehend well. 

Just looking at this equation and all the hypothesis, we know it's true. 
But Lean just needs to know this. 
-/



lemma bs_lemma {γ d α β ε : ℝ} (ha : 0 < γ) (hb : 0 < d) (hc : 0 < α)(hd : 0 ≤ β)(he : 0 < ε) (gnz : γ ≠ 0) (anz : α ≠ 0) (dnz : d ≠ 0) (h : d ≤ γ) (h' : (1 / (d * α) * β ≤ ε)) 
: (1 / (γ * α) * β ≤ ε) :=
begin
  have L1 : d * α ≤ γ * α, exact mul_le_mul_right_plz1 hc h, 
  have L2 : 1 / (γ * α) ≤ 1 / (d * α), exact stuff4 gnz dnz anz h, 
  have L2 : (1 / (γ * α)) * β ≤ (1 / (d * α)) * β, exact mul_le_mul_right1 hd L2, 
  linarith, 

end 

end xena -- hide 