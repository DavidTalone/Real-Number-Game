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

## Level 5

In this proof you will be showing that if you have four non-negative real numbers a d e f,
as well real numbers b and c such that b ≤ e and c ≤ f that a * b + c * d ≤ a * e + f * d.
This should be a pretty obvious fact but lean doesn't seem to think so.

-/

lemma pos_mul_pos_add_pos_mul_pos_le {a b c d e f: ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) 
(he: 0 ≤ e) (hf : 0 ≤ f) (hbe : b ≤ e) (hcf : c ≤ f) : a * b + c * d ≤ a * e + f * d :=
begin
    have L1 : a ≤ a, 
    linarith, 
    have L2 : a *b ≤ a * e, exact mul_le_mul_left1 ha hbe, 

    have L3 : d ≤ d, linarith, 
    have L4 : c * d ≤ f * d, exact mul_le_mul_right1 hd hcf, 
    linarith,   


end 

end xena -- hide