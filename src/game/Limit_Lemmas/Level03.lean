import game.limits.bounded_if_convergent -- hide
import game.limits.Blockus_time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import data.real.basic -- hide
import tactic.linarith -- hide

namespace xena -- hide

/-
# Chapter 7 : Limits

## Level 4

The following three proofs should prove to be very useful in the level where you prove lim_mul.

This proof is very specific to that proof but the idea should be obvious in a general case.
The proof basically says that if you have a positive real number ε and divide it by
a positive real number, then the quotient is also positive. In this particular example,
the second positive real number is b which is multiplied by two for proving lim_mul.

-/


lemma eps_by_2_div_pos {b ε : ℝ} (hε : 0 < ε) (hb :0 < b) : 0 < ε / (2 * b) :=
begin 
    have f1 : 0 < 2 * b, linarith, 
    exact div_pos hε f1,  

end 

end xena -- hide