import game.limits.Blockus_Time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import game.limits.bounded_if_convergent -- hide
import data.real.basic -- hide
import tactic.linarith -- hide
import game.limits.seq_limitProd -- hide
import game.limits.lim_recip -- hide
import game.limits.Mulv2 -- hide


namespace xena -- hide
/-
# Chapter 7 : Limits

## Level 13


Prove the quotient property of limits. 

In this proof, you may find that you will have to 
compare equal functions. For this, you will want to use 
"funext", which basically says that if two functions 
have equal parts, then they are equal. 

Good luck. 
-/



local notation `|`x`|` := abs x



lemma lim_quo (a : ℕ → ℝ) (b : ℕ → ℝ) (L  R  : ℝ)
    (ha : is_limit a L) (hb : is_limit b R) (hbnz : ∀ n : ℕ, b n ≠ 0) (hr : R ≠ 0): 
    is_limit ( λ n, (a n) / (b n) ) (L / R) :=
    begin  
        
       have L1 := lim_recip b R hr hb hbnz,
       set c := (λn , 1 / b n),
       have L2 := lim_mul a c L (1/R) ha L1,
       have L3 : L * (1 / R) = L / R, ring, rw L3 at L2, 
       have L4 : (λn , a n * c n) = (λn, a n / b n),
       funext, have F : c n = 1 / b n, refl, 
       rw F, symmetry, exact div_eq_mul_one_div (a n) (b n), 
       rw L4 at L2, exact L2,   
       
    end 

end xena -- hide