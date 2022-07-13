import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import game.limits.bounded_if_convergent
import data.real.basic
import tactic.linarith
import game.limits.seq_limitProd
import game.limits.lim_recip
import game.limits.Mulv2


namespace xena -- hide



local notation `|`x`|` := abs x



lemma lim_quo (a : ℕ → ℝ) (b : ℕ → ℝ) (L  R  : ℝ)
    (ha : is_limit a L) (hb : is_limit b R) (hbnz : ∀ n : ℕ, b n ≠ 0) (hr : R ≠ 0): 
    is_limit ( λ n, (a n) / (b n) ) (L / R) :=
    begin  
        
       have L1 := lim_recip b R hr hb hbnz,
       set c := (λn , 1 / b n),
       have L2 := lim_mul2 a c L (1/R) ha L1,
       have L3 : L * (1 / R) = L / R, ring, rw L3 at L2, 
       have L4 : (λn , a n * c n) = (λn, a n / b n),
       funext, have F : c n = 1 / b n, refl, 
       rw F, symmetry, exact div_eq_mul_one_div (a n) (b n), 
       rw L4 at L2, exact L2,   
       
    end 

end xena -- hide