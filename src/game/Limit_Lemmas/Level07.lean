import game.limits.bounded_if_convergent -- hide
import game.limits.Lemmas -- hide
import game.limits.Blockus_time -- hide
import game.sets.L01defs -- hide
import game.sup_inf.GLBprop_if_LUBprop -- hide
import data.real.basic -- hide
import tactic.linarith -- hide

namespace xena -- hide

/-
# Chapter 8 : Limit Lemmas

## Level 4


-/

definition ev_bd_away_from_zero (b : ℕ → ℝ) :=
 ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |b n| ≥ c  

 lemma lim_nz_ev_bd_away_from_zero (b : ℕ → ℝ) {k : ℝ} (hk: k ≠ 0) : is_limit b k → ev_bd_away_from_zero b :=
 begin
    intro j, 
    unfold ev_bd_away_from_zero, 


    unfold is_limit at j,
    use |k| /2, 
    split, 
    have T := abs_pos_of_ne_zero hk, 
    linarith, 

    have T : 0 < |k|, exact abs_pos_of_ne_zero hk, 
    have T1 : 0 < |k| / 2, linarith,
    have Q := (j(|k|/2))(T1), 
     cases Q with d hd,  
    use d, 
    intro n, 
    intro y,

    have M := hd(n) y, 
    have L : | |b n| - |k| | ≤ |b n - k|, exact abs_abs_sub_abs_le_abs_sub _ _, 

    have P : | |b n| - |k| | < |k| / 2, linarith, 
    rw abs_lt at P, 
    cases P with d hd,
    have O : |k| - |k| / 2 < | b n |, linarith, 
    have R : |k| - |k| / 2 = |k| / 2, ring, rw R at O, 
    apply lt_imp_le, exact O,    
 end  

 end xena -- hide