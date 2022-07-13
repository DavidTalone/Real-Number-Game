import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import game.limits.bounded_if_convergent
import data.real.basic
import tactic.linarith
import game.limits.seq_limitProd
import game.limits.Lemmas

namespace xena -- hide



local notation `|`x`|` := abs x

lemma lim_recip (b : ℕ → ℝ) (k : ℝ) (hk : k ≠ 0) (hb : is_limit b k) (hbnz : ∀ n : ℕ, b n ≠ 0) : 
is_limit (λn , 1 / b n) (1 / k) :=
begin 

  apply lim_le_iff_lim_lt.mpr,
  
  intro ε,
  intro hε, 

  unfold_coes, 
  have R := lim_nz_ev_bd_away_from_zero, 
  have D := R b _ _, 
  unfold ev_bd_away_from_zero at D, 
  cases D with c hc, cases hc with y hy, 
  cases hy with N1 hN1, 

  ------
  swap, exact k, swap, exact hk, swap, exact hb, 
  -----
  unfold is_limit at hb, 
  have H1 := hb(c * |k| * ε), 
  have duh4 := abs_pos_of_ne_zero hk,
  have H2 : 0 < (c * |k|), exact mul_pos y duh4, 
  have H3 : 0 < (c * |k| * ε), exact mul_pos H2 hε, 
  specialize H1 H3, cases H1 with N2 hN2,  
  use max N1 N2, 

  intros n hn,
  rw max_le_iff at hn,
  cases hn with hn1 hn2, 
  have L : | 1 / b n - 1 / k | = | (k - b n) / ( b n * k) |, 
  have L1 := hbnz n, revert hk, revert L1, exact stuff1 _ _, 

  rw L, 
  have L2 : | (k - b n) / ( b n * k) | = 1 / (|b n| * |k|) * |b n - k|, have L1 := hbnz n,
  revert hk, revert L1, exact stuff2 _ _,  
  rw L2, 

  have L1 := hbnz n,
  have L3 := hN1 n hn1,  
  have duh : | b n | ≠ 0, linarith, 
  have duh2 : c ≠ 0, linarith, 

  have L4 : 1 / |b n| ≤ 1 / c, exact stuff3 duh duh2 y L3, 
  have duh3 := abs_nonneg (b n - k), 
  have duh4 := abs_pos_of_ne_zero hk, 
  have duh5 := abs_nonneg (k), 



     
  have L5 : c * |k| ≤ |b n| * |k|, exact mul_le_mul_right1 duh5 L3, 
  have L505 : 0 < |b n|, linarith, 
  have L5051 : |k| ≠ 0, linarith, 
  have L51 : 0 < c * |k|, exact mul_pos y duh4, 
  have FuckYou : 0 < (1 : ℝ), linarith, 
  have L511 : 0 < 1 / (c * |k|), exact div_pos (FuckYou) (L51), 
  have L512 : 0 ≤ 1 / (c * |k|), exact lt_imp_le L511,   
  have L52 : 0 < |b n| * |k|, exact mul_pos L505 duh4,  
  have L6 : 1 / (|b n| * |k|) ≤ 1 / (c * |k|), exact stuff4 duh duh2 L5051 L3,      
  have L7 : (1 / (|b n| * |k|)) * |b n - k| ≤ (1 / (c * |k|)) * |b n - k|, exact mul_le_mul_right1 duh3 L6,
    
  have duh6 : |b n - k| < (c * |k| * ε), have H4 := hN2(n), specialize H4 hn2, exact H4, 
  

  have W : 0 < 1 / (c * |k|), linarith, 
  have H6 : (1 / (c * |k|)) * |b n - k| < (1 / (c * |k|)) * (c * |k| * ε), 
  exact stuff5 L511 duh3 H3 duh6,      
     
  have L65 : (c * |k|) ≠ 0, linarith, 
  have H7 : 1 / (c * |k|) * (c * |k| * ε) = ε, exact soul_sucking_deep_sadness hε L65, 
  rw H7 at H6,

  have H8 := bs_lemma L505 y duh4 duh3 hε duh L5051 duh2 L3 _, 
  swap, have H9 : 1 / (c * |k|) * |b n - k| ≤ ε, exact lt_imp_le H6, exact H9, 
  exact H8,

end 

end xena 