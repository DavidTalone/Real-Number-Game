
import game.limits.bounded_if_convergent
import game.limits.Blockus_time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith




lemma mul_le_mul_left1 {a b c : ℝ} (h1 : 0 ≤ a) (h2 : b ≤ c) : a * b ≤ a * c := 
begin 
have f1 : 0 ≤ c -b, linarith, 
have f2 : 0 ≤ a * (c-b), exact mul_nonneg h1 f1,
have f3 : 0 ≤ a * c - a * b, linarith, 
linarith, 
end 

lemma mul_le_mul_right1 {a b c : ℝ} (h1 : 0 ≤ a) (h2 : b ≤ c) : b * a ≤ c * a := 
begin 
have f1 : 0 ≤ c -b, linarith, 
have f2 : 0 ≤ a * (c-b), exact mul_nonneg h1 f1,
have f3 : 0 ≤ a * c - a * b, linarith, 
linarith, 
end 



lemma add_le_add_right1 {a b c d: ℝ} ( h1 : b ≤ c) (h2 : a ≤ d): b +a ≤ c + d :=
begin 
linarith, 
end

lemma le_if_mul_le_mul {a b c : ℝ} (h1 : 0 ≤ a) (h2 : a ≤ b) (h3 : 0 ≤ c) : a ≤ b → a * c ≤ b * c :=
begin 
    intro h, 
    exact mul_le_mul_right1 h3 h2, 
    
    
end 

lemma div_div_self1 {a b : ℝ} (h1 : 0 < a) (h2 : 0 < b) : a / (a / b) = b :=
begin
  ring_nf,
  rw inv_mul',
  rw inv_inv,
  ring_nf,
  sorry,
end

lemma mul_div_mul_self {a b c : ℝ} (h1 : 0 < a) (h2 : 0 < c) :  (b * a) / (c * a) = b/ c := 
begin
  sorry,
  /-
  have f1 : 0 < c * a, exact mul_pos h2 h1,
  rw div_mul_eq_div_div_swap,
  have P := div_div_self' _ _,
  -/
  
  
   

end



lemma eps_by_2_div_pos {b ε : ℝ} (hε : 0 < ε) (hb :0 < b) : 0 < ε / (2 * b) :=
begin 
    have f1 : 0 < 2 * b, linarith, 
    exact div_pos hε f1,  

end 


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

lemma pos_mul_pos_add_pos_mul_pos_le2 {a b c d e: ℝ} (hb : 0 ≤ b) 
  (hae: a ≤ e): a * b + c * d ≤ e * b + c * d :=
begin
have L1 : b ≤ b, linarith, 
have L2 : a * b ≤ e * b, 
exact mul_le_mul_right1 hb hae,  
linarith, 

end 


definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε



definition is_limit' (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| ≤ ε 

lemma lim_le_iff_lim_lt {L : ℝ}{a : ℕ → ℝ} : ((is_limit a L) ↔ (is_limit' a L)):=
begin
split,
intros h ε hε,
have Q := h(ε)(hε),
cases Q with N hN,
use N,
intros n hn,
have R := hN(n)(hn),
linarith,
intros h ε hε,
have hε' : 0 < (ε / 2), by linarith, 
have S := h(ε/2)(hε'),
cases S with N hN,
use N,
intros n hn,
have T := hN(n)(hn),
linarith,
end

lemma so_obvious {a b c d: ℝ} (hb : 0 < b) (hc : 0 < c): a * b + c * d < a * b + b + d * c + c :=
begin 
 linarith, 

end 

 lemma lt_imp_le {a b : ℝ} (h : a < b) : a ≤ b :=
 begin 
linarith, 
 end 


 lemma abs_pos_of_ne_zero {a : ℝ} : a ≠ 0 → 0 < |a| :=
 begin
  intro h,
  rw lt_abs,
  simp,
  simp at h,
  tauto,
 end 

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

 lemma stuff1 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) : | ( 1 /a - 1 / b) | = | (b - a) / (a * b) |:= 
 begin 
 
  sorry,    

 end 

 lemma stuff2 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :  | (b - a) / ( a * b) | = 1 / (|a| * |b|) * |a - b| :=
 begin
  rcases lt_trichotomy a 0 with han | haz | hap,
  swap,
  contradiction,
  rcases lt_trichotomy b 0 with hbn | hbz | hbp,
  swap,
  contradiction,
  ring_nf, rw mul_inv,
  rw mul_assoc, rw mul_comm (b⁻¹) b,
  simp, rw mul_inv_cancel hb,
  
  --rw mul_left_comm a⁻¹ b⁻¹ a,
  rw mul_assoc, rw mul_comm (b⁻¹) a,
  rw ← mul_assoc,
  have Bruh : a⁻¹ * 1 - a⁻¹ * a * b⁻¹ = a⁻¹ * 1 - b⁻¹ * a * a⁻¹,
  ring,
  rw Bruh,
  rw mul_assoc,
  rw mul_inv_cancel ha,
  rw mul_one,
  rw mul_one, 
  sorry,
  sorry,
  sorry,


 end 

 lemma stuff3 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (pb : 0 < b) (c : a ≥ b) : 1 / a ≤ 1 / b := 
 begin 
  sorry,
 end 

lemma stuff4 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ≥ b) : 1 / (a * c) ≤ 1 / (b * c) :=
begin 
  sorry, 
end 

lemma stuff5 {a b c : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hbc : b < c) : 
a * b < a * c := 
begin
  rw mul_lt_mul_left,
  exact hbc,
  exact ha, 
end


lemma mul_le_mul_right_plz1 {a b c : ℝ} (h1 : 0 < a) (h2 : b ≤ c) : b * a ≤ c * a := 
begin 
    have Q : a ≥ 0, exact lt_imp_le h1, 
    have f1 : 0 ≤ c -b, linarith,  
have f2 : 0 ≤ a * (c-b), exact mul_nonneg Q f1,
have f3 : 0 ≤ a * c - a * b, linarith, 
linarith, 

end 

lemma soul_sucking_deep_sadness {ε a : ℝ} (h : 0 < ε) (ha : a ≠ 0): (1 / a) * (a * ε) = ε :=
begin 
simp, rw ← mul_assoc, rw inv_mul_cancel, linarith, exact ha, 
end 


lemma bs_lemma {γ d α β ε : ℝ} (ha : 0 < γ) (hb : 0 < d) (hc : 0 < α)(hd : 0 ≤ β)(he : 0 < ε) (gnz : γ ≠ 0) (anz : α ≠ 0) (dnz : d ≠ 0) (h : d ≤ γ) (h' : (1 / (d * α) * β ≤ ε)) 
: (1 / (γ * α) * β ≤ ε) :=
begin
  have L1 : d * α ≤ γ * α, exact mul_le_mul_right_plz1 hc h, 
  have L2 : 1 / (γ * α) ≤ 1 / (d * α), exact stuff4 gnz dnz anz h, 
  have L2 : (1 / (γ * α)) * β ≤ (1 / (d * α)) * β, exact mul_le_mul_right1 hd L2, 
  linarith, 

end 
