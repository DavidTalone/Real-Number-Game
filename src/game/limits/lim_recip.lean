import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import game.limits.bounded_if_convergent
import game.limits.bounded_away_from_0
import data.real.basic
import tactic.linarith


namespace xena -- hide

local notation `|`x`|` := abs x

lemma lim_recip (b : ℕ → ℝ) (k : ℝ) (hk : k ≠ 0) (hb : is_limit b k) :
is_limit (λ n, 1 / b n) (1 / k) := 
begin
  intros ε hε,
  have P := lim_nz_ev_bdd_away_zero,
  unfold ev_bdd_away_zero,
  unfold ev_bdd_away_zero at P,
  unfold is_limit at P,
  have F := P b hk _,
  cases F with d hd,
  unfold is_limit at hb,
  cases hd with y hy,
  

  /-
  have Q : ∃α : ℝ, is_limit b α := exists.intro k hb,
  have T := P b Q,
  cases T with M hM,
  
  unfold_coes,
  use n,
  have I : ∃ N1 : ℕ, ∃ c > 0,  (N1 ≤ n → c ≤ |b n| ),
  use n,
  -/


  
  
  
  

end

/-
have P := bounded_if_convergent,
  unfold is_bounded at P,
  unfold is_bound at P,
  unfold is_convergent at P,
  have Q : ∃α : ℝ, is_limit b α := exists.intro k ha,
  have T := P b Q,
  cases T with M hM,
  unfold ev_bdd_away_zero,
  have R := lim_nz_ev_bdd_away_zero,
  unfold ev_bdd_away_zero at R,
  use 0,
  intro c,
  intro b,
  unfold is_limit at R,


  have R := lim_nz_ev_bdd_away_zero,
  unfold ev_bdd_away_zero at R,
  have F := R b hk _,
  cases F with d hd,
-/


end xena -- hide