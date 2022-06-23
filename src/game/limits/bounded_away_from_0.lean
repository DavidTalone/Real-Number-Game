import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import game.limits.bounded_if_convergent
import game.limits.Lemmas
import data.real.basic
import tactic.linarith

namespace xena

local notation `|`x`|` := abs x

def ev_bdd_away_zero (a : ℕ → ℝ)  := ∃c : ℝ, (0 < c) ∧ (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (c ≤ |a n|))

lemma lim_nz_ev_bdd_away_zero (b : ℕ → ℝ) {k : ℝ} (hk : k ≠ 0) : is_limit b k → ev_bdd_away_zero b :=
begin
  intro j,
  unfold ev_bdd_away_zero,

  unfold is_limit at j,
  use |k| / 2,
  split,
  have T := abs_pos_of_ne_zero hk,
  linarith,
  
  use 0,
  intro n,
  intro y,
  have Y : |b n| - |k| ≤ |b n - k|,
  exact abs_sub_abs_le_abs_sub _ _,
  have R : 0 ≤ |b n - k|,
  exact abs_nonneg _,
  have P : | |b n| - |k| | < |k| / 2,
  

  have O : |k| - |k| / 2 < |b n|,
  
  

  /-
  intro p,
  have Q := j(|k| / 2) p,
  cases Q with n hd,
  use n,
  intro n,
  intro y,
  have M := hd(n) y,
  have L : | |b n| - |k| | ≤ |b n - k|,
  exact abs_abs_sub_abs_le_abs_sub _ _,
  have P : | |b n| - |k| | < |k| / 2,
  linarith,
  rw abs_lt at P,
  cases P with d hd,
  have O : |k| - |k| / 2 < |b n|,
  linarith,
  have R : |k| - |k| / 2 = |k| / 2,
  ring,
  rw R at O,
  apply lt_imp_le,
  exact O,
  -/
end


/-
have Y : |b n| - |k| ≤ |b n - k|,
  exact abs_sub_abs_le_abs_sub _ _,
  have R : 0 ≤ |b n - k|,
  exact abs_nonneg _,
  --rw abs_abs_sub_abs_le_abs_sub
  norm_num,
  have O : |b n| ≤ |b n - k| + |k|,
  linarith,
  have U : |k| ≤ |b n - k| + |k| + |b n - k| → |k| ≤ |b n| + |b n - k|,
  intro B,
-/

end xena -- hide