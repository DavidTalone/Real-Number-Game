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

## Level 8

For this proof you will be proving that in the definition of a limit, |a n - α| < ε if and only
if |a n - α| ≤ ε. 

-/

--definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
  --∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε



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

end xena -- hide