import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith



definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε

def seq (n : ℕ) (a : ℕ → ℝ) := a n

def limit (n : ℕ) (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N : ℕ, n ≥ N → |a n - L | < ε

definition is_limit' (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| ≤ ε
