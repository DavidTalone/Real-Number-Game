import data.real.basic

import tactic.suggest

import game.Completeness.level01

noncomputable theory
open_locale classical


lemma inf_lt {A : set ℝ} {x : ℝ} (hx : x is_an_inf_of A) :
  ∀ y, x < y → ∃ a ∈ A, a < y :=
begin
  -- Let `y` be any real number.
  intro y,
  -- Let's prove the contrapositive
  contrapose,
  -- The symbol `¬` means negation. Let's ask Lean to rewrite the goal without negation,
  -- pushing negation through quantifiers and inequalities
  push_neg,
  -- Let's assume the premise, calling the assumption `h`
  intro h,
  -- `h` is exactly saying `y` is a lower bound of `A` so the second part of
  -- the infimum assumption `hx` applied to `y` and `h` is exactly what we want.
  exact hx.2 y h
end


