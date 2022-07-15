import data.real.basic

import tactic.suggest

import game.Completeness.level01

noncomputable theory
open_locale classical

/-
# Chapter 6 : Completeness

## Level 3 

The infimum, call it y, of a set A is the greatest lower bound
of A. In lean, we define the infimum as the maximum of the lwoer bound. 


Prove that for any number in a lower bounded set, 
there exists an element in A such that 
the element will be less than the number. 

Hint: it may help to prove by contrapositive. 
-/

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


