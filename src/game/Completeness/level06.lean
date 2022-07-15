import data.real.basic
import game.Completeness.level04


noncomputable theory
open_locale classical

/-
# Chapter 6 : Completeness

## Level 6  

Prove that a nonempty and upper bounded 
set has a unique least upper bound. 

-/

definition has_lub (S : set ℝ) := ∃ x, is_lub S x

definition is_upper_bound (S : set ℝ) (x : ℝ) := ∀ s ∈ S, s ≤ x 

definition is_lub_plzwork (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
∀ y : ℝ, is_upper_bound S y → x ≤ y

/-
lemma unique_LUB (A : set ℝ) (x y : ℝ) (H : has_lub A) (hx : is_lub A x) (hy : is_lub A y) : x = y :=
begin
  cases hx with d hd,
  cases hy with f hf,

  specialize hd y,
  specialize hf x,
  specialize hf d,
  specialize hd f,
  linarith,
end
-/

theorem nonempty_and_bounded_has_unique_LUB (x y : ℝ) (S : set ℝ) (H : has_lub S) (hx : is_lub_plzwork S x) (hy : is_lub_plzwork S y) : 
 (S ≠ ∅) ∧ (has_lub S) → x = y :=
begin
  intro h,
  cases h with t ht,
  cases ht with t ht,

  cases hx with d hd,
  cases hy with f hf,

  --specialize hd y,
  specialize hf x,
  specialize hd y,

  specialize hf d,
  specialize hd f,
  linarith,
end

