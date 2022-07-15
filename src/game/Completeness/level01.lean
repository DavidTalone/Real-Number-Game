import data.real.basic

import tactic.suggest

noncomputable theory
open_locale classical

/-
# Chapter 6 : Completeness

## Level 1  


In the Completeness world, youj will be solving proofs regarding 
theroems and properties of bounded sets of reals.  

In Lean, we define the lower bounds of a set A such that 
∀ x : ℝ, | ∀ a ∈ A, x ≤ a. Essentially, for any number x, 
x is less than or equal to any element a in the set A.    

For the upper bounds, we define the upper bounds of a set A such that 
∀ x : ℝ, | ∀ a ∈ A, a ≤ x. Saying that for any number x, 
x is greater than or equal to any element a in the set A. 




For this proof, prove that there is a unique max on a set A of real numbers.
-/


def up_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, a ≤ x}

def is_maximum (a : ℝ) (A : set ℝ) := a ∈ A ∧ a ∈ up_bounds A

infix ` is_a_max_of `:55 := is_maximum

def low_bounds (A : set ℝ) := { x : ℝ | ∀ a ∈ A, x ≤ a}

def is_inf (x : ℝ) (A : set ℝ) := x is_a_max_of (low_bounds A)

infix ` is_an_inf_of `:55 := is_inf

lemma unique_max (A : set ℝ) (x y : ℝ) (hx : x is_a_max_of A) (hy : y is_a_max_of A) : x = y :=
begin
  -- We first break our assumptions in their two constituent pieces.
  -- We are free to choose the name following `with`
  cases hx with x_in x_up,
  cases hy with y_in y_up,
  -- Assumption `x_up` means x isn't less than elements of A, let's apply this to y
  specialize x_up y,
  -- Assumption `x_up` now needs the information that `y` is indeed in `A`.
  specialize x_up y_in,
  -- Let's do this quicker with roles swapped
  specialize y_up x x_in,
  -- We explained to Lean the idea of this proof.
  -- Now we know `x ≤ y` and `y ≤ x`, and Lean shouldn't need more help.
  -- `linarith` proves equalities and inequalities that follow linearly from
  -- the assumption we have.
  linarith,
end


