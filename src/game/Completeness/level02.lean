import game.Completeness.level01
import tactic

/-
# Chapter 6 : Completeness

## Level 2 

The supremum, call it x, of a set A is the least upper bound of A. 
In lean, we define the supremum as an upper bound of A 
and that ∀ y, if y is an upper bound of A, then x ≤ y. 


Prove that for all numbers in a set bounded above, 
there exists a number between any number and the supremum. 

-/

def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

example {A : set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro h,
  contrapose!,
  exact hx.right h,

end
