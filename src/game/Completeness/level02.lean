import game.Completeness.level01
import tactic

def upper_bound (A : set ℝ) (x : ℝ) := ∀ a ∈ A, a ≤ x
def is_sup (A : set ℝ) (x : ℝ) := upper_bound A x ∧ ∀ y, upper_bound A y → x ≤ y

example {A : set ℝ} {x : ℝ} (hx : is_sup A x) :
∀ y, y < x → ∃ a ∈ A, y < a :=
begin
  intro h,
  contrapose!,
  exact hx.right h,

end
