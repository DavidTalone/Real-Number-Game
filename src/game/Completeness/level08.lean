import data.real.basic
import game.Completeness.level04
import game.Completeness.level02


noncomputable theory
open_locale classical

definition has_lub (S : set ℝ) := ∃ x, is_lub S x

--sup(S) - ε < s < sup(S)

lemma thinklater (S : set ℝ) (x y ε : ℝ) (H : has_lub S) (S ≠ ∅) (hy : is_sup S y) : 
  ∀ ε > 0, ∃ x ∈ S, is_sup S y - ε < x ∧ x ≤ is_sup S y :=
begin
  
end
