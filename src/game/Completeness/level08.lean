import data.real.basic
import game.Completeness.level04
import game.Completeness.level02


noncomputable theory
open_locale classical

definition has_lub (S : set ℝ) := ∃ x, is_lub S x

--sup(S) - ε < s < sup(S)

--lemma thinklater (S : set ℝ) (x y ε : ℝ) (H : has_lub S) (S ≠ ∅) (hy : is_sup S y) : 
  --∀ ε > 0, ∃ x ∈ S, is_sup S y - ε < x ∧ x ≤ is_sup S y :=

lemma do_now {x : ℝ} {S : set ℝ} (h : S ≠ ∅) (Hsup : is_sup S x)  : (∀ ε > 0, ∃ s ∈ S, x-ε<s ∧ s ≤ x) := 
begin
    

    rw is_sup at Hsup, 
    cases Hsup with a ha, 
    rw upper_bound at a,    

    intro ε, intro h, 
    use x, split, swap, 

    split, 
    linarith, linarith,
    

    



     -- rewrite this level cause I am pretty sure it is written incorrectly 
  
end
