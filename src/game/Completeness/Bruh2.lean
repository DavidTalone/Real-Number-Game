import data.real.basic
import tactic.suggest 
import game.Completeness.completeness_level01
import game.Completeness.completeness_level02
import game.Completeness.completeness_level03
import game.Completeness.completeness_level06
import game.Completeness.completeness_level07
import game.Completeness.completeness_level08
import game.sup_inf.level01
import game.sup_inf.level02
import game.sup_inf.level03
import game.sup_inf.level04
import game.Completeness.completeness_level10
namespace xena 

noncomputable theory 
open_locale classical  

lemma thing1 {d n : ℕ} (hd : 0 < d) (nd : d ≤ n) : (1 / n : ℝ) ≤ (1 / d : ℝ) := 
begin 

sorry, 

end 



lemma thing2 {d n : ℕ} (hd : 0 < d) (nd : d ≤ n) : (1 / n : ℝ) ≤ (1 / d : ℝ) → (1 / (n + 1) : ℝ) < (1 / d : ℝ) :=
begin
  sorry,
end

lemma thing3 {x : ℝ} {n : ℕ} : x < x + 1 / (n + 1)  := 
begin
sorry, 
end

lemma thing4 {n N : ℕ} {a : ℕ → ℝ} (h : ∀n : ℕ, a n ≤ a (n + 1)) (h2 : N ≤ n) :  a N ≤ a n :=
begin
  intro j,
  induction j with t ht,
  refl,
  sorry,

end

end xena 