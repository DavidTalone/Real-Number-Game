import data.real.basic
import tactic.suggest 
import game.Completeness.level01
import game.Completeness.level02
import game.Completeness.level03
import game.Completeness.level05
import game.sup_inf.level01
import game.sup_inf.level02
import game.sup_inf.level03
import game.sup_inf.level04
import data.nat.basic
import algebra.order
namespace xena 

noncomputable theory 
open_locale classical  

lemma inv_succ_pos : ∀ n : ℕ, 1/(n+1 : ℝ) > 0 :=
begin
  -- Let `n` be any integer
  intro n,
  -- Since we don't know the name of the relevant lemma, asserting that the inverse of
  -- a positive number is positive, let's state that is suffices
  -- to prove that `n+1`, seen as a real number, is positive, and ask `library_search`
  suffices : (n + 1 : ℝ) > 0,
  { library_search },
  -- Now we want to reduce to a statement about natural numbers, not real numbers
  -- coming from natural numbers.
  norm_cast,
  -- and then get the usual help from `linarith`
  linarith,
end





example (S : set ℝ) (H : S = {r | ∃ v ∈ ℕ, r  = 3 - 1/(v + 1 : ℝ)}) : is_sup S 3 := 
begin 
 rw is_sup, 
 split, rw upper_bound, 
 intros h j, 
 rw le_iff_eq_or_lt, 
 right, rw H at j, 
 cases j with v hv, cases hv with f hf, 
 rw hf,
 refine sub_lt.mp _,
 norm_num,
 tauto, 

 intro h, 
 rw upper_bound,
 cases H with t ht,
 intro j, 
 apply j, tauto, 


end 


end xena