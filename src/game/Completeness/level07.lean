import data.real.basic
import game.Completeness.level04
import game.Completeness.level02


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



example  (S : set ℝ) (n : ℕ) (H : S = {3 - 1 / n}) : is_sup S 3 :=
begin
  rw is_sup,
  split,
  intro h,
  intro j,
  rw H at j,

  cases n with n hn,
  simp at H,
  simp at j,
  rw j,
  rw nat.succ_eq_add_one at H,
  rw nat.succ_eq_add_one at j,
  --simp at j,
  --rw j,
  --revert j,
  --contrapose!,
  --intro j,
  --intro f,
  have L := inv_succ_pos,
  rw self
  have P : 3 - 1 / ↑(n + 1) > 0,
  sorry,
  
  sorry,
  
  intro h,
  intro j,
  rw upper_bound at j,
  apply j,
  rw H at j,
  rw H,
  cases n with d hd,
  norm_num,
  sorry,
  
  --return at later date (preferably never)
end




/-
rw upper_bound,
  intro j,
  intro k,
  rw H at k,
  cases k with k hk,
  cases k with d hd,




  
-/