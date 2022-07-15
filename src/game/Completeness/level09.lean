import game.sup_inf.level01
import game.sup_inf.level02
import data.real.basic
import game.limits.Blockus_Time
import game.Completeness.Bruh2
import game.Completeness.level085
import tactic

namespace xena -- hide

open classical

axiom choice {α : Sort*} : nonempty α → α

/-
# Chapter 7 : Limits

## Level 15

-/


definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε


/- Hide 
Lemma : thing1 
{d n : ℕ} (hd : 0 < d) (nd : d ≤ n) : 1 / n ≤ 1 / d
-/ 

/- Hide
Lemma : thing2 
{d n : ℕ} (hd : 0 < d) (nd : d ≤ n) (nd : 1 / n ≤ 1 / d ) : 1 / (n + 1) < 1 / d 
-/


/-
Prove that there exists a sequence 
that converges to the supremum 
of a upper bounded set such that 
every number in the seqence is in 
the set for all natural numbers. 
-/ 

theorem seq_conv_to_sup {x : ℝ}{S : set ℝ} {h1 : S ≠ ∅} (h2 : is_lub S x): ∃(a : ℕ → ℝ), ((is_limit a x) ∧ (∀(n : ℕ),(a n ∈ S))) := 
begin
-- give them this
have : ∀ n : ℕ, ∃ a ∈ S, x - 1/(n+1) < a,
{ intros n,
  have Q := generate_element h2 (1/(n + 1) : ℝ),
  have R : 0 < (1 / ((n : ℝ) + 1)),
  have Y : 0 < n + 1,
  linarith,
  rw one_div_pos,
  norm_cast,
  exact Y,
  have P : ¬ ∀ a ∈ S, a ≤ x - 1 / (n + 1) := Q R,
  push_neg at P,
  simpa using P,
  exact h1 },
choose a a_in lt_a using this,
use a,
-- to this
/- hint
sorry,
-/
end  

/- Hide
split,
rw is_limit,
intro ε,
intro j,
swap,
intro n,
tauto,
have Y := archimedean_R,
specialize Y ε,
have J := Y(j),
cases J with d hd,
use d,
intro n,
intro v,
cases hd with g hg,

specialize lt_a n,
specialize a_in n,

have R : 1 / (n : ℝ) ≤ 1 / (d : ℝ),
have O := thing1 g v,
exact O,
have P : 0 < n,
linarith,
have T : 1 / ((n : ℝ) + 1) < 1 / (d : ℝ),
have M := thing2 g v,
have I := M(R),
exact I,
have U : a n ≤ x,
unfold is_lub at h2,
cases h2 with e he,
rw is_upper_bound at e,
specialize e (a n),
specialize e a_in,
exact e,
have Q : x < x + 1 / (n + 1),
linarith,
have L : a n - x < 1 / (n + 1),
linarith,
have L2 : - (1 / (↑n + 1)) < a n - x,
linarith,
have L3 : - (1 / (↑n + 1)) < a n - x ∧ a n - x < 1 / (n + 1),
split,
exact L2,
exact L,
have B : |a n - x| < 1 / (n + 1),
rw abs_lt,
exact L3,
have G : |a n - x| < 1 / d,
have K : 1 / ((n : ℝ) + 1) < 1 / (d : ℝ),
linarith,
have G := lt_trans B _, exact G, exact K, linarith,
-/

end xena