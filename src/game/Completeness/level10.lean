import game.sup_inf.level01
import game.sup_inf.level02
import data.real.basic
import game.limits.Blockus_Time
import game.Completeness.Bruh2
import game.Completeness.level09
import tactic

namespace xena -- hide

theorem mono_incr_seq_sup {a : ℕ → ℝ} {S : set.range a} {x : ℝ} (ha : ∀ (n : ℕ), a n ≤ a (n + 1)) (h2 : is_lub (set.range a) x) : is_limit a x := 
begin 
rw is_limit, 
intro ε, intro hε,



unfold_coes at S,
simp at S,
cases S with d hd,
cases hd with n₀ hn,

have Q := generate_element h2 (ε),
specialize Q hε,
unfold is_upper_bound at Q,
push_neg at Q,
cases Q with v hv,
cases hv with t ht,
unfold set.range at t,
cases t with N hN,
use N,
intro n,
intro j,
have U : a N ≤ x,
unfold is_lub at h2,
cases h2 with e he,
rw is_upper_bound at e,
specialize e (a N),

have Q : a N ∈ set.range a, by simp, 
specialize e Q, exact e,

have R : a N < x + ε,
linarith,
rw ← hN at ht,

have J : x - ε < a N ∧ a N < x + ε,
split,
exact ht, exact R,
have I : |a n - x| = |x - a n|,
rw abs_eq_abs_neg,
simp,
have B : a N ≤ a n, exact thing4 ha j,
have duh1 : 0 ≤ x - a N, linarith,
have duh3 : -a n ≤ - a N, linarith,
have duh4 : x - a n ≤ x - a N, linarith,
have duh5 : |x - a n| = x - a n,
unfold abs,
simp,
unfold is_lub at h2,
cases h2 with batman robin,
unfold is_upper_bound at batman,
apply batman,
simp,
have V : |x - a n| ≤ x - a N, linarith,
rw I, rw duh5, linarith, simp,

end 






end xena -- hide
