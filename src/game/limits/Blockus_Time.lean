import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith
import game.limits.defs

namespace xena -- hide

local notation `|`x`|` := abs x
/-
# Chapter 7 : Limits

## Level 1

-/

/- 

Using The following definitions you should be able to prove that the limit of a function 
a n 'a(n)' plus the limit of another function b n 'b(n)' is just the limit of
a n + b n. Following the math proof should make this proof very attainable.


definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε

def seq (n : ℕ) (a : ℕ → ℝ) := a n

def limit (n : ℕ) (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N : ℕ, n ≥ N → |a n - L | < ε

definition is_limit' (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| ≤ ε
-/


lemma lim_add (a : ℕ → ℝ) (b : ℕ → ℝ) (α β : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, (a n) + (b n) ) (α + β) :=
begin
  intro ε,
  intro j,
  set e := ε / 2 with hedef,
  have he : 0 < e,
  linarith,
  have Ha := ha e he,
  have Hb := hb e he,
  cases Ha with d hd,
  cases Hb with t ht,
  set m := max d t with hm,
  have q : m ≥ d, norm_num,
  have  r : m ≥ t, norm_num,
  use m,
  intros v hv,
  have I : v ≥ d, linarith,
  have O : v ≥ t, linarith,
  have W := hd v I,
  have X := ht v O,
  have H := abs_add (a v - α) (b v - β),
  simp,
  have G : a v - α + (b v - β) = a v + b v - (α + β), linarith,
  rw G at H,
  have F : |a v - α| + |b v - β| < 2 * e, linarith,
  have E : |a v + b v - (α + β)| < 2 * e, linarith,
  have D : 2 * e = ε, linarith,
  rw D at E,
  exact E,
end
end xena -- hide