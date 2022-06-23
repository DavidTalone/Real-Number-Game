import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith

namespace xena -- hide

local notation `|`x`|` := abs x

definition is_limit (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| < ε

def seq (n : ℕ) (a : ℕ → ℝ) := a n

def limit (n : ℕ) (a : ℕ → ℝ) (L : ℝ) := ∀ ε > 0, ∃ N : ℕ, n ≥ N → |a n - L | < ε

definition is_limit' (a : ℕ → ℝ) (α : ℝ) := 
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → |a n - α| ≤ ε

lemma lim_le_iff_lim_lt {L : ℝ}{n : ℕ}(a : ℕ → ℝ) : ((is_limit a L) ↔ (is_limit' a L)):=
begin
split,
intros h ε hε,
have Q := h(ε)(hε),
cases Q with N hN,
use N,
intros n hn,
have R := hN(n)(hn),
linarith,
intros h ε hε,
have hε' : 0 < (ε / 2), by linarith, 
have S := h(ε/2)(hε'),
cases S with N hN,
use N,
intros n hn,
have T := hN(n)(hn),
linarith,
end

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
  have q : m ≥ d, norm_num, left, linarith,
  have  r : m ≥ t, norm_num, right, linarith,
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