import game.limits.bounded_if_convergent
import game.limits.Blockus_Time
import game.sets.L01defs
import game.sup_inf.GLBprop_if_LUBprop
import data.real.basic
import tactic.linarith
import game.limits.Lemmas

namespace xena -- hide

local notation `|`x`|` := abs x

/-
I don't even know where to begin with this proof. You're gonna need some luck.
-/

lemma lim_mul2 (a : ℕ → ℝ) (b : ℕ → ℝ) (L  R  : ℝ)
    (ha : is_limit a L) (hb : is_limit b R ) : 
    is_limit ( λ n, (a n) * (b n) ) (L * R) :=
begin
intros ε hε, 
have P :=bounded_if_convergent,
unfold is_bounded at P,
  unfold is_bound at P,
  unfold is_convergent at P,
  have Q : ∃α : ℝ, is_limit a α := exists.intro L ha,
  have T := P a Q,
  cases T with M hM,

  set f := ε / (2 * (|R| + 1)) with hfdef,
  have hf : 0 < f,
  have G : 0 ≤ |R|,
  have J := abs_nonneg R,
  exact J,
  have Z : 0 < (|R| + 1),
  linarith,
  rw hfdef,
  exact eps_by_2_div_pos hε Z,
  have hε2R : 0<(ε/(2*(|R|+1))),
  rw hfdef at hf,
  exact hf,
  
  have P1 := ha (ε/(2*(|R|+1))) hε2R,
  cases P1 with N1 hN1,

  set e := ε / (2 * (M + 1)) with hedef,
  have he : 0 < e,
  have O : 0 ≤ M,
  have K := hM 1,
  have J := abs_nonneg (a 1),
  exact le_trans J K,
  have B : 0 < (M + 1),
  linarith,
  exact eps_by_2_div_pos hε B,
  have hε2M : 0<(ε/(2*(M+1))),
  rw hedef at he,
  exact he,

  have P2 := hb (ε/(2*(M+1))) hε2M,
  cases P2 with N2 hN2,

  use max N1 N2,
  intros n hn,
  simp,
  rw max_le_iff at hn,
  have F1 : N1 ≤ n := hn.left,
  have F2 : N2 ≤ n := hn.right,
  have F3 := hN1 n F1,
  have F4 := hN2 n F2,

  have duh := abs_nonneg (a n),
  have duh2 := abs_nonneg (R),
  have L42 : |b n - R| ≤ (ε/(2*(M+1))),
  linarith,
  have  L45 : |a n - L| ≤ (ε/(2*(|R|+1))),
  linarith,
  have duh8 : 0 ≤  (ε/(2*(M+1))), rw ← hedef, 
  linarith,
  have duh9 : 0 ≤  (ε/(2*(|R|+1))), rw ← hfdef, 
  linarith,

  have L51 : |a n| ≤ M, 
  have Y := hM(n),
  exact Y,
  
  have L61 : M * (ε/(2*(M+1))) < M * (ε/(2*(M+1))) + (ε/(2*(M+1))),
  rw ← hedef,
  linarith,
  have L62 : M * (ε/(2*(M+1))) + (ε/(2*(M+1))) = ε * (M + 1) / ((2 * (M + 1))),
  ring,
  have L63 : (ε * (M + 1)) / (2 * (M + 1)) = ε / 2,
  have O : 0 ≤ M,
  have K := hM 1,
  have J := abs_nonneg (a 1),
  exact le_trans J K,
  have duh3 : 0 < M + 1,
  linarith,
  have duh4 : 0 < (2 : ℝ),
  linarith,
  exact mul_div_mul_self duh3 duh4,
  
  have L64 : (ε/(2*(|R|+1))) * |R| < |R| * (ε/(2*(|R|+1))) + (ε/(2*(|R|+1))),
  rw ← hfdef,
  linarith,
  have L65 : |R| * (ε/(2*(|R|+1))) + (ε/(2*(|R|+1))) = ε * (|R| + 1) / ((2 * (|R|+ 1))),
  ring,
  have L66 : (ε * (|R| + 1)) / (2 * (|R| + 1)) = ε / 2,
  have J := abs_nonneg R,
  have duh5 : 0 < |R| + 1,
  linarith,
  have duh6 : 0 < (2 : ℝ),
  linarith,
  exact mul_div_mul_self duh5 duh6,

  have L66 : M*(ε/(2*(M+1)))+(ε/(2*(|R|+1)))*|R| < M * (ε/(2*(M+1))) + (ε/(2*(M+1))) + |R| * (ε/(2*(|R|+1))) + (ε/(2*(|R|+1))),
  rw ← hedef,
  rw ← hfdef,
  exact so_obvious he hf,

  have L67 : M * (ε/(2*(M+1))) + (ε/(2*(M+1))) + |R| * (ε/(2*(|R|+1))) + (ε/(2*(|R|+1))) = ε * (M + 1) / ((2 * (M + 1))) + ε * (|R| + 1) / ((2 * (|R|+ 1))),
  ring,

  have L68 : ε * (M + 1) / ((2 * (M + 1))) + ε * (|R| + 1) / ((2 * (|R|+ 1))) = ε / 2 + ε / 2,
  linarith,

  have L69 : M*(ε/(2*(M+1)))+(ε/(2*(|R|+1)))*|R| < ε / 2 + ε / 2,
  linarith,
  
  calc
  |a n * b n - L * R| = |a n * b n - a n * R + a n * R - L * R| : by ring ; rw mul_comm R L
                  ... ≤ |a n*(b n - R)+ (a n - L)* R|  : by ring
                  ... ≤ |a n * (b n - R)| + |(a n - L) * R| : abs_add (a n*(b n - R)) ((a n - L)* R)
                  ... ≤ |a n|*|b n - R|+ |a n - L|*|R| : by rw ← abs_mul ; rw ← abs_mul
                  ... ≤ |a n|*(ε/(2*(M+1)))+(ε/(2*(|R|+1)))*|R| : pos_mul_pos_add_pos_mul_pos_le (duh) (duh2) (duh8) (duh9) (L42) (L45)
                  ... ≤ M*(ε/(2*(M+1)))+(ε/(2*(|R|+1)))*|R| : pos_mul_pos_add_pos_mul_pos_le2 duh8 L51
                  ... < ε/2+ε/2: L69
                  ... = ε : by ring,
  
end

end xena -- hide


