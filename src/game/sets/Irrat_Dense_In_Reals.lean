import data.real.basic
import tactic
import algebra.ring
import game.sets.sets_level10
import game.sets.sqrt2NotRational
import data.real.irrational


def embedded_irrationals : set ℝ := { x : ℝ | ¬ ∃ r : ℚ, x = (r : ℝ) }
def Irr : set ℝ := {x | ∀ r : ℚ, x ≠ ↑r}

lemma sqrt2_irrational : real.sqrt 2 ∈ Irr :=
begin
  intro h,
  intro j,
  --unfold real.sqrt at j,
  have Y := rational_not_sqrt_two,
  push_neg at Y,
  have I : (real.sqrt 2) ^ 2 = 2, simp,
  specialize Y (↑h),
  rw j at I,
  norm_cast at *,
end

lemma rat_minus_rat_eq_rat {a b: ℚ} : ∃c : ℚ, a - b = c :=
begin
  
end

lemma any_plus_irr_eq_irr {b : Irr} {a : ℚ}  : ((a : ℝ) + (b : ℝ)) ∈ Irr :=
begin
  intro j,
  intro k,
  have P : (b : ℝ) = (j : ℝ) - (a : ℝ),
  linarith, 
  
  
end


theorem irrat_dense_in_R : dense_in_R embedded_irrationals :=
begin
  intros h j k,
  have x : 0 < j - h,
  simp,
  exact k,
  have y : 0 < (j - (real.sqrt 2)) - (h - (real.sqrt 2)),
  linarith,
  have p := archimedean_R ((j - real.sqrt 2) - (h - real.sqrt 2)),
  have t := p(y),
  cases t with n hn,
  cases hn with v hv,
  have v1 : 0 < (n : ℝ), simp, exact v,
  have g : 0 < (j - real.sqrt 2 - h + real.sqrt 2 - 1 / (n : ℝ)), linarith,
  have s : 0 < (n : ℝ) * (j - real.sqrt 2 - h + real.sqrt 2 - 1 / (n : ℝ)),
  revert g,
  revert v1,
  exact mul_pos,

  have F := has_ceiling ((n : ℝ) * (j - real.sqrt 2 - h + real.sqrt 2 - 1 / (n : ℝ))),
  cases F with m hm,
  cases hm with z hz,
  have J : j - real.sqrt 2 - h + real.sqrt 2 - 1 / (n : ℝ) = (j - real.sqrt 2) + (-h + real.sqrt 2)
   + (-1 / (n : ℝ)),
  ring,
  rw J at s,
  have P : (j - real.sqrt 2 + (-h + real.sqrt 2)) = ((j - real.sqrt 2) + (-h + real.sqrt 2)),
  linarith,
  
  rw P at s,
  rw add_assoc at s,
  rw left_distrib at s,
  rw left_distrib at s,
  field_simp at s,
  have L : - (n : ℝ) / (n : ℝ) = -1,
  ring,
  rw inv_mul_cancel,
  linarith,
  rw L at s,
  rw left_distrib at s,
  have I : j - real.sqrt 2 = j + (- real.sqrt 2),
  linarith,
  rw I at s,
  rw left_distrib at s,

  have D := has_ceiling (↑n * h - ↑n * real.sqrt 2),
  cases D with r hr,
  cases hr with b hb,
  have U : ↑r ≤ ↑n * h - ↑n * real.sqrt 2 + 1,
  linarith,
  use ((↑r / ↑n) + real.sqrt 2 : ℝ),
  split,
  unfold embedded_irrationals,
  push_neg,
  simp,
  intro e,
  have B := sqrt2_irrational,
  
  use ((↑r / ↑n) + real.sqrt 2 : ℝ),
  unfold set.Ioo,
  split,
  have duh2 : ↑n * (h - real.sqrt 2) = ↑n * h - ↑n * real.sqrt 2, linarith,
  have Y : (↑n * (h - real.sqrt 2)) * (1 / ↑n) < ↑r * (1 / ↑n),
  rw duh2,
  finish,

  rw mul_assoc at Y,
  rw mul_comm ↑n _ at Y,
  rw mul_assoc at Y,
  rw inv_prod_self at Y,
  swap,
  exact v,
  rw mul_one at Y,
  field_simp at Y,
  linarith,

  have HP : ↑r < (j - real.sqrt 2) * ↑n,
  linarith,
  have P : ↑r * (1 / ↑n) < ((j - real.sqrt 2) * ↑n) * (1 / ↑n),
  finish,

  rw mul_assoc at P,
  rw mul_comm ↑n _ at P,
  rw inv_prod_self at P,
  swap,
  exact v,
  rw mul_one at P,
  field_simp at P,
  linarith,
  
  
end