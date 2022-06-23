import data.real.basic
import tactic
import algebra.ring

/-
# Chapter 1 : Sets

## Level 10

As a final test of your ability in working with sets, prove that the set of rational 
numbers is dense in the reals.

This proof will, among other things, rely on several new axioms that appear
in the left side bar.
Note that you may need to change the type of some quantities from rationals to reals.
Lean doesn't necessarily consider the rational $2$ to be the same at the real number $2$.
Some of the axioms on the left make working with the casts from rationals to reals easier.
-/

/-
This is a very difficult proof to think out but with a little bit of assistance it does become possible.
One recommendation is doing the proof in math terms first. We will provide the math proof for you
but you will have to make sense of it yourself. If you don't want to see the proof then you should
skip the following paragraph.

(Spoiler)
The mathematical proof goes as follows. 

let r1 and r2 ∈ ℝ s.t. r1 < r2
Then r2 - r1 > 0

By the Archimedean Property ∃ n ∈ ℕ s.t. 1 / n < r2 - r1,
so 1 < nr2 - nr1

Then using has_ceiling we get ∃ m ∈ ℤ s.t. 
nr1 < m < nr2

finally we get that r1 < m / n < r2
(End Spoiler)

Hints:
use inv_prod_self, archimedean_R, has_ceiling, as well as norm_num and possibly norm_cast.
-/


/- Axiom : inv_prod_self : 
∀ n : ℕ, 0 < n → (1/n : ℝ) * (n : ℝ ) = 1 
-/

/- Axiom : inv_prod_other : 
∀ (m : ℤ), ∀ (n : ℕ), 0 < n → (1/n : ℝ) * (m : ℝ) = (m/n : ℝ)
-/

/- Axiom : archimedean_R : ∀ x : ℝ, 0 < x → ∃ n : ℕ, 0 < n ∧ (1/n : ℝ) < x
-/

/- Axiom : has_ceiling : ∀ x : ℝ,  ∃ m : ℤ, ((m-1) : ℝ) ≤ x ∧ x < (m:ℝ)
-/

-- one way to prove ℚ dense in ℝ 
def dense_in_R (A : set ℝ) := ∀ (x y : ℝ), x < y → ∃ a ∈ A, a ∈ set.Ioo x y
def embedded_rationals : set ℝ := { x | ∃ r : ℚ, x = ↑r }
-- begin hide
axiom archimedean_R : ∀ x : ℝ, 0 < x → ∃ n : ℕ, 0 < n ∧ (1/n : ℝ) < x
-- we might want to prove these below. Made into axioms just for ease.
-- the problem is that the proofs are too hard for this level, IMO (DS)
axiom has_ceiling : ∀ x : ℝ,  ∃ m : ℤ, ((m-1) : ℝ) ≤ x ∧ x < (m:ℝ)
axiom inv_prod_self : ∀ n : ℕ, 0 < n → (1/n : ℝ) * (n : ℝ ) = 1 
axiom inv_prod_other : ∀ (m : ℤ), ∀ (n : ℕ), 0 < n → (1/n : ℝ) * (m : ℝ) = (m/n : ℝ)
-- end hide

/- Lemma
Rationals are dense in the reals.
-/
theorem rat_dense_in_R : dense_in_R embedded_rationals := 
begin
  intros h j k,
  have x : 0 < j - h,
  simp,
  exact k,
  have p := archimedean_R (j - h),
  have t := p(x),
  cases t with n hn,
  cases hn with v hv,
  --have V : 1 < ↑n * (j - h),
  have v1 : 0 < (n : ℝ), simp, exact v,
  have g : 0 < (j - h - 1 / (n : ℝ)), linarith,
  have s : 0 < (n : ℝ) * (j - h - 1 / (n : ℝ)),
  revert g,
  revert v1,
  exact mul_pos,

  have F := has_ceiling ((n : ℝ) * (j - h - 1 / (n : ℝ))),
  cases F with m hm,
  cases hm with z hz,
  have J : j - h - 1 / (n : ℝ) = j + (-h) + (-1 / (n : ℝ)),
  ring,
  rw J at s,
  rw add_assoc at s,
  rw left_distrib at s,
  rw left_distrib at s,
  field_simp at s,
  have L : - (n : ℝ) / (n : ℝ) = -1,
  ring,
  rw inv_mul_cancel,
  linarith,
  rw L at s,
  ring at s,
  ring at s,
  simp at s,
  have P : (j - h) = (j + (-h)),
  linarith,
  rw P at s,
  rw right_distrib at s,
  have D := has_ceiling (h * ↑n),
  cases D with r hr,
  cases hr with b hb,
  have U : ↑r ≤ h * ↑n + 1,
  linarith,
  use (↑r / ↑n : ℚ),
  split,
  unfold embedded_rationals,
  use (↑r / ↑n : ℚ),
  unfold set.Ioo,
  split,
  have Y : (h * ↑n) * (1 / ↑n) < ↑r * (1 / ↑n),
  finish,
  rw mul_assoc at Y,
  rw mul_comm ↑n _ at Y,
  rw inv_prod_self at Y,
  swap,
  exact v,
  rw mul_one at Y,
  field_simp at Y,
  norm_num,
  exact Y,
  have HO : ↑r < j * ↑n,
  linarith,
  have O :  ↑r * (1 / ↑n) < (j * ↑n) * (1 / ↑n),
  finish,
  rw mul_assoc at O,
  rw mul_comm ↑n _ at O,
  rw inv_prod_self at O,
  swap,
  exact v,
  rw mul_one at O,
  field_simp at O,
  norm_num,
  exact O,

end















/-
intros x y hxy,
    have H := lt_trichotomy x 0,
    cases H with xL xr, swap, cases xr with x0 xR,
    -- case x = 0
    rw x0 at hxy, 
    have G :=archimedean_R  y hxy,
    cases G with n hn, cases hn with hnL hnR,
    use (1/n), split, existsi (1/n : ℚ), norm_num,
    split, swap, exact hnR, rw x0, norm_num, exact hnL,
    -- case 0 < x
    have H : 0 < y - x, linarith,
    have G := archimedean_R (y-x) H,
    cases G with n hn, cases hn with hnL hnR, 
    have F := has_ceiling (n*x),
    cases F with m hm, cases hm with hmL hmR,
    use (m/n), split, existsi (m/n : ℚ), norm_num,
    have hnL1 : 0 < (n : ℝ), norm_cast, exact hnL, 
    have hnL2 : 0 < (1/n : ℝ), exact one_div_pos_of_pos hnL1,
    split, exact (lt_div_iff' hnL1).mpr hmR,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h2 : (m/n : ℝ) ≤ x + (1/n : ℝ), 
        have h21 := (mul_le_mul_left hnL2).mpr h1, 
        rw mul_add (1/n : ℝ) _ _ at h21, rw mul_one at h21,
        rw ← mul_assoc at h21, 
        have h22 := inv_prod_self n hnL,    --cheating here
        rw h22 at h21, rw one_mul at h21,
        have h23 := inv_prod_other m n hnL, --and here
        rw h23 at h21, exact h21,
    have h3 : x + (1/n : ℝ) < x + (y-x), linarith,
    have h4 : x + (y-x) = y, norm_num, rw h4 at h3,
    linarith, 
    -- case x < 0  -- reduces to the above
     have H : 0 < y - x, linarith,
    have G := archimedean_R (y-x) H,
    cases G with n hn, cases hn with hnL hnR, 
    have F := has_ceiling (n*x),
    cases F with m hm, cases hm with hmL hmR,
    use (m/n), split, existsi (m/n : ℚ), norm_num,
    have hnL1 : 0 < (n : ℝ), norm_cast, exact hnL, 
    have hnL2 : 0 < (1/n : ℝ), exact one_div_pos_of_pos hnL1,
    split, exact (lt_div_iff' hnL1).mpr hmR,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h1 : (m : ℝ) ≤ n*x + 1, linarith,
    have h2 : (m/n : ℝ) ≤ x + (1/n : ℝ), 
        have h21 := (mul_le_mul_left hnL2).mpr h1, 
        rw mul_add (1/n : ℝ) _ _ at h21, rw mul_one at h21,
        rw ← mul_assoc at h21, 
        have h22 := inv_prod_self n hnL,    --cheating here
        rw h22 at h21, rw one_mul at h21,
        have h23 := inv_prod_other m n hnL, --and here
        rw h23 at h21, exact h21,
    have h3 : x + (1/n : ℝ) < x + (y-x), linarith,
    have h4 : x + (y-x) = y, norm_num, rw h4 at h3,
    linarith, done




    intros h j k,
  have x : 0 < j - h,
  simp,
  exact k,
  have p := archimedean_R (j - h),
  have t := p(x),
  cases t with n hn,
  cases hn with v hv,
  have v1 : 0 < ↑n,
  linarith,
  have g : 0 < (j - h - 1 / ↑n),
  linarith,
  have s : 0 < ↑n * (j - h - 1 / ↑n),
  revert v1,
  revert g,
  have b := mul_pos (0 < (j - h - 1 / ↑n)) (0 < ↑n),
-/