import game.sup_inf.level01

namespace xena -- hide
-- World name : Sup and Inf

/-
# Chapter 3 : Sup and Inf

## Level 2  

-/

/-
The completeness axiom on the reals states that any non-empty subset 
$X \subseteq \mathbb{R}$ that is bounded above has a least upper bound.
Here we explore the converse statement: any set of reals that has a supremum is non-empty and 
has an upper bound. The second part of the result is trivial, but showing that the
set is non-empty will ask you to use techniques learned in the first world.
-/

-- definition is_upper_bound' (S : set ℝ) (x : ℝ) := x ∈ upper_bounds S 
-- (Definition above deprecated? GT)

definition is_lub (S : set ℝ) (x : ℝ) := is_upper_bound S x ∧ 
∀ y : ℝ, is_upper_bound S y → x ≤ y

definition has_lub (S : set ℝ) := ∃ x, is_lub S x 

local attribute [instance] classical.prop_decidable --hide


/- Lemma
Any set of reals that has a supremum is non-empty and bounded above.
-/
theorem nonempty_and_bounded_of_has_LUB (S : set ℝ) (H : has_lub S) : 
  (S ≠ ∅) ∧ (∃ x, is_upper_bound S x) :=
begin
  cases H with b Hb,
  split,
  intro t,
  have H1 : (b-1) ∈ upper_bounds S,
  change ∀ x ∈ S, x ≤ (b-1),
  by_contradiction hn,
  push_neg at hn,
  cases hn with d hd,
  cases hd with y hy,
  rw t at y,
  exact y,
  unfold is_lub at Hb,
  have HH := Hb.2 (b-1) H1,
  linarith,

  existsi b,
  exact Hb.1,


end 

end xena -- hide







/-
cases H with b Hb,
  -- b is LUB, Hb is proof it's LUB
  split,
  { -- first prove S is not empty, by contradiction as usual with empty sets
    intro Hempty,
    have H1 : (b-1) ∈ upper_bounds S,
    change ∀ x ∈ S, x ≤ (b-1),
    by_contradiction hn,
    push_neg at hn,
    cases hn with x h1, 
    cases h1 with h11 h12,
    rw Hempty at h11, 
    exact h11, 
    unfold is_lub at Hb,
    have HH := Hb.2 (b-1) H1, -- b - 1 is an upper bound
    linarith,
  },
  {
     existsi b,
     exact Hb.1,
  }, 
  done
-/