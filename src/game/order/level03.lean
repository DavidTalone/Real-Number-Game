import game.order.level02

namespace xena -- hide

/-
# Chapter 2 : Order

## Level 3

Another property of the absolute value.
-/

notation `|` x `|` := abs x --hide

/- Lemma
For any two real numbers $a$ and $b$, we have that
$$|a| ≤ c ↔ -c ≤ a ≤ c$$.
-/
theorem abs_le (a c : ℝ) (h : 0 ≤ c): |a| ≤ c ↔ (-c) ≤ a ∧ a ≤ c :=
begin
    split,
    intro j,
    rcases lt_trichotomy a 0 with han | haz | hap,
    swap,
    rw haz,
    split,
    linarith,
    exact h,
    split,
    have h1 : | a | = - a, exact abs_of_neg han,
    rw h1 at j,
    linarith,
    linarith,
    split,
    have h2 : | a | = a, exact abs_of_pos hap,
    rw h2 at j,
    linarith,
    have h2 : | a | = a, exact abs_of_pos hap,
    rw h2 at j,
    exact j,
    intro k,
    cases k with d hd,
    rcases lt_trichotomy a 0 with han | haz | hap,
    have h1 : | a | = - a, exact abs_of_neg han,
    rw h1,
    linarith,
    rw haz,
    norm_num,
    exact h,
    have h1 : | a | = a, exact abs_of_pos hap,
    rw h1,
    linarith,
end

end xena --hide




















/-
split,
    rcases lt_trichotomy a 0 with haNeg | haZero | haPos,
    { -- case a < 0
        intro H, 
        have h1 : | a | = - a, exact abs_of_neg haNeg,
        rw h1 at H, split, linarith, linarith,
    },
    { -- case a = 0
        intro H, rw haZero, split, linarith, exact h,
    },
    { -- case 0 < a
        intro H,
        have h1 : |a| = a, exact abs_of_pos haPos,
        rw h1 at H, split, linarith, exact H,
    },
    
    
    rcases lt_trichotomy a 0 with haNeg | haZero | haPos,
    { -- case a < 0
        intro H, 
        have h1 : | a | = - a, exact abs_of_neg haNeg,
        rw abs_le, 
        exact H,
    },
    { -- case a = 0
        intro H,
        rw abs_le, exact H,
    },
    { -- case 0 < a
        intro H,
        rw abs_le, exact H,
    },
    

    done
-/