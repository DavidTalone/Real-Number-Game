import game.max.level01 -- hide

open_locale classical -- hide

noncomputable theory -- hide

namespace xena -- hide

/-
# Chapter ? : Max and abs

## Level 2

`max_comm` is the statement that `max a b = max b a`. See if you can prove it.
-/

/- Hint : Hint
Again, do a case split with `cases le_total a b`. 
-/

/- Lemma
For any real numbers $a$ and $b$, we have $\max(a,b) = \max(b,a).$
-/
theorem max_comm (a b : ℝ) : max a b = max b a :=
begin
  cases le_total a b with h h;
  rw max_eq_right h; 
  rw max_eq_left h,
  
end

end xena --hide
