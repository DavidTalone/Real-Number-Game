import game.sets.sets_level01
import data.set.basic
import tactic

namespace xena -- hide

variable X : Type -- hide

open_locale classical

theorem distr_inter (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  rw ext_iff,
  intro h,
  split,
  intro j,
  rw mem_inter_iff at j,
  cases j with d hd,
  rw mem_union_iff,
  cases hd with y hy,
  left,
  split,
  exact d,
  exact y,
  right,
  split,
  exact d,
  exact hy,
  intro k,
  rw mem_union_iff at k,
  cases k with d hd,
  cases d with y hy,
  rw mem_inter_iff,
  split,
  exact y,
  left,
  exact hy,
  cases hd with t ht,
  rw mem_inter_iff,
  split,
  exact t,
  right,
  exact ht,
end


end xena -- hide