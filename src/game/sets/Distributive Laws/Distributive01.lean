import game.sets.sets_level01
import data.set.basic
import tactic

namespace xena -- hide

variable X : Type -- hide

open_locale classical

theorem distr_union (A B C : set X) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  rw ext_iff,
  intro h,
  split,
  intro j,
  rw mem_inter_iff,
  rw mem_union_iff,
  rw mem_union_iff,
  rw mem_union_iff at j,
  rw mem_inter_iff at j,
  cases j with d hd,
  split,
  left,
  exact d,
  left,
  exact d,
  cases hd with t ht,
  split,
  right,
  exact t,
  right,
  exact ht,
  intro j,
  rw mem_inter_iff at j,
  cases j with d hd,
  cases d with t ht,
  left,
  exact t,
  cases hd with y hy,
  left,
  exact y,
  right,
  split,
  exact ht,
  exact hy,
end

end xena -- hide