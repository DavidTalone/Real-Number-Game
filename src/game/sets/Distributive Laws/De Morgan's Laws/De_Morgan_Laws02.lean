import game.sets.sets_level01
import data.set.basic
import tactic

namespace xena -- hide

variable X : Type -- hide

open_locale classical

theorem distr_dif_inter (A B C : set X) : A \ (B ∩ C) = (A \ B) ∪ (A \ C) := 
begin
  rw ext_iff,
  intro h,
  split,
  intro j,
  rw mem_sdiff_iff at j,
  rw mem_union_iff,
  rw mem_inter_iff at j,
  push_neg at j,
  cases j with d hd,
  cases hd with t ht,
  left,
  rw mem_sdiff_iff,
  split,
  exact d,
  exact t,
  right,
  rw mem_sdiff_iff,
  split,
  exact d,
  exact ht,
  intro k,
  rw mem_union_iff at k,
  rw mem_sdiff_iff,
  rw mem_inter_iff,
  push_neg,
  cases k with d hd,
  rw mem_sdiff_iff at d,
  cases d with y hy,
  split,
  exact y,
  left,
  exact hy,
  rw mem_sdiff_iff at hd,
  split,
  cases hd with t ht,
  exact t,
  cases hd with r hr,
  right,
  exact hr,
end

end xena -- hide
