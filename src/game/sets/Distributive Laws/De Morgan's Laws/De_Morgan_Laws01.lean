import game.sets.sets_level01
import data.set.basic
import tactic

namespace xena -- hide

variable X : Type -- hide

open_locale classical

theorem distr_dif_union (A B C : set X) : A \ (B ∪ C) = (A \ B) ∩ (A \ C):=
begin
  rw ext_iff,
  intro h,
  split,
  intro j,
  rw mem_inter_iff,
  split,
  cases j with r hr,
  split,
  exact r,
  simp_rw mem_union_iff at hr,
  push_neg at hr,
  cases hr with d hd,
  exact d,
  rw mem_sdiff_iff at j,
  cases j with f hf,
  simp_rw mem_union_iff at hf,
  push_neg at hf,
  cases hf with y hy,
  split,
  exact f,
  exact hy,
  intro n,
  rw mem_sdiff_iff,
  split,
  simp_rw mem_inter_iff at n,
  cases n with y hy,
  rw mem_sdiff_iff at hy,
  cases hy with t ht,
  exact t,
  rw mem_inter_iff at n,
  rw mem_sdiff_iff at n,
  rw mem_sdiff_iff at n,
  cases n with j hj,
  cases j with g hg,
  cases hj with r hr,
  rw mem_union_iff,
  push_neg,
  split,
  exact hg,
  exact hr,
end

end xena -- hide