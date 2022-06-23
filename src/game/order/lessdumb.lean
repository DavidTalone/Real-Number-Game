import game.order.level08
import game.order.level02
open real

namespace xena -- hide

/-
Hint: use max_comm
-/

lemma abs_eq_abs_neg (a : ℝ) : abs a = abs (-a) :=
begin
  rw abs,
  rw abs,
  simp,
  exact max_comm a (-a),
  

end



end xena -- hide