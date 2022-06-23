import game.order.level04

namespace xena -- hide

theorem abs_le_if_pos_neg_le (c ε  : ℝ) : max (c)(-c) ≤ ε → |c| ≤ ε  :=
begin
  intro h,
  rcases lt_trichotomy c 0 with cn | cz | cp,
  swap,
  rw cz,
  rw cz at h,
  rw max_eq_left at h,
  norm_num,
  exact h,
  norm_num,
  have h1 : | c | = - c, exact abs_of_neg cn,
  rw h1,
  rw max_eq_right at h,
  exact h,
  linarith,
  have h1 : | c | = c, exact abs_of_pos cp,
  rw h1,
  rw max_eq_left at h,
  exact h,
  linarith,
end

end xena -- hide