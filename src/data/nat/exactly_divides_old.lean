
/-

lemma divides_p_times (r : ℕ) (n : ℕ) : p^r ∣ n ↔ p^(r+1) ∣ (p * n) :=
calc p^r ∣ n ↔ (p * p^r) ∣ (p * n)  : (nat.mul_dvd_mul_iff_left (gt_zero hp)).symm
     ...     = (p^r * p ∣ p * n)     : by rw mul_comm

lemma exactly_divides_p_times (r : ℕ) (n : ℕ) : p^r ∣∣ n ↔ p^(r+1) ∣∣ (p * n) :=
have eq : (p * n) / p^(r+1) = n / p^r, from
calc (p * n) / p^(r+1) = (p * n) / (p^r * p)  : rfl
     ...               = (p * n) / (p * p^r)  : by rw mul_comm (p^r) p
     ...               = (p * n) / p / p^r    : by rw nat.div_div_eq_div_mul
     ...               = n / p^r    : by rw (nat.mul_div_cancel_left n (gt_zero hp)),
--      : congr_arg (λ m, m / p^r) (nat.mul_div_cancel_left n gt_zero),
and_congr (divides_p_times hp r n) (by rw eq)

lemma exactly_divides' {r : ℕ} {n : ℕ} : p^r ∣∣ n → (∀ i, p^i ∣ n ↔ i ≤ r) :=
begin
  intros prn i, apply iff.intro,
  { intro pin,
    apply (le_or_gt _ _).resolve_right, intro i_gt_r,
    have :=
    calc p^r * p = p^(r+1)  : rfl
         ...     ∣ p^i      : pow_dvd_pow p i_gt_r
         ...     ∣ n        : pin,
    exact absurd (dvd_div_of_mul_dvd (pos_pow_of_pos r (gt_zero hp)) this) prn.right,
  },
  { intro i_le_r,
    exact dvd.trans (pow_dvd_pow p i_le_r) (and.left prn) }
end

-/


/-

lemma exactly_divides_mul (r s a b : ℕ) : p^r ∣∣ a → p^s ∣∣ b → p^(r+s) ∣∣ a*b :=
begin
  intros pra psb, split,
  { rw nat.pow_add, exact mul_dvd_mul pra.left psb.left },
  let a' := a / p^r,
  have ha : p^r * a' = a := nat.mul_div_cancel' pra.left,
  let b' := b / p^s,
  have hb : p^s * b' = b := nat.mul_div_cancel' psb.left,
  have : (a * b) / (p^(r+s)) = (a / p^r) * (b / p^s) :=
  calc (a * b) / (p^(r+s)) = ((p^r * a') * (p^s * b')) / (p^r * p^s)
    : by rw [ha, hb, pow_add]
       ...                 = ((p^r * p^s) * (a' * b')) / (p^r * p^s)
    : by ac_refl
       ...                 = a' * b'
    : by rw nat.mul_div_cancel_left _
            (mul_pos (pos_pow_of_pos r (gt_zero hp)) (pos_pow_of_pos s (gt_zero hp)))
       ...                 = (a / p^r) * (b / p^s)  : rfl,
  rw this,
  exact prime.not_dvd_mul hp pra.right psb.right
end

-/


