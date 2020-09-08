/-
protected def raw_order : ℕ → ℕ
| 0 := 0
| 1 := 0
| n@(k+2) :=
  have n / p < n, from div_lt_self dec_trivial hp,
  if p ∣ n then succ (raw_order (n / p)) else 0

protected lemma raw_order_one : raw_order 1 = 0 := rfl

protected lemma raw_order_not_div : ∀ n (hn : ¬(p ∣ n)), raw_order n = 0
| 0 _ := rfl
| 1 _ := rfl
| n@(k+2) hn := if_neg hn

protected lemma raw_order_div : ∀ n (n_pos : n > 0) (hn : p ∣ n),
  raw_order n = succ (raw_order (n / p))
| 0       n_pos _  := absurd n_pos dec_trivial
| 1       _     hn :=
  have p < p, from
  calc p = 1  : eq_one_of_dvd_one hn
     ... < p  : hp,
  absurd this (lt_irrefl p)
| n@(k+2) _     hn := if_pos hn

end raw_order

-/


/-
protected lemma ind (n : ℕ) : ∀ (n_pos : n > 0), p^(ord p ⟨n,n_pos⟩) ∣∣ n :=
begin
  apply nat.strong_induction_on n, clear n, intros n ih n_pos,
  let np : ℕ+ := ⟨n,n_pos⟩,
  show p^(ord p np) ∣∣ n,
  by_cases h : (p : ℕ+) ∣ np,
  { let m := n / p,
    have n_pm : n = p * m := (nat.mul_div_cancel' h).symm,
    have m_pos : m > 0 := pos_of_mul_pos_left (n_pm ▸ n_pos : 0 < ↑p * m) dec_trivial,
    let mp : ℕ+ := ⟨m,m_pos⟩,
    have : np = p * mp := subtype.eq n_pm,
    rw [this, n_pm, ord_div, ←@exactly_divides_p_times ↑p p.property],
    have t1 : m < n := div_lt_self n_pos p.gt_one,
    exact ih m t1 m_pos,
  },
  { rw (ord_not_div _ h),
    unfold exactly_divides, split,
    exact one_dvd _, simpa
  }
end

lemma ord_iff_exactly_divides (r : ℕ) (n : ℕ+) : ord p n = r ↔ p^r ∣∣ n :=
-- this shouldn't really need tactic mode
begin
  have h : p^(ord p n) ∣∣ n := order.ind n n.property,
  apply iff.intro,
  { intro a, rw ←a, exact h },
  { exact exactly_divides_unique p.property h }
end
-/
