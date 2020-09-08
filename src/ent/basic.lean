/- Assorted trivialities. -/

import data.nat.basic
import tactic.ring

open nat

theorem nat.pow_two {a : ℕ} : a^2 = a * a := begin rw [(^), (^)], simp end

lemma sqrt_eq {x y : ℕ} : x * x = y * y → x = y := begin
  intro H,
  apply le_antisymm; { apply nat.mul_self_le_mul_self_iff.mpr, rw H }
end

lemma pos_of_square_pos {x : ℕ} (H : x^2 > 0) : x > 0 :=
  (eq_zero_or_pos x).resolve_left (λ x0, have H' : 0^2 > 0 := by rwa x0 at H,
  (dec_trivial : ¬(0^2 > 0)) H')

-- @[simp] lemma nat_pow_is_pow {a i : ℕ} : a^i = monoid.pow a i := sorry

-- #check mul_pow
lemma nat.mul_pow {x y i : ℕ} : (x * y)^i = x^i * y^i := begin
  induction i with j ih,
  { reflexivity },
  { unfold nat.pow, rw ih, ac_refl }
end

lemma square_twice {x : ℕ} : (x^2)^2 = x^4 :=
calc (x^2)^2 = x^2 * x^2  : by rw nat.pow_two
     ...     = x^(2 + 2)  : by rw nat.pow_add

lemma self_divides_square {x : ℕ} : x ∣ x^2 :=
calc   x = x^1  : (nat.pow_one x).symm
     ... ∣ x^2  : pow_dvd_pow x dec_trivial

lemma self_divides_pow {x n : ℕ} : n > 0 → x ∣ x^n := λ Hn,
calc   x = x^1  : (nat.pow_one x).symm
     ... ∣ x^n  : pow_dvd_pow x Hn

lemma pow_dvd_pow_of_dvd {a b n : ℕ} : a ∣ b → a^n ∣ b^n := begin
  intro H,
  induction n with m ih,
  { simp },
  { exact mul_dvd_mul ih H }
end

lemma one_if_dvd_coprime {a b : ℕ} (a_b : coprime a b) (a_div_b : a ∣ b) : a = 1 :=
  have p : a ∣ 1 :=
  calc   a ∣ gcd a b  : dvd_gcd (dvd_refl a) a_div_b
       ... = 1        : a_b,
  eq_one_of_dvd_one p

lemma one_if_pow_one {a n : ℕ} (Hn : n > 0) (H : a^n = 1) : a = 1 :=
  dvd_antisymm (H ▸ self_divides_pow Hn) (one_dvd a)

lemma dvd_of_pow_dvd_pow {a b n : ℕ} (Hn : n > 0) (H : a^n ∣ b^n) : a ∣ b := begin
  cases eq_zero_or_pos b with b_zero b_pos,
  { rw b_zero, exact dvd_zero _ },
  let g := gcd a b,
  have gcd_pos : g > 0 := gcd_pos_of_pos_right a b_pos,
  rcases exists_coprime gcd_pos with ⟨a', b', a'_b', Ha', Hb'⟩,
  change a = a' * g at Ha',
  change b = b' * g at Hb',
  rw [Ha', Hb', nat.mul_pow, nat.mul_pow] at H,
  have := dvd_of_mul_dvd_mul_right (pos_pow_of_pos n gcd_pos) H,
  have a'n_b'n := coprime.pow n n a'_b',
  have := one_if_dvd_coprime a'n_b'n this,
  have := one_if_pow_one Hn this,
  have :=
  calc b = b' * g  : Hb'
     ... = b' * (1 * g)   : by simp
     ... = b' * (a' * g)  : by rw this
     ... = b' * a         : by rw Ha',
  rw this,
  exact dvd_mul_left a b'
end

lemma polarization {x y : ℤ}
  : 2 * (x*x + y*y) = (x + y)*(x + y) + (x - y)*(x - y) := by ring

lemma nat.polarization {x y : ℕ} (H : x ≥ y)
  : 2 * (x^2 + y^2) = (x + y)^2 + (x - y)^2 := begin
  repeat { rw nat.pow_two },
  have p := @polarization (int.of_nat x) (int.of_nat y),
  have two : 2 = int.of_nat 2 := rfl,
  rw two at p,
  rw [←int.of_nat_sub H] at p,
  exact int.of_nat_inj p
end

lemma pos_of_pos_mul {k n : ℕ} : k * n > 0 → n > 0 := begin
  intro kn_pos,
  apply (eq_zero_or_pos n).resolve_left,
  intro n_zero,
  simp [n_zero] at kn_pos,
  exact lt_irrefl _ kn_pos
end

lemma le_square {n : ℕ} : n ≤ n^2 := by rw nat.pow_two; exact le_mul_self n
