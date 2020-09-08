/- Even and odd natural numbers. -/

import data.nat.modeq
import ent.basic
import ent.modeq
import ent.xor

namespace nat

-- * Definition

def even (a : ℕ) := a ≡ 0 [MOD 2]
def odd (a : ℕ) := a ≡ 1 [MOD 2]

instance decidable_even {a : ℕ} : decidable (even a) :=
  by unfold even; apply_instance
instance decidable_odd {a : ℕ} : decidable (odd a) :=
  by unfold odd; apply_instance

-- * Basic facts

theorem even_iff_two_dvd {a : ℕ} : even a ↔ 2 ∣ a := modeq.modeq_zero_iff

theorem even_or_odd (a : ℕ) : even a ∨ odd a :=
  mod_two_eq_zero_or_one a

theorem not_even_and_odd (a : ℕ) : ¬ (even a ∧ odd a) :=
  λ ⟨ea, oa⟩,
  have h : 0 ≡ 1 [MOD 2] := ea.symm.trans oa,
  (dec_trivial : ¬ (0 ≡ 1 [MOD 2])) h

theorem even_xor_odd {a : ℕ} : xor (even a) (odd a) :=
  xor.mk (even_or_odd a) (not_even_and_odd a)

theorem odd_plus_odd_is_even {a b : ℕ} : odd a → odd b → even (a + b) :=
  modeq.modeq_add

theorem odd_plus_even_is_odd {a b : ℕ} : odd a → even b → odd (a + b) :=
  modeq.modeq_add

theorem even_plus_odd_is_odd {a b : ℕ} : even a → odd b → odd (a + b) :=
  modeq.modeq_add

theorem odd_minus_odd_is_even {a b : ℕ} (H : a ≤ b) : odd a → odd b → even (b - a) :=
  begin
    intros oa ob,
    cases even_or_odd (b - a) with eba oba,
    { assumption },
    { have h : even (a + (b - a)) := odd_plus_odd_is_even oa oba,
      rw add_sub_of_le H at h,
      have := and.intro h ob,
      have := not_even_and_odd b,
      contradiction }
  end

theorem even_times_any_is_even {a b : ℕ} : even a → even (a * b) := λ ea,
  even_iff_two_dvd.mpr $ dvd.trans (even_iff_two_dvd.mp ea) (dvd_mul_right a b)

theorem two_n_even (n : ℕ) : even (2 * n) :=
  even_times_any_is_even (dec_trivial : 2 ≡ 0 [MOD 2])

theorem two_n_not_odd (n : ℕ) : ¬ (odd (2 * n)) :=
  even_xor_odd.resolve_right.mpr (two_n_even n)

theorem odd_times_odd_is_odd {a b : ℕ} : odd a → odd b → odd (a * b) := modeq.modeq_mul

theorem even_square_is_even {a : ℕ} : even a → even (a^2) :=
  by rw pow_two; apply even_times_any_is_even

theorem odd_square_is_odd {a : ℕ} : odd a → odd (a^2) := begin
  intro oa,
  rw pow_two,
  exact (odd_times_odd_is_odd oa oa)
end

theorem even_iff_square_even {a : ℕ} : even a ↔ even (a^2) :=
  iff.intro even_square_is_even
  (even_xor_odd.resolve_right.mp ∘ mt odd_square_is_odd ∘
   even_xor_odd.resolve_right.mpr)

theorem odd_iff_square_odd {a : ℕ} : odd a ↔ odd (a^2) :=
  iff.intro odd_square_is_odd
  (even_xor_odd.resolve_left.mp ∘ mt even_square_is_even ∘
   even_xor_odd.resolve_left.mpr)

/- This is longer anyways 
theorem odd_iff_square_odd {a : ℕ} : odd a ↔ odd (a^2) := 
calc odd a ↔ ¬ even a      : even_xor_odd.resolve_left.symm
     ...   ↔ ¬ even (a^2)  : not_congr even_iff_square_even
     ...   ↔ odd (a^2)     : even_xor_odd.resolve_left
-/

theorem not_both_even_if_coprime {a b : ℕ} : coprime a b → ¬ (even a ∧ even b)
  := begin
  intros a_b eab, cases eab with ea eb,
  rw even_iff_two_dvd at ea eb,
  have := not_coprime_of_dvd_of_dvd dec_trivial ea eb, contradiction
end

end nat



open nat

-- * Squares of even and odd numbers mod 4

lemma odd_number_lemma {a : ℕ} (o : odd a) : ∃ k : ℕ, a = 2*k + 1 := modeq.rep_of_modeq o dec_trivial

lemma odd_square_lemma {k : ℕ} : (2*k+1)^2 = 4*(k*k + k) + 1 := 
  calc
    (2*k+1)^2 = (2*k + 1) * (2*k + 1)     : by rw nat.pow_two
    ...       = 2*k * (2*k + 1) + 1 * (2*k + 1) : by rw right_distrib
    ...       = 2*k * (2*k + 1) + 2*k + 1 : by simp
    ...       = 2*k * (2*k) + 2*k * 1 + 2*k + 1 : by rw left_distrib
    ...       = 2*k*2*k + 2*k * 1 + 2*k + 1   : by rw ←mul_assoc
    ...       = 2*k*2*k + 2*k + 2*k + 1   : by simp
    ...       = 2*(k*2)*k + 2*k + 2*k + 1 : by rw ←mul_assoc
    ...       = 2*(2*k)*k + 2*k + 2*k + 1 : by rw (mul_comm k 2)
    ...       = 2*2*k*k + 2*k + 2*k + 1   : by rw ←mul_assoc
    ...       = 4*k*k + 2*k + 2*k + 1     : by refl
    ...       = 4*k*k + (2*k + 2*k) + 1   : by rw (add_assoc (4*k*k) (2*k) (2*k))
    ...       = 4*k*k + (2 + 2)*k + 1     : by rw (right_distrib 2 2 k)
    ...       = 4*k*k + 4*k + 1           : by refl
    ...       = 4*(k*k) + 4*k + 1         : by rw mul_assoc
    ...       = 4*(k*k + k) + 1           : by rw left_distrib

theorem odd_square_mod_four {a : ℕ} : odd a → a^2 ≡ 1 [MOD 4] :=
  begin
    intro o,
    cases modeq.rep_of_modeq o dec_trivial with k,
    rw [h, odd_square_lemma],
    apply modeq.modeq_of_rep
  end

theorem even_square_mod_four {a : ℕ} : even a → a^2 ≡ 0 [MOD 4] :=
  begin
    intro e,
    rw modeq.modeq_zero_iff,
    have h : 2 ∣ a := begin rw ←modeq.modeq_zero_iff, assumption end,
    have h2 : 4 ∣ a^2 := begin
      rw nat.pow_two,
      apply (mul_dvd_mul h h)
    end,
    assumption
  end

theorem square_two_mod_four {a : ℕ} : ¬ (a^2 ≡ 2 [MOD 4]) :=
  begin
    intro,
    cases even_or_odd a,
    { have h1 : 2 ≡ 0 [MOD 4] :=
        modeq.trans (modeq.symm a_1) (even_square_mod_four h),
      have h2 : ¬ (2 ≡ 0 [MOD 4]) := dec_trivial,
      exact h2 h1 },
    { have h1 : 2 ≡ 1 [MOD 4] :=
        modeq.trans (modeq.symm a_1) (odd_square_mod_four h),
      have h2 : ¬ (2 ≡ 1 [MOD 4]) := dec_trivial,
      exact h2 h1 }
  end

