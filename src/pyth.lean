import data.nat.basic
import data.nat.modeq

import ent.basic
import ent.gcd
import ent.modeq
import ent.parity

set_option max_memory 4096

open nat

section pyth
  parameters a b c : ℕ
  parameter py : a^2 + b^2 = c^2
  include a b c py

  lemma not_both_odd : not (odd a ∧ odd b) :=
    begin
      intro oab,
      cases oab with oa ob,
      have ha : a^2 ≡ 1 [MOD 4] := odd_square_mod_four oa,
      have hb : b^2 ≡ 1 [MOD 4] := odd_square_mod_four ob,
      have hc : c^2 ≡ 2 [MOD 4] := begin
        rw ←py, apply modeq.modeq_add; assumption end,
      apply (@square_two_mod_four c), assumption
    end

  lemma at_least_one_even : even a ∨ even b :=
    begin
      cases even_or_odd a,
      { apply or.inl, assumption },
      { cases even_or_odd b,
        { apply or.inr, assumption },
        { have := and.intro ‹odd a› ‹odd b›,
          have := not_both_odd,
          contradiction } }
    end

  parameter a_b : coprime a b
  include a_b

  lemma not_both_even : ¬ (even a ∧ even b) := begin
    intros H,
    cases H with a_even b_even,
    rw even_iff_two_dvd at a_even b_even,
    have := not_coprime_of_dvd_of_dvd dec_trivial a_even b_even,
    contradiction
  end

  -- Need this later, so prove it before assumption "even b"
  lemma c_odd : odd c := begin
    have : odd (a^2 + b^2) := begin
      cases even_or_odd a with a_even a_odd,
      { cases even_or_odd b with b_even b_odd,
        { have := not_both_even,
          have := and.intro a_even b_even,
          contradiction },
        { apply even_plus_odd_is_odd,
          apply even_square_is_even, assumption,
          apply odd_square_is_odd, assumption } },
      { cases even_or_odd b with b_even b_odd,
        { apply odd_plus_even_is_odd,
          apply odd_square_is_odd, assumption,
          apply even_square_is_even, assumption },
        { have := not_both_odd,
          have := and.intro a_odd b_odd,
          contradiction } }
    end,
    rw py at this,
    cases even_or_odd c with c_even c_odd,
    { exact absurd (and.intro (even_square_is_even c_even) this)
                   (not_even_and_odd _) },
    { assumption }
  end

  parameter b_even : even b
  include b_even

  lemma a_odd : odd a := begin
    cases even_or_odd a with a_even _,
    { have := and.intro a_even b_even,
      have := not_both_even,
      contradiction },
    assumption
  end

/-
  lemma c_odd : odd c := begin
    cases even_or_odd c with c_even _,
    { refine absurd (and.intro _ _) (not_even_and_odd (c^2)),
      exact even_square_is_even c_even,
      rw ←py,
      apply odd_plus_even_is_odd,
      exact odd_square_is_odd a_odd,
      exact even_square_is_even b_even
    },
    assumption
  end
-/

  lemma a_c : coprime a c :=
    -- a^2 _|_ b^2 and so a^2 _|_ a^2 + b^2 = c^2 and then a _|_ c by divisibility.
    begin
      have a2_c2 : gcd (a*a) (c*c) = 1 := calc
        gcd (a*a) (c*c) = gcd (a^2) (c^2)           : by rw [nat.pow_two, nat.pow_two]
        ...             = gcd (a^2) (a^2 + b^2)     : by rw py
        ...             = gcd (a^2) (a^2 * 1 + b^2) : by simp
        ...             = gcd (a^2) (b^2)           : by rw gcd.gcd_row_op (a^2) (b^2) 1
        ...             = 1                         : coprime.pow 2 2 a_b,
      exact coprime.coprime_mul_left (coprime.coprime_mul_left_right a2_c2)
    end

  parameter pos : a > 0 ∧ b > 0 ∧ c > 0
  include pos

  lemma a_lt_c : a < c := begin
    cases nat.lt_or_ge a c with _ ge,
    { assumption },
    { have b2pos : b^2 > 0 := begin
        rw nat.pow_two,
        exact nat.mul_self_lt_mul_self_iff.mp pos.2.1
      end,
      have : a^2 < a^2 :=
      calc a^2 < a^2 + b^2  : nat.lt_add_of_pos_right b2pos
           ... = c^2        : by rw py
           ... = c*c        : by rw nat.pow_two
           ... ≤ a*a        : nat.mul_self_le_mul_self_iff.mp ge
           ... = a^2        : by rw nat.pow_two,
      exact absurd this (not_lt_of_ge (le_refl (a^2)))
      }
  end
  lemma a_le_c : a ≤ c := le_of_lt a_lt_c

  lemma cma_cpa_b2 : (c - a) * (c + a) = b^2 :=
    calc (c - a) * (c + a) = c^2 - a^2  : by rw [mul_comm, ←nat.mul_self_sub_mul_self_eq, nat.pow_two, nat.pow_two]
         ...               = a^2 + b^2 - a^2  : by rw py
         ...               = b^2  : by rw nat.add_sub_cancel_left

  -- local attribute [simp] add_comm add_left_comm add_assoc
  local attribute [simp] mul_comm mul_left_comm mul_assoc

  -- XXX: m > n?
  lemma ex : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ n < m ∧ coprime m n ∧
                        a = m^2 - n^2 ∧ b = 2 * m * n ∧ c = m^2 + n^2 :=
  begin
    have gac : gcd (c - a) (c + a) = 2 :=
      gcd.sum_difference_of_coprime_odd a c a_le_c a_c a_odd c_odd,
/-
    cases @exists_coprime (c - a) (c + a) (gac.symm ▸ (dec_trivial : 2 > 0)) with x H,
    cases H with y H',
    cases H' with x_y H'',
    cases H'' with hx hy,
-/
    rcases @exists_coprime (c - a) (c + a) (gac.symm ▸ (dec_trivial : 2 > 0)) with ⟨x, y, x_y, hx, hy⟩,
    have g := cma_cpa_b2,
    rw gac at hx hy,
    rw [hx, hy] at g,
    cases modeq.rep_of_modeq b_even dec_trivial with half_b Hb,
    simp at Hb,
    have : 2 * 2 * (x * y) = 2 * 2 * half_b^2 :=
      calc 2 * 2 * (x * y) = x * 2 * (y * 2)  : by simp
           ...             = b^2              : g
           ...             = (half_b * 2)^2   : by rw Hb
           ...             = (half_b * 2) * (half_b * 2)  : by rw nat.pow_two
           ...             = 2 * 2 * half_b^2 : by simp [nat.pow_two],
    have xyb : x * y = half_b^2 := nat.eq_of_mul_eq_mul_left dec_trivial this,
    cases coprime_square_product xyb x_y with n H5,
    cases H5 with m H6,
    cases H6 with xn2 ym2,
    existsi [m, n],
    have cma : c - a = 2 * n^2 := by rw [hx, mul_comm, xn2],
    have cpa : c + a = 2 * m^2 := by rw [hy, mul_comm, ym2],
    have twoa : 2 * a = 2 * (m^2 - n^2) :=
    calc 2 * a = (c + a) - (c - a)  : by rw gcd.sum_difference_difference a_le_c
         ...   = 2 * (m^2 - n^2)    : by simp [cma, cpa, nat.mul_sub_left_distrib],
    have twoc : 2 * c = 2 * (m^2 + n^2) :=
    calc 2 * c = (c - a) + (c + a)  : by rw gcd.sum_difference_sum a_le_c
         ...   = 2 * (m^2 + n^2)    : by simp [cma, cpa, left_distrib],
    repeat { split },
    { apply pos_iff_ne_zero.mpr, intro m0,
      have :=
      calc 0 = 0^2  : rfl
         ... = m^2  : by rw m0
         ... = y    : ym2.symm,
      have :=
      calc 0 = x * 2 * (0 * 2)  : by simp
         ... = x * 2 * (y * 2)  : by rw this
         ... = b^2  : g
         ... > 0    : pow_lt_pow_of_lt_left pos.2.1 (dec_trivial : 2 > 0),
      exact absurd this (lt_irrefl _)
    },
    { apply pos_iff_ne_zero.mpr, intro n0,
      have :=
      calc 0 = 0^2  : rfl
         ... = n^2  : by rw n0
         ... = x    : xn2.symm,
      have :=
      calc 0 = 0 * 2 * (y * 2)  : by simp
         ... = x * 2 * (y * 2)  : by rw this
         ... = b^2  : g
         ... > 0    : pow_lt_pow_of_lt_left pos.2.1 (dec_trivial : 2 > 0),
      exact absurd this (lt_irrefl _)
    },
    { apply lt_of_not_ge, intro n_ge_m,
      have :=
      calc c - a = 2 * n^2  : cma
           ...   ≥ 2 * m^2  : mul_le_mul_left 2 (pow_le_pow_of_le_left n_ge_m 2)
           ...   = c + a    : cpa.symm
           ...   > c        : nat.lt_add_of_pos_right pos.1
           ...   ≥ c - a    : nat.sub_le _ _,
      exact absurd this (lt_irrefl _)
    },
    { exact gcd.coprime_iff_squares_coprime.mp (ym2 ▸ xn2 ▸ x_y.symm) },
    { exact eq_of_mul_eq_mul_left dec_trivial twoa },
    {
      rw nat.pow_two at xyb xn2 ym2,
      have : b * b = (2 * m * n) * (2 * m * n) :=
      calc b * b = 2 * 2 * (half_b * half_b)    : by simp [*, Hb]
           ...   = 2 * 2 * (x * y)              : by rw ←xyb
           ...   = 2 * 2 * ((n * n) * (m * m))  : by rw [xn2, ym2]
           ...   = (2 * m * n) * (2 * m * n)    : by simp,
      exact sqrt_eq this
    },
    { exact eq_of_mul_eq_mul_left dec_trivial twoc }
  end
end pyth

/-
#check not_both_odd
#check not_both_even
#check c_odd
#check ex
#print axioms not_both_odd
-/
