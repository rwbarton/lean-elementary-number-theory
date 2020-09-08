import data.nat.gcd
import data.nat.prime

import pyth

open nat

local attribute [simp] mul_comm mul_left_comm mul_assoc

section fermat
  parameters x y z : ℕ
  parameter fmt : x^4 = y^4 + z^2
  parameter pos : x > 0 ∧ y > 0 ∧ z > 0
  include fmt pos

  lemma x_pos : x > 0 := pos.1
  lemma y_pos : y > 0 := pos.2.1
  lemma z_pos : z > 0 := pos.2.2

  lemma y_lt_x : y < x := begin
    cases nat.lt_or_ge y x with _ ge, { assumption },
    { have z2pos : z^2 > 0 := begin
        rw nat.pow_two,
        exact nat.mul_self_lt_mul_self_iff.mp z_pos
      end,
      have : y^4 < y^4 :=
      calc y^4 < y^4 + z^2  : nat.lt_add_of_pos_right z2pos
           ... = x^4        : by rw fmt
           ... ≤ y^4        : pow_le_pow_of_le_left ge 4,
      exact absurd this (not_lt_of_ge (le_refl (y^4)))
    }
  end
  lemma y_le_x : y ≤ x := le_of_lt y_lt_x

  lemma l1 : (x^2 + y^2) * (x^2 - y^2) = z^2 :=
  calc (x^2 + y^2) * (x^2 - y^2) = x^2 * x^2 - y^2 * y^2  : by rw ←nat.mul_self_sub_mul_self_eq
       ...                       = x^(2 + 2) - y^(2 + 2)  : by simp [nat.pow_add]
       ...                       = y^4 + z^2 - y^4        : by simp [fmt]
       ...                       = z^2                    : by rw nat.add_sub_cancel_left

  section x_y
    parameter x_y : coprime x y
    include x_y

    lemma x2_y2 : coprime (x^2) (y^2) := coprime.pow 2 2 x_y
    lemma l2 : gcd (x^2 - y^2) (x^2 + y^2) ∣ 2 :=
      gcd.sum_difference_of_coprime (y^2) (x^2) (pow_le_pow_of_le_left y_le_x 2) (coprime.pow 2 2 x_y.symm)

    section case_a
    parameter gmp2 : gcd (x^2 - y^2) (x^2 + y^2) = 2
    include gmp2

    lemma x2py2_even : 2 ∣ x^2 + y^2 := begin
      have := (gcd_dvd (x^2 - y^2) (x^2 + y^2)).right,
      rwa gmp2 at this,
    end

    lemma odd_x : odd x := begin
      apply even_xor_odd.resolve_left.mp, intro even_x,
      have := not_both_even_if_coprime x_y,
      cases even_or_odd y with even_y odd_y,
      { exact this ⟨even_x, even_y⟩ },
      { have x2py2_odd : odd (x^2 + y^2) :=
          even_plus_odd_is_odd (even_square_is_even even_x)
                               (odd_square_is_odd odd_y),
        exact not_even_and_odd (x^2 + y^2) ⟨even_iff_two_dvd.mpr x2py2_even, x2py2_odd⟩
      }
    end
    lemma odd_y : odd y := begin
      apply even_xor_odd.resolve_left.mp, intro even_y,
      have x2py2_odd : odd (x^2 + y^2) :=
        odd_plus_even_is_odd (odd_square_is_odd odd_x)
                             (even_square_is_even even_y),
        exact not_even_and_odd (x^2 + y^2) ⟨even_iff_two_dvd.mpr x2py2_even, x2py2_odd⟩
    end

    lemma case_a :
      ∃ x' y' z' : ℕ,
      0 < x' ∧ 0 < y' ∧ 0 < z' ∧ x' < x ∧ x'^4 = y'^4 + z'^2 :=
    begin
      have py : (y^2)^2 + z^2 = (x^2)^2 :=
      calc (y^2)^2 + z^2 = y^4 + z^2  : by rw square_twice
           ...           = x^4        : fmt.symm
           ...           = (x^2)^2    : by rw square_twice,
      have ppos : y^2 > 0 ∧ z > 0 ∧ x^2 > 0 :=
        ⟨ pos_pow_of_pos 2 y_pos, z_pos, pos_pow_of_pos 2 x_pos ⟩,
      have even_z : even z := or.resolve_right (even_or_odd z) (begin
          intro odd_z,
          have ex4 : even (x^4) := begin
            rw fmt,
            rw ←square_twice,
            apply odd_plus_odd_is_even,
            exact (odd_square_is_odd (odd_square_is_odd odd_y)),
            exact (odd_square_is_odd odd_z)
          end,
          have ox4 : odd (x^4) := begin
            rw ←square_twice,
            exact (odd_square_is_odd (odd_square_is_odd odd_x))
          end,
          exact absurd (and.intro ex4 ox4) (not_even_and_odd (x^4))
        end),
      have y2_z : coprime (y^2) z := begin
        have x4_y4 : coprime (x^4) (y^4) := coprime.pow 4 4 x_y,
        rw fmt at x4_y4,
        have y4_z2 : coprime (y^4) (z^2) := begin
          rw coprime at *,
          have : gcd (y^4) (z^2) = gcd (y^4) (y^4 * 1 + z^2) := gcd.gcd_row_op (y^4) (z^2) 1,
          rw gcd_comm at x4_y4,
          rewrite [nat.mul_one, x4_y4] at this,
          assumption
        end,
        rw ←square_twice at y4_z2,
        exact gcd.coprime_iff_squares_coprime.mp y4_z2,
      end,
      rcases ex (y^2) z (x^2) py y2_z even_z ppos
        with ⟨d,e,d_pos,e_pos,d_gt_e,_,Hy,Hz,Hx⟩,

      have e2_pos : e^2 > 0 := pos_pow_of_pos 2 e_pos,

      have d_ge_e : d ≥ e := le_of_lt d_gt_e,

      existsi [d, e, x*y],
      repeat { split },
      { exact d_pos }, { exact e_pos }, { exact mul_pos x_pos y_pos },
      { apply (nat.lt_or_ge d x).resolve_right,
        intro d_ge_x,
        have : x^2 < x^2 :=
        calc x^2 = d^2 + e^2  : by rw Hx
             ... ≥ x^2 + e^2  : nat.add_le_add_right (pow_le_pow_of_le_left d_ge_x 2) (e^2)
             ... > x^2        : nat.lt_add_of_pos_right e2_pos,
        exact absurd this (lt_irrefl _)
      },
      { have : d^4 - e^4 = (x * y)^2 :=
        calc d^4 - e^4 = (d^2)^2 - (e^2)^2  : by rw [square_twice, square_twice]
             ...       = (d^2)*(d^2) - (e^2)*(e^2)  : by rw [@nat.pow_two (d^2), @nat.pow_two (e^2)]
             ...       = (d^2 + e^2) * (d^2 - e^2)  : nat.mul_self_sub_mul_self_eq (d^2) (e^2)
             ...       = x^2 * y^2          : by rw [←Hx, ←Hy]
      -- Why is there no (a * b)^n = a^n * b^n
             ...       = (x * x) * (y * y)  : by simp [nat.pow_two]
             ...       = (x * y) * (x * y)  : by simp
             ...       = (x * y)^2          : by rw ←nat.pow_two,
        exact
        calc d^4 = (d^4 - e^4) + e^4  : (nat.sub_add_cancel (pow_le_pow_of_le_left d_ge_e 4)).symm
             ... = (x * y)^2 + e^4    : by rw this
             ... = e^4 + (x * y)^2    : by simp,
      }
    end
    end case_a

    section case_b
      parameter g : gcd (x^2 - y^2) (x^2 + y^2) = 1
      include g

      -- From (x^2 - y^2) * (x^2 + y^2) = z^2
      parameters s t : ℕ
      parameter Hs : x^2 + y^2 = s^2
      parameter Ht : x^2 - y^2 = t^2
      include Hs Ht

      def s_pos : s > 0 := begin
        apply (eq_zero_or_pos s).resolve_left, intro s_zero,
        simp [s_zero] at Hs,
        have : 0^2 > 0^2 :=
        calc 0^2 = x^2 + y^2  : by rw Hs
             ... ≥ x^2        : le_add_right _ _
             ... > 0^2        : pow_lt_pow_of_lt_left x_pos dec_trivial,
        exact absurd this (lt_irrefl _)
      end

      def s_odd : odd s := c_odd x y s Hs x_y
      def t_odd : odd t :=
        have l : s^2 + t^2 = 2 * x^2, from
        calc s^2 + t^2 = (x^2 - y^2) + (x^2 + y^2)  : by rw [add_comm, Hs, Ht]
             ...       = 2 * x^2                    : by rw ←gcd.sum_difference_sum (pow_le_pow_of_le_left y_le_x 2),

        begin
          cases even_or_odd t with t_even _,
          { have : odd (s^2 + t^2) :=
              odd_plus_even_is_odd (odd_square_is_odd s_odd)
                                   (even_square_is_even t_even),
            rw l at this,
            have e : even (2 * x^2) := even_times_any_is_even (dec_trivial : 2 ≡ 0 [MOD 2]),
            exact absurd (and.intro e this) (not_even_and_odd _)
          },
          assumption
        end

      def t_lt_s : t < s := lt_of_not_ge $ begin
        by_contradiction h,
        have :=
        calc x^2 + y^2 = s^2        : Hs
             ...       ≤ t^2        : pow_le_pow_of_le_left h 2
             ...       = x^2 - y^2  : Ht.symm
             ...       ≤ x^2        : sub_le _ _
             ...       < x^2 + y^2  : nat.lt_add_of_pos_right
                                      (pos_pow_of_pos 2 y_pos),
        exact absurd this (lt_irrefl _) -- @[irrefl]?
      end
      def t_le_s := le_of_lt t_lt_s

      def spt_even : even (s + t) := odd_plus_odd_is_even s_odd t_odd
      def smt_even : even (s - t) := odd_minus_odd_is_even t_le_s t_odd s_odd

      -- These definitions are in core lean :(
      local attribute [trans] dvd_trans
      local attribute [refl] dvd_refl

      def s_t : coprime s t := begin
        apply coprime_of_dvd', intros k ks kt,
        have x2_y2 := gcd.coprime_iff_squares_coprime.mpr x_y,
        have := gcd.sum_difference_of_coprime (y^2) (x^2)
                (pow_le_pow_of_le_left y_le_x 2) x2_y2.symm,
        have k2_div_sub :=
        calc k^2 ∣ t^2  : pow_dvd_pow_of_dvd kt
             ... = x^2 - y^2  : Ht.symm,
        have k2_div_add :=
        calc k^2 ∣ s^2  : pow_dvd_pow_of_dvd ks
             ... = x^2 + y^2  : Hs.symm,
        have k2_div_2 := dvd.trans (dvd_gcd k2_div_sub k2_div_add) this,
        cases (dvd_prime dec_trivial).mp
              (dvd.trans self_divides_square k2_div_2) with k_1 k_2,
        { rw k_1 },
        { rw k_2 at k2_div_2, have : ¬(4 ∣ 2) := dec_trivial, contradiction }
      end

      def u := (s + t) / 2
      lemma lu : 2 * u = s + t :=
        nat.mul_div_cancel' (even_iff_two_dvd.mp spt_even)
      def v := (s - t) / 2
      lemma lv : 2 * v = s - t :=
        nat.mul_div_cancel' (even_iff_two_dvd.mp smt_even)
      lemma u_v : coprime u v := begin
        have g_div_two := gcd.sum_difference_of_coprime t s t_le_s s_t.symm,
        have two_div_g := dvd_gcd (even_iff_two_dvd.mp smt_even) (even_iff_two_dvd.mp spt_even),
        have g_eq_two := dvd_antisymm g_div_two two_div_g,
        rw [←lu, ←lv] at g_eq_two,
        have :=
        calc 2 * gcd u v = gcd (2 * u) (2 * v)  : by rw gcd_mul_left
             ...         = gcd (2 * v) (2 * u)  : gcd_comm _ _
             ...         = 2                    : g_eq_two
             ...         = 2 * 1                : by simp,
        exact eq_of_mul_eq_mul_left dec_trivial this
      end

      lemma y2_2uv : y^2 = 2 * u * v := begin
      have :=
      calc 2 * y^2 = (x^2 + y^2) - (x^2 - y^2)
        : (gcd.sum_difference_difference (pow_le_pow_of_le_left y_le_x 2)).symm
           ...     = s^2 - t^2  : by rw [Hs, Ht]
           ...     = s*s - t*t  : by repeat { rw nat.pow_two }
           ...     = (s + t) * (s - t)  : by rw nat.mul_self_sub_mul_self_eq
           ...     = (2 * u) * (2 * v)  : by rw [lu, lv]
           ...     = 2 * (2 * u * v)    : by ac_refl,
      exact eq_of_mul_eq_mul_left dec_trivial this
      end

      lemma u2_v2_x2 : u^2 + v^2 = x^2 := begin
      have :=
      calc (2^2) * x^2
                   = (2 * 2) * x^2  : by reflexivity
           ...     = 2 * (2 * x^2)  : by rw [mul_assoc]
           ...     = 2 * ((x^2 - y^2) + (x^2 + y^2))
        : by rw (gcd.sum_difference_sum (pow_le_pow_of_le_left y_le_x 2))
           ...     = 2 * (s^2 + t^2)  : by rw [Hs, Ht, add_comm]
           ...     = (s + t)^2 + (s - t)^2  : nat.polarization t_le_s
           ...     = (2 * u)^2 + (2 * v)^2  : by rw [lu, lv]
           ...     = 2^2 * u^2 + 2^2 * v^2  : by rw [nat.mul_pow, nat.mul_pow]
           ...     = 2^2 * (u^2 + v^2)  : by rw mul_add,
      exact eq_of_mul_eq_mul_left dec_trivial this.symm
      end

      lemma y_even : even y := begin
        apply even_iff_square_even.mpr,
        rw [y2_2uv, mul_assoc],
        apply two_n_even
      end
      def half_y := y / 2
      lemma ly : 2 * half_y = y :=
        nat.mul_div_cancel' (even_iff_two_dvd.mp y_even)
      lemma u_or_v_even : even u ∨ even v := begin
        by_contradiction a,
        cases (decidable.not_or_iff_and_not (even u) (even v)).mp a
          with neu nev,
        rw [even_xor_odd.resolve_left] at neu nev,
        have :=
        calc 2 * (u * v) = 2 * u * v  : by ac_refl
             ... = y^2       : y2_2uv.symm
             ... = (2 * half_y)^2  : by rw ly
             ... = (2 * half_y) * (2 * half_y)  : pow_two
             ... = 2 * (2 * (half_y * half_y))  : by ac_refl,
        have := nat.eq_of_mul_eq_mul_left dec_trivial this,
        have odd_uv : odd (u * v) := odd_times_odd_is_odd neu nev,
        have also_even : even (2 * (half_y * half_y)) := two_n_even _,
        rw ←this at also_even,
        exact not_even_and_odd _ ⟨also_even, odd_uv⟩
      end
      lemma uvx_pos : u > 0 ∧ v > 0 ∧ x > 0 := begin
        repeat { split },
        { apply pos_of_pos_mul, rw lu,
          exact calc s + t ≥ s  : le_add_right _ _
                     ...   > 0  : s_pos
        },
        { apply pos_of_pos_mul, rw lv,
          exact nat.sub_pos_of_lt t_lt_s
        },
        { exact x_pos }
      end
      -- have u_v, u^2 + v^2 = x^2, y^2 = 2 * u * v, u > 0 ∧ v > 0
      -- If u is even, swap u & v
      section even_v
        parameters u' v' : ℕ
        parameter u'_pos : u' > 0
        parameter v'_pos : v' > 0
        parameter u'_v' : coprime u' v'
        parameter u'2_v'2_x2 : u'^2 + v'^2 = x^2
        parameter y2_2u'v' : y^2 = 2 * u' * v'
        include u'_pos v'_pos u'_v' u'2_v'2_x2 y2_2u'v'

        parameter even_v' : even v'
        include even_v'

        lemma u'v'x_pos : u' > 0 ∧ v' > 0 ∧ x > 0 := ⟨u'_pos, v'_pos, x_pos⟩
        lemma u'_2v' : coprime u' (2 * v') := begin
          refine coprime.mul_right _ u'_v',
          exact coprime.coprime_dvd_right (even_iff_two_dvd.mp even_v') u'_v'
        end
        lemma v'_twice_square_etc : ∃ m k, u' = m^2 ∧ v' = 2 * k^2 := begin
          have u'2v'_y2 : u' * (2 * v') = y^2 :=
          calc u' * (2 * v') = 2 * u' * v'  : by ac_refl
               ...         = y^2        : y2_2u'v'.symm,
          rcases coprime_square_product u'2v'_y2 u'_2v' with ⟨m, k1, Hm, Hk1⟩,
          have even_k1 : even k1 := begin
            apply or.resolve_right (even_or_odd k1),
            intro odd_k1, have := odd_square_is_odd odd_k1, rw ←Hk1 at this,
            have := two_n_not_odd v', contradiction
          end,
          let k := k1 / 2,
          have H' := nat.mul_div_cancel' (even_iff_two_dvd.mp even_k1),
          existsi [m, k],
          split, { exact Hm }, {
          have :=
          calc 2 * v' = k1^2         : Hk1
               ...   = (2 * k)^2    : by rw H'
               ...   = (2*k)*(2*k)  : nat.pow_two
               ...   = 2*(2*(k*k))  : by ac_refl
               ...   = 2*(2*k^2)    : by rw ←nat.pow_two,
          exact nat.eq_of_mul_eq_mul_left dec_trivial this }
        end

        lemma case_b : ∃ g h k, 
          0 < g ∧ 0 < h ∧ 0 < k ∧ g < x ∧ g^4 = h^4 + k^2 :=
        begin
          rcases ex u' v' x u'2_v'2_x2 u'_v' even_v' u'v'x_pos
            with ⟨d, e, dpos, epos, d_gt_e, d_e, Hu', Hv', Hx⟩,
          rcases v'_twice_square_etc with ⟨m, k, Hm, Hk⟩,
          have : k^2 = d * e := nat.eq_of_mul_eq_mul_left (dec_trivial : 2 > 0) (
          calc 2 * k^2 = v'            : Hk.symm
               ...     = 2 * d * e    : Hv'
               ...     = 2 * (d * e)  : by rw mul_assoc),
          rcases coprime_square_product this.symm d_e with ⟨g_, h, Hg, Hh⟩,
          -- Weird shadowing behavior if we use "g", because u depends on the
          -- assuption "g" defined way above.
          existsi [g_, h, m], repeat { split },
          { exact pos_of_square_pos (Hg ▸ dpos) },
          { exact pos_of_square_pos (Hh ▸ epos) },
          { exact pos_of_square_pos (Hm ▸ u'v'x_pos.1) },
          { exact
            calc g_ ≤ g_^2  : le_square
                ... = d     : Hg.symm
                ... ≤ d^2   : le_square
                ... < d^2 + e^2  : nat.lt_add_of_pos_right
                                   (pos_pow_of_pos 2 epos)
                ... = x     : Hx.symm
          },
          { exact calc g_^4 = (g_^2)^2  : by rw square_twice
                       ...  = d^2      : by rw Hg
                       ...  = d^2 - e^2 + e^2
                    : by rw nat.sub_add_cancel (pow_le_pow_of_le_left (le_of_lt d_gt_e) 2)
                       ...  = u' + e^2  : by rw Hu'
                       ...  = m^2 + (h^2)^2  : by rw [Hm, Hh]
                       ...  = h^4 + m^2  : by rw [square_twice, add_comm] }
        end
      end even_v
    end case_b
  end x_y

  set_option trace.simplify.rewrite true

  lemma descent : ∃ x' y' z',
    0 < x' ∧ 0 < y' ∧ 0 < z' ∧ x' < x ∧ x'^4 = y'^4 + z'^2 := begin
    let g := gcd x y,
    have g_pos : g > 0 := gcd_pos_of_pos_left y x_pos,
    cases eq_or_lt_of_le (succ_le_of_lt g_pos) with g_eq_1 g_gt_1,
    swap,
    { -- g > 1
      have g_dvd_x : g ∣ x := (gcd_dvd x y).left,
      have g_dvd_y : g ∣ y := (gcd_dvd x y).right,
      let x' := x/g,
      have Hx' : g * x' = x := nat.mul_div_cancel' g_dvd_x,
      let y' := y/g,
      have Hy' : g * y' = y := nat.mul_div_cancel' g_dvd_y,
      have g2_dvd_z : g^2 ∣ z := begin
        -- nat.dvd_sub doesn't actually need the (H : n ≤ m) hypothesis
        have : g^4 ∣ z^2 :=
          (nat.dvd_add_iff_right (pow_dvd_pow_of_dvd g_dvd_y)).mpr
          (fmt ▸ pow_dvd_pow_of_dvd g_dvd_x),
        apply dvd_of_pow_dvd_pow (dec_trivial : 2 > 0),
        rwa square_twice
      end,
      let z' := z/(g^2),
      have Hz' : g^2 * z' = z := nat.mul_div_cancel' g2_dvd_z,
      existsi [x', y', z'], repeat { split },
      { apply pos_of_pos_mul, rw Hx', exact x_pos },
      { apply pos_of_pos_mul, rw Hy', exact y_pos },
      { apply pos_of_pos_mul, rw Hz', exact z_pos },
      { exact div_lt_self x_pos g_gt_1 },
      { have :=
        calc g^4 * x'^4 = (g * x')^4  : by rw nat.mul_pow
             ...        = x^4         : by rw Hx'
             ...        = y^4 + z^2   : by rw fmt
             ...        = (g * y')^4 + (g^2 * z')^2  : by rw [Hy', Hz']
             ...        = g^4 * y'^4 + g^4 * z'^2  : by rw [nat.mul_pow, nat.mul_pow, square_twice]
             ...        = g^4 * (y'^4 + z'^2)  : by rw mul_add,
        exact nat.eq_of_mul_eq_mul_left (pos_pow_of_pos 4 g_pos) this
      }
    },
    { -- g = 1
      have x_y : coprime x y := g_eq_1.symm,
      let gmp := gcd (x^2 - y^2) (x^2 + y^2),
      have : gmp ∣ 2 := l2 x_y,
      cases (dvd_prime dec_trivial).mp this with gmp1 gmp2, swap,
      { -- gmp = 2
        exact case_a x_y gmp2   -- planning!!
      },
      { -- gmp = 1
        rcases coprime_square_product l1 ((gcd_comm _ _).trans gmp1)
          with ⟨s,t,Hs,Ht⟩,
        -- this got a bit out of control
        let u0 := u x_y gmp1 s t Hs Ht,
        let v0 := v x_y gmp1 s t Hs Ht,
        let uvx_pos0 := uvx_pos x_y gmp1 s t Hs Ht,
        let u_v0 := u_v x_y gmp1 s t Hs Ht,
        let u2_v2_x2_0 := u2_v2_x2 x_y gmp1 s t Hs Ht,
        let y2_2uv_0 := y2_2uv x_y gmp1 s t Hs Ht,
        have : even u0 ∨ even v0 := u_or_v_even x_y gmp1 s t Hs Ht,
        cases this with even_u0 even_v0,
        { have u2_v2_x2' : v0^2 + u0^2 = x^2 :=
          calc v0^2 + u0^2 = u0^2 + v0^2  : by ac_refl
               ...         = x^2  : u2_v2_x2_0,
          have y2_2uv' : y^2 = 2 * v0 * u0 :=
          calc y^2 = 2 * u0 * v0  : y2_2uv_0
               ... = 2 * v0 * u0  : by ac_refl,
          refine case_b x_y gmp1 s t Hs Ht v0 u0 uvx_pos0.2.1 uvx_pos0.1 (coprime.symm u_v0) u2_v2_x2' y2_2uv' even_u0
        },
        { exact case_b x_y gmp1 s t Hs Ht u0 v0 uvx_pos0.1 uvx_pos0.2.1 u_v0 u2_v2_x2_0 y2_2uv_0 even_v0 },
      }
    }
  end
end fermat


lemma no_solutions' : ∀ x, ¬(∃ y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^4 = y^4 + z^2) :=
begin
  intro x0,
  refine nat.strong_induction_on x0 _,
  intros x iH a,
  rcases a with ⟨y,z,x_pos,y_pos,z_pos,fmt⟩,
  rcases descent x y z fmt ⟨x_pos,y_pos,z_pos⟩
    with ⟨x',y',z',x'_pos,y'_pos,z'_pos,x'_lt_x,fmt'⟩,
  exact iH x' x'_lt_x ⟨y',z',x'_pos,y'_pos,z'_pos,fmt'⟩,
end

theorem no_solutions : ¬(∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^4 = y^4 + z^2) :=
  not_exists_of_forall_not no_solutions'

theorem fermat4 : ¬(∃ a b c, 0 < a ∧ 0 < b ∧ 0 < c ∧ a^4 + b^4 = c^4) := begin
  intros H,
  rcases H with ⟨a,b,c,a_pos,b_pos,c_pos,fmt⟩,
  have fmt' : c^4 = a^4 + (b^2)^2 :=
  calc c^4 = a^4 + b^4  : fmt.symm
       ... = a^4 + (b^2)^2  : by rw square_twice,
  have b2_pos := pos_pow_of_pos 2 b_pos,
  exact no_solutions ⟨c,a,b^2,c_pos,a_pos,b2_pos,fmt'⟩
end
