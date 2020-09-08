import data.nat.modeq

import ent.modeq
import ent.parity

open nat

namespace gcd
  theorem gcd_row_op (a b k : ℕ) : gcd a b = gcd a (a * k + b) :=
    have mods : b ≡ a * k + b [MOD a] := modeq.modeq_of_rep.symm,
    calc gcd a b = gcd (b % a) a            : by rw gcd_rec
         ...     = gcd ((a * k + b) % a) a  : begin unfold modeq at mods, rw mods end
         ...     = gcd a (a * k + b)        : by rw ←gcd_rec

  lemma sum_difference_sum {a c : ℕ} (H : a ≤ c) : (c - a) + (c + a) = 2 * c :=
    calc (c - a) + (c + a) = (c - a) + (a + c)  : by rw add_comm a c
         ...               = ((c - a) + a) + c  : by rw add_assoc
         ...               = (a + (c - a)) + c  : by rw add_comm (c - a) a
         ...               = c + c              : by rw add_sub_of_le H
         ...               = 2 * c              : by rw two_mul

  lemma sum_difference_difference {a c : ℕ} (H : a ≤ c) : (c + a) - (c - a) = 2 * a :=
    calc (c + a) - (c - a) = (a + c) - (c - a)  : by rw add_comm c a
         ...               = a + (c - (c - a))  : by rw nat.add_sub_assoc (sub_le c a) a
         ...               = a + a              : by rw nat.sub_sub_self H
         ...               = 2 * a              : by rw two_mul

  lemma sum_difference_of_coprime (a c : ℕ) (H : a ≤ c) : coprime a c → gcd (c - a) (c + a) ∣ 2 :=
    begin
      intros ac,
      let g := gcd (c - a) (c + a),
      cases gcd_dvd (c - a) (c + a) with gminus gplus,
      have g2c : g ∣ 2 * c := by rw ←sum_difference_sum H; apply dvd_add; assumption,
      have : c - a ≤ c + a := trans (nat.sub_le c a) (le_add_right c a),
      have g2a : g ∣ 2 * a := by rw ←sum_difference_difference H; apply nat.dvd_sub this; assumption,
      have g2ac : g ∣ gcd (2 * a) (2 * c) := dvd_gcd g2a g2c,
      rw [gcd_mul_left 2 a c, ac.gcd_eq_one] at g2ac,
      exact g2ac
    end

  lemma sum_difference_of_coprime_odd (a c : ℕ) (H : a ≤ c) : coprime a c → odd a → odd c → gcd (c - a) (c + a) = 2 :=
    begin
      intros ac oa oc,
      apply nat.dvd_antisymm,
      { exact sum_difference_of_coprime a c H ac },
      { exact
         dvd_gcd (even_iff_two_dvd.mp (odd_minus_odd_is_even H oa oc))
                 (even_iff_two_dvd.mp (odd_plus_odd_is_even oc oa))
      }
    end

  lemma coprime_iff_squares_coprime {x y : ℕ} : coprime (x^2) (y^2) ↔ coprime x y :=
    iff.intro
      (λ H, coprime.coprime_dvd_left self_divides_square
            (coprime.coprime_dvd_right self_divides_square H))
      (coprime.pow 2 2)
end gcd


lemma coprime_square_product {x y z : ℕ} : x * y = z^2 → coprime x y →
                                           ∃ x1 y1, x = x1^2 ∧ y = y1^2 :=
  begin
    intros,
    rw nat.pow_two at a,
    cases eq_zero_or_pos x with xzero xpos,
    { -- x = 0
      have y1 : y = 1 :=
        begin simp [xzero, coprime, gcd_zero_left] at a_1, exact a_1 end,
      existsi [0, 1],
      split,
      { rw xzero, refl }, { rw y1, refl }
    },
    -- x > 0
    have H : x ∣ z * z := begin rw ←a, apply dvd_mul_right end,
    cases exists_eq_prod_and_dvd_and_dvd H with x1 H1,
    cases H1 with x2,
    cases H1_h,
    cases H1_h_right,
    existsi [x1, (z/x1)],
    let y1 := z / x1,
    let y2 := z / x2,
    have xyz1 : x1 * y1 = z :=
      begin
        show x1 * (z / x1) = z,
        apply nat.mul_div_cancel',
        exact H1_h_right_left
      end,
    have xyz2 : x2 * y2 = z :=
      begin
        show x2 * (z / x2) = z,
        apply nat.mul_div_cancel',
        exact H1_h_right_right
      end,
    have y1y2 : y = y1 * y2 :=
      begin
        show y = (z / x1) * (z / x2),
        rw [←nat.mul_left_inj xpos, a, H1_h_left],
        have res : z * z = x1 * x2 * (z / x1 * (z / x2)) :=
          calc z * z = (x1 * (z / x1)) * z      : by rw nat.mul_div_cancel' H1_h_right_left
               ...   = (x1 * (z / x1)) * (x2 * (z / x2)) : by rw nat.mul_div_cancel' H1_h_right_right
               ...   = x1 * ((z / x1) * (x2 * (z / x2))) : by rw mul_assoc
               ...   = x1 * (((z / x1) * x2) * (z / x2)) : by rw mul_assoc
               ...   = x1 * ((x2 * (z / x1)) * (z / x2)) : by rw mul_comm (z / x1) x2
               ...   = x1 * (x2 * ((z / x1) * (z / x2))) : by rw mul_assoc
               ...   = (x1 * x2) * ((z / x1) * (z / x2)) : by rw mul_assoc,
        exact res
      end,
    have xeq : x1 = x2 :=
      begin
        rw [H1_h_left, y1y2] at a_1,
        have cx1y2 : gcd x1 y2 = 1 := a_1.coprime_mul_right.coprime_mul_left_right,
        have cx2y1 : gcd x2 y1 = 1 := a_1.coprime_mul_left.coprime_mul_right_right,
        have g2 : gcd x z = x2 :=
          begin
            rw [H1_h_left, ←xyz2, mul_comm x2 y2],
            calc gcd (x1 * x2) (y2 * x2) = gcd x1 y2 * x2 : by rw gcd_mul_right
                 ...                     = 1 * x2         : by rw cx1y2
                 ...                     = x2             : by simp
          end,
        have g1 : gcd x z = x1 :=
          begin
            rw [H1_h_left, ←xyz1],
            calc gcd (x1 * x2) (x1 * y1) = x1 * gcd x2 y1 : by rw gcd_mul_left
                 ...                     = x1 * 1         : by rw cx2y1
                 ...                     = x1             : by simp
          end,
        exact (symm g1).trans g2
      end,
    split,
    { rw [nat.pow_two], rwa ←xeq at H1_h_left },
    { have yeq : y1 = y2 := begin show z / x1 = z / x2, rw xeq end,
      rw [nat.pow_two],
      calc y = y1 * y2                : y1y2
           ... = y1 * y1              : by rw yeq
           ... = (z / x1) * (z / x1)  : by simp
    }
  end

/-

x y = z^2, x _|_ y 

x = z1 z2
y = (z / z1) (z / z2)

If p divides z2 more times than z1 then p will also divide z / z1 at least once,
and then z / z1 and z2 will not be relatively prime.

gcd(z2, z/z1) = 1 => gcd(z1 z2, z) = z1
gcd(z1, z/z2) = 1 => gcd(z1 z2, z) = z2

-/
