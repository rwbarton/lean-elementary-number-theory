import data.nat.prime
import data.pnat

import data.nat.exactly_divides

open nat

namespace order

section raw_order

variables (p : ℕ) (hp : p > 1)

protected def order_core : Π (n : ℕ), n > 0 → {r // p^r ∣∣ n}
| 0       := λ n_pos, absurd n_pos dec_trivial
| n@(k+1) := λ n_pos,
  have n / p < n, from div_lt_self n_pos hp,
  if h : p ∣ n
  then
    have p * (n / p) = n, from nat.mul_div_cancel' h,
    let ⟨s, hs⟩ :=
      order_core (n / p)
        (pos_of_mul_pos_left (this.symm ▸ n_pos : 0 < p * (n / p)) dec_trivial)
    in ⟨succ s, this ▸ (exactly_divides_succ (hp.trans dec_trivial)).mp hs⟩
  else ⟨0, (exactly_divides_zero (hp.trans dec_trivial)).mp h⟩

def order (n : ℕ) (n_pos : n > 0) : ℕ := (order.order_core p hp n n_pos).val

lemma exactly_divides_order (n : ℕ) (n_pos : n > 0) :
  p^(order p hp n n_pos) ∣∣ n :=
(order.order_core p hp n n_pos).property


end raw_order

/- XXX comments -/

instance : has_dvd ℕ+ := ⟨λ a b, a.val ∣ b.val⟩

def 𝓟 := {p : ℕ // prime p}
notation `PP` := 𝓟

def 𝓟.gt_one (p : 𝓟) : p.val > 1 := p.property.gt_one
def 𝓟.pos (p : 𝓟) : p.val > 0 := p.property.pos

instance : has_coe 𝓟 ℕ+ := ⟨λ p, ⟨p.val, p.pos⟩⟩

def ord (p : 𝓟) (n : ℕ+) : ℕ := order p p.gt_one n n.property
def exactly_divides_ord {p : 𝓟} {n : ℕ+} : p^(ord p n) ∣∣ n :=
exactly_divides_order p p.gt_one n n.property
def exactly_divides_iff_ord {p : 𝓟} {r : ℕ} {n : ℕ+} : ord p n = r ↔ p^r ∣∣ n :=
iff.intro
  (λ e, e ▸ exactly_divides_ord)
  (exactly_divides_unique exactly_divides_ord)

variable {p : 𝓟}

-- Recursion (though we prove them in a round-about fashion)

lemma ord_not_div {n : ℕ+} : ¬(↑p ∣ n) ↔ ord p n = 0 :=
(exactly_divides_zero p.pos).trans exactly_divides_iff_ord.symm

lemma ord_div {n : ℕ+} : ord p (p * n) = succ (ord p n) :=
exactly_divides_iff_ord.mpr
((exactly_divides_succ p.pos).mp exactly_divides_ord)

-- Multiplicative

lemma ord_one : ord p 1 = 0 :=
exactly_divides_iff_ord.mpr (exactly_divides_one p.property)

lemma ord_mul (a b : ℕ+) : ord p (a * b) = ord p a + ord p b :=
exactly_divides_iff_ord.mpr
(exactly_divides_mul p.property
  exactly_divides_ord exactly_divides_ord)

lemma ord_ppow {k : ℕ} {a : ℕ+} : ord p (pnat.pow a k) = k * ord p a :=
exactly_divides_iff_ord.mpr
(exactly_divides_pow p.property exactly_divides_ord)

lemma ord_pow {k : ℕ} {a : ℕ+} : ord p (a^k) = k * ord p a :=
have pnat.pow a k = a^k, from (pnat.coe_nat_coe _).symm, this ▸ ord_ppow

-- Gcd

def pgcd (a b : ℕ+) : ℕ+ := ⟨gcd a b, gcd_pos_of_pos_left b a.pos⟩

lemma ord_pgcd {a b : ℕ+} : ord p (pgcd a b) = min (ord p a) (ord p b) :=
exactly_divides_iff_ord.mpr
(exactly_divides_gcd
  exactly_divides_ord exactly_divides_ord)

lemma ord_gcd {a b : ℕ+} : ord p (gcd a b) = min (ord p a) (ord p b) :=
have pgcd a b = gcd a b, from (pnat.coe_nat_coe _).symm, this ▸ ord_pgcd

end order
