import data.multiset
import data.list
import data.nat.prime
import ent.order


open order
open list
open nat

local notation `prod` := list.prod

/-
set_option pp.all true

variables {x : ℕ} {lx : list ℕ}
set_option pp.all true
#check prod (map succ (x :: lx))
-/

-- def prime_factorization := multiset PP

section

-- factors facts

lemma factors_lemma_nil : ∀ (n : ℕ), factors n = [] → n = 0 ∨ n = 1
| 0 h := or.inl rfl
| 1 h := or.inr rfl
| n@(k+2) h := absurd h dec_trivial

lemma factors_lemma_cons : ∀ (n : ℕ) (m : ℕ) (fs' : list ℕ),
  factors n = m :: fs' → n ≠ 1 ∧ min_fac n = m ∧ factors (n / min_fac n) = fs'
| 0 _ _ h := absurd h dec_trivial
| 1 _ _ h := absurd h dec_trivial
| n@(k+2) m fs' hn := ⟨dec_trivial, cons.inj hn⟩

-- wouldn't it be easier to just start from scratch
-- almost certainly
def factors_as_primes :
  Π (fs : list ℕ) (n : ℕ) (h : factors n = fs),
    {l : list PP // l.map subtype.val = fs}
| [] _ _ := ⟨[], rfl⟩
| (m :: fs') n h :=
begin
  rcases factors_lemma_cons n m fs' h with ⟨n_ne_1, hm, hfs'⟩,
  let r := factors_as_primes fs' (n / min_fac n) hfs',
  have prime_m := min_fac_prime n_ne_1, rw hm at prime_m,
  existsi subtype.mk m prime_m :: r.val,
  transitivity list.cons m (map subtype.val (r.val)),
  apply map_cons subtype.val,
  rw r.property
end

lemma factors_as_factorization :
  ∀ (fs : list ℕ) (n : ℕ) (h : factors n = fs), n > 0 → prod fs = n
| [] n h n_pos := eq.symm $
  (factors_lemma_nil n h).resolve_left
  (λ e, absurd (calc 0 = n : e.symm ... > 0 : n_pos) dec_trivial)
| (m :: fs') n h n_pos :=
begin
  rcases factors_lemma_cons n m fs' h with ⟨_, hm, hfs'⟩,
  have : min_fac n ∣ n := min_fac_dvd n,
  rw hm at this hfs',
  let n' := n / m,
  have p : m * n' = n := nat.mul_div_cancel' this,
  have : n' > 0 := pos_of_mul_pos_left (p.symm ▸ n_pos : 0 < m * n') dec_trivial,
  have r' := factors_as_factorization fs' n' hfs' this,
  rw ←r' at p, rwa prod_cons
end

def factors_prime_factorization (n : ℕ) (n_pos : n > 0) :
  {l : list PP // (l.map subtype.val).prod = n} :=
let ⟨l, h⟩ := factors_as_primes (factors n) n rfl in
⟨l, h.symm ▸ factors_as_factorization (factors n) n rfl n_pos⟩

-- or just
lemma factors_is_factorization (n : ℕ) (n_pos : n > 0) :
  (factors n).prod = n :=
factors_as_factorization (factors n) n rfl n_pos

-- ∀ m ∈ factors n, prime m

/-
instance {α β : Sort*} [has_coe α β] : has_coe (list α) (list β) := ⟨map coe⟩

lemma coe_cons {α β : Sort*} [has_coe α β] (hd : α) (tl : list α) :
  (↑(@list.cons α hd tl)) = (@list.cons β hd tl) := sorry
@[reducible] def prodN := @list.prod ℕ
-/

def p_to_pnat (p : PP) : ℕ+ := ↑p

lemma ord_of_prod (l : list PP) (p : PP) :
  ord p (prod (l.map p_to_pnat)) = count p l :=
begin
  induction l with l_hd l_tl ih,
  { exact ord_one },
  { by_cases h : p = l_hd,

    exact calc
      ord p (prod (map p_to_pnat (l_hd :: l_tl)))
          = ord p (prod (p_to_pnat l_hd :: (l_tl.map p_to_pnat)))  : rfl
      ... = ord p (p_to_pnat l_hd * prod (l_tl.map p_to_pnat))     : by rw prod_cons
      ... = ord p (p_to_pnat p * prod (l_tl.map p_to_pnat))  : by rw ←h
      ... = ord p (p * prod (l_tl.map p_to_pnat))  : rfl
      ... = succ (ord p (prod (l_tl.map p_to_pnat)))  : by rw ord_div
      ... = succ (count p l_tl)                    : by rw ih
      ... = count p (p :: l_tl)                    : by simp [count_cons]
      ... = count p (l_hd :: l_tl)                 : by rw h,

    let q := l_hd,
    have : ord p q = 0 :=
      ord_not_div.mp
        ((prime.coprime_iff_not_dvd p.property).mp
         ((coprime_primes p.property q.property).mpr (mt subtype.eq h))),
    exact calc
      ord p (prod (map p_to_pnat (l_hd :: l_tl)))
          = ord p (prod (p_to_pnat l_hd :: (l_tl.map p_to_pnat)))  : rfl
      ... = ord p (p_to_pnat l_hd * prod (l_tl.map p_to_pnat))     : by rw prod_cons
      ... = ord p (p_to_pnat q * prod (l_tl.map p_to_pnat))  : rfl
      ... = ord p (q * prod (l_tl.map p_to_pnat))  : rfl
      ... = ord p q + ord p (prod (l_tl.map p_to_pnat))  : by rw ord_mul
      ... = ord p (prod (l_tl.map p_to_pnat))      : by simp [this]
      ... = count p l_tl                           : by rw ih
      ... = count p (l_hd :: l_tl)                 : by simp [count_cons, h]
  }
end

lemma ord_of_prod_multi (l : multiset PP) (p : PP) :
  ord p ((l.map p_to_pnat).prod) = l.count p :=
begin
  revert l, apply quot.ind, intro l,
  exact calc
    ord p ((multiset.map p_to_pnat ↑l).prod)
        = ord p (prod (l.map p_to_pnat))  : by simp
    ... = count p l                       : by rw ord_of_prod
    ... = multiset.count p ↑l  : by simp
end

lemma uniq (l1 l2 : multiset PP) :
  (l1.map p_to_pnat).prod = (l2.map p_to_pnat).prod → l1 = l2 :=
begin
  intro h,
  rw multiset.ext, intro p,
  rw [←ord_of_prod_multi, ←ord_of_prod_multi, h]
end


-- old weird stuff below

/-

def orders := PP →₀ ℕ

-- Yuck
lemma big_prime (p : PP) (n : ℕ+) : (p : ℕ) > n → ord p n = 0 :=
λ p_big, ord_not_div.mp (λ d, not_le_of_gt p_big (nat.le_of_dvd n.pos d))

lemma big_prime_2 (p : PP) (n : ℕ+) : ord p n ≠ 0 → (p : ℕ) ≤ n :=
le_of_not_gt ∘ mt (big_prime p n)

lemma val_is_injective {α : Type} {p : α → Prop} :
  injective (subtype.val : subtype p → α) :=
λ a1 a2 e, subtype.eq e

-- euclid's lesser known theorem
lemma finitely_many_primes (n : ℕ) : finite {p : PP | ↑p ≤ n} :=
@finite_preimage PP ℕ {i : ℕ | i ≤ n} (λ p, p.val) val_is_injective (finite_le_nat n)

lemma primes_contained (n : ℕ+) : {p | ord p n ≠ 0} ⊆ {p : PP | (p : ℕ) ≤ n} :=
swap big_prime_2 n


def prime_orders (n : ℕ+) : orders :=
⟨λ p, ord p n, finite_subset (finitely_many_primes n) (primes_contained n)⟩


-- Multiplying

noncomputable def product : orders → ℕ+ :=
λ os, finsupp.prod os (λ p r, pnat.pow p r)

-/

end 
