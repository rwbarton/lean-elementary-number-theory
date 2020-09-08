/- Additional lemmas on modular equality. -/

import data.nat.modeq

open nat

namespace modeq
  variables {a r n k : ℕ}
  lemma mod_of_modeq : a ≡ r [MOD n] → r < n → a % n = r :=
    begin
      rw modeq,
      intros e l,
      have h : r % n = r := mod_eq_of_lt l,
      rw [e, h]
    end

  lemma rep_of_modeq : a ≡ r [MOD n] → r < n → ∃ q : ℕ, a = n * q + r :=
    begin
      intros e l,
      existsi (a / n),
      apply symm,
      rw [add_comm, ←(mod_of_modeq e l)],
      apply mod_add_div
    end

  lemma n_mod_n : n ≡ 0 [MOD n] :=
    begin rw [modeq, mod_self, zero_mod] end

  lemma modeq_of_rep_0 : n*k + r ≡ 0*k + r [MOD n] :=
    modeq.modeq_add (modeq.modeq_mul_right k n_mod_n) (modeq.refl r)
  lemma modeq_of_rep : n*k + r ≡ r [MOD n] :=
    begin
      apply (modeq.trans modeq_of_rep_0 _),
      simp
    end
end modeq
