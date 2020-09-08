namespace xor

protected def mk {p q : Prop} : p ∨ q → ¬ (p ∧ q) → xor p q
| (or.inl Hp) Hpq := or.inl ⟨Hp, λ Hq, Hpq ⟨Hp,Hq⟩⟩
| (or.inr Hq) Hpq := or.inr ⟨Hq, λ Hp, Hpq ⟨Hp,Hq⟩⟩

protected def resolve_left {p q : Prop} : xor p q → (¬p ↔ q) := λ x,
  iff.intro (λ Hp, (or.resolve_left x (mt and.left Hp)).left)
            (λ Hq, (or.resolve_left x (mt and.right (not_not_intro Hq))).right)

protected def resolve_right {p q : Prop} : xor p q → (¬q ↔ p) := λ x,
  iff.intro (λ Hq, (or.resolve_right x (mt and.left Hq)).left)
            (λ Hp, (or.resolve_right x (mt and.right (not_not_intro Hp))).right)

end xor
