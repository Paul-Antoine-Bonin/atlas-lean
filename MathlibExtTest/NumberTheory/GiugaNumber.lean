module

public import MathlibExt.NumberTheory.GiugaNumber

namespace MetaMathlibExt

@[expose] public section

example (n : ℕ) : IsGiugaNumber n ↔
    2 ≤ n ∧ ¬ Nat.Prime n ∧ ∀ p, Nat.Prime p → p ∣ n → p ∣ (n / p - 1) := Iff.rfl

example : ¬ IsGiugaNumber 0 := by
  simp [IsGiugaNumber]

example : ¬ IsGiugaNumber 1 := by
  simp [IsGiugaNumber]

#print axioms IsGiugaNumber

end

end MetaMathlibExt
