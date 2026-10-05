/-
# Tests for linear sums of Legendre symbols
-/
module

public import MathlibExt.NumberTheory.LegendreSymbol.LinearSum

@[expose] public section

open scoped BigOperators

example (p : ℕ) [Fact p.Prime] (hpodd : Odd p) (b c : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
    ∑ ℓ ∈ Finset.range p, legendreSym p (b * (ℓ : ℤ) + c) = 0 :=
  legendreSym.sum_linear_eq_zero p hpodd b c hb

end
