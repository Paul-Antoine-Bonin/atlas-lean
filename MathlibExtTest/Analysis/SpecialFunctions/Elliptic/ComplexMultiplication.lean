module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.ComplexMultiplication

@[expose] public section

namespace PeriodPair

variable (L : PeriodPair)

example : (0 : ℂ) ∈ L.endomorphismRing := by
  simp

example : (1 : ℂ) ∈ L.endomorphismRing := by
  simp

example : L.IsProperIdeal L.endomorphismRing := by
  simp

end PeriodPair
