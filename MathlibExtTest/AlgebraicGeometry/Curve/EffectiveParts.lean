module

public import MathlibExt.AlgebraicGeometry.Curve.EffectiveParts

@[expose] public section

namespace CurveDivisor

variable {C : Type*} [DecidableEq C]

example (D : CurveDivisor C) (P : C) : divZeros D P = max (D P) 0 := by
  simp

example (D : CurveDivisor C) (P : C) : divPoles D P = max (-(D P)) 0 := by
  simp

example (D : CurveDivisor C) : 0 ≤ divZeros D :=
  divZeros_nonneg D

example (D : CurveDivisor C) : 0 ≤ divPoles D :=
  divPoles_nonneg D

example (D : CurveDivisor C) : divZeros D - divPoles D = D := by
  simp

example (P : C) : divZeros (Finsupp.single P (5 : ℤ) : CurveDivisor C) P = 5 := by
  simp

example (P : C) : divPoles (Finsupp.single P (5 : ℤ) : CurveDivisor C) P = 0 := by
  simp

example (P : C) : divZeros (Finsupp.single P (-7 : ℤ) : CurveDivisor C) P = 0 := by
  simp

example (P : C) : divPoles (Finsupp.single P (-7 : ℤ) : CurveDivisor C) P = 7 := by
  simp

end CurveDivisor
