/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# Consecutive polynomial families

This module packages the notion of a finite family of integer-coefficient polynomials whose
successive members differ by one.

Source: Jean-Marie De Koninck and Matthieu Moineau, *Consecutive Integers Divisible by a Power
of their Largest Prime Factor*,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/DeKoninck/dek22.tex>.

JIS concept: `jis_sem_426da1032b58ae06add015fc`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- A family `L₀, …, Lₖ₋₁` of polynomials in `ℤ[X]` is consecutive when
`L_(i+1) - L_i = 1` for every `i < k - 1`. -/
def IsConsecutivePolynomialFamily (k : ℕ) (L : Fin k → Polynomial ℤ) : Prop :=
  ∀ i : Fin k, ∀ h : i.val + 1 < k, L ⟨i.val + 1, h⟩ - L i = 1

end

end MetaMathlibExt
