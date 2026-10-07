/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A four-function HRT configuration
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Analysis.FourFunctionHRTWanted

/-- Modulation by frequency one. -/
noncomputable def modulationOne (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- The four functions `g(x)`, `g(x - 1)`, `g(x - √2)`, and
`exp(2πix) g(x)` are linearly independent in `L²(ℝ)` for every nonzero `g ∈ L²(ℝ)`. -/
def conjecture : Prop :=
  ∀ g : ℝ → ℂ, MemLp g 2 volume → ¬(g =ᵐ[volume] 0) →
    ∀ c₀ c₁ c₂ c₃ : ℂ,
      (fun x ↦ c₀ * g x + c₁ * g (x - 1) + c₂ * g (x - Real.sqrt 2) +
        c₃ * modulationOne x * g x) =ᵐ[volume] 0 →
      c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0

/--
Resolved true: Demeter (Math. Res. Lett. 17 (2010), arXiv:1006.0732, Thm 1.4(b)) proved HRT for
(1,3) configurations when one spacing parameter is rational; Liu (J. Fourier Anal. Appl. 2019,
arXiv:1609.08230, Thm 1.1(b)) states it for {(0,0),(a,0),(b,0),(0,1)}, which with a = 1, b =
sqrt2 is exactly this target. Source: Ciprian Demeter, Linear independence of time frequency
translates for special configurations, Math. Res. Lett. 17 (2010) 761-779, arXiv:1006.0732,
https://arxiv.org/abs/1006.0732; Wencai Liu, Proof of the HRT conjecture for almost every (1,3)
configuration, J. Fourier Anal. Appl. (2019), arXiv:1609.08230,
https://arxiv.org/abs/1609.08230. Moved from `OpenConjectures/Analysis/FourFunctionHRT`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.FourFunctionHRTWanted
