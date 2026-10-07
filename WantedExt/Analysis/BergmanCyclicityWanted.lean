/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
AMR-022-8010: if f and 1/f are in the Bergman space A^2,
does it follow that Pf = {polynomial multiples of f} is dense in A^2?

Gap: the record also asks a generalization (to other spaces);
only the first part (A^2 cyclicity) is formalized here.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

namespace MathlibExt.Analysis.BergmanCyclicityWanted

/-! Source record `AMR-022-8010`. -/
open MeasureTheory

/-- The open unit disc in `ℂ`. -/
def Disc : Set ℂ := {z | ‖z‖ < 1}

/-- Bergman space `A^2` membership: analytic on the disc and square-integrable. -/
def Bergman (f : ℂ → ℂ) : Prop :=
  AnalyticOn ℂ f Disc ∧ MemLp f 2 (volume.restrict Disc)

/-- Pointwise reciprocal. -/
noncomputable def Inv (f : ℂ → ℂ) : ℂ → ℂ := fun z => (f z)⁻¹

/-- Polynomial multiples of `f` are dense in `A^2`: every Bergman function
is an `L^2` limit of `p * f` over polynomials `p`. -/
def Dense (f : ℂ → ℂ) : Prop :=
  ∀ g : ℂ → ℂ, Bergman g → ∀ ε : ENNReal, 0 < ε →
    ∃ p : Polynomial ℂ, eLpNorm (fun z => p.eval z * f z - g z) 2 (volume.restrict Disc) < ε

/-- [AMR-022-8010] If `f` and `1 / f` are both in the Bergman space `A^2` (with `f` zero-free on the disc, so the reciprocal is genuine and not Lean's totalized inverse), then the polynomial multiples of `f` are dense in `A^2`. -/
def conjecture : Prop :=
  ∀ f : ℂ → ℂ, Bergman f → Bergman (Inv f) →
    (∀ z ∈ Disc, f z ≠ 0) → Dense f

/--
Resolved false: Borichev and Hedenmalm (J. Amer. Math. Soc. 10 (1997) 761-796) constructed
invertible but non-cyclic functions in the unweighted Bergman spaces B^p(D), 0<p<inf; for p=2
this gives f with f, 1/f in A^2 whose polynomial multiples are not dense, as stated in
Borichev-Hedenmalm-Volberg (arXiv:math/0304318). Source: Alexander Borichev, Haakan Hedenmalm
and Alexander Volberg, Large Bergman spaces: invertibility, cyclicity, and subspaces of
arbitrary index, arXiv:math/0304318 (2003), https://arxiv.org/abs/math/0304318. Moved from
`OpenConjectures/Analysis/BergmanCyclicity`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Analysis.BergmanCyclicityWanted
