/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

/-
# Erdős Problem 755
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Card
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.MetricSpace.Defs

@[expose] public section

open Filter
open scoped Asymptotics EuclideanGeometry Finset

namespace MathlibExt.Geometry.ErdosProblem755Wanted

/-! Source record `FC-ErdosProblem755`, ported from FormalConjectures
`ErdosProblems/755.lean` and checked against erdosproblems.com/755.
The equilateral-triangle counting API is inlined from FC
(`IsEquilateralTriangle`, `IsUnitEquilateralTriangle`,
`IsAnySizeEquilateralTriangle`, `unitEquilateralTriangleCount`,
`anySizeEquilateralTriangleCount`, `TUnit`, `TAnySize`; absent from
pinned Mathlib). `test` lemmas are not ported. The upstream
`answer(True)` is dropped. Status: resolved true by [CDL25b]. This module
states the result but does not prove it; an external Lean proof is linked in
the registry. -/

/-- Three points with all pairwise distances equal to `side`. -/
def IsEquilateralTriangle {d : ℕ} (side : ℝ)
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  T.card = 3 ∧ ∀ p ∈ T, ∀ q ∈ T, p ≠ q → dist p q = side

/-- A unit equilateral triangle. -/
def IsUnitEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  IsEquilateralTriangle 1 T

/-- An equilateral triangle of positive side length. -/
def IsAnySizeEquilateralTriangle {d : ℕ}
    (T : Finset (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ side : ℝ, 0 < side ∧ IsEquilateralTriangle side T

/-- Unit equilateral triangles spanned by a point set. -/
noncomputable def unitEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsUnitEquilateralTriangle T).card

/-- Positive-side equilateral triangles spanned by a point set. -/
noncomputable def anySizeEquilateralTriangleCount (d : ℕ)
    (P : Finset (EuclideanSpace ℝ (Fin d))) : ℕ :=
  open scoped Classical in
  ((P.powersetCard 3).filter fun T => IsAnySizeEquilateralTriangle T).card

/-- Max unit triangles over `n`-point sets in `ℝ^d`. -/
noncomputable def TUnit (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ unitEquilateralTriangleCount d P = m}

/-- Max any-size triangles over `n`-point sets in `ℝ^d`. -/
noncomputable def TAnySize (d n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin d)),
    P.card = n ∧ anySizeEquilateralTriangleCount d P = m}

/-- `(1/27 + o(1)) n³` unit triangles in `ℝ⁶`, and the any-size form. -/
def conjecture : Prop :=
  (∃ o : ℕ → ℝ,
    o =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n in atTop,
        (TUnit 6 n : ℝ) ≤ ((1 / 27 : ℝ) + o n) * (n : ℝ) ^ 3) ∧
  ((fun n : ℕ => (TAnySize 6 n : ℝ)) ~[atTop]
    (fun n : ℕ => (1 / 27 : ℝ) * (n : ℝ) ^ 3))

/--
Resolved true: Resolved externally by Clemen, Dumitrescu, and Liu. This repository records the
statement, not an internal proof; a separate pinned Lean proof is cited below. Source: Felix
Christian Clemen, Adrian Dumitrescu, and Dingyuan Liu, The number of regular simplices in higher
dimensions, arXiv:2507.19841 (2025), https://arxiv.org/abs/2507.19841. Moved from
`OpenConjectures/Geometry/ErdosProblem755`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem755Wanted
