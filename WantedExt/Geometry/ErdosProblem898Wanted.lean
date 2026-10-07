/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 898
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Geometry.TwoD
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Independent

@[expose] public section

open Affine EuclideanGeometry
open scoped EuclideanGeometry EuclideanSpace

namespace MathlibExt.Geometry.ErdosProblem898Wanted

/-! Source record `FC-ErdosProblem898`, ported from FormalConjectures
`ErdosProblems/898.lean` (`theorem erdos_898`) and checked against
erdosproblems.com/898. `ℝ²` is MathlibExt's notation; affine lines,
independence, convex hulls, and orthogonality are Mathlib's. The
`answer(...)` wrapper is elaborated away. Status: resolved true externally by
Mordell and Barrow. This module states the inequality but does not prove it;
a pinned external Lean proof is linked in the registry. -/

/-- The Erdős–Mordell inequality: for an interior point `P`, `PA + PB + PC ≥
2(PM + PN + PL)` where `M, N, L` are the feet of perpendiculars. -/
def conjecture : Prop :=
  ∀ (A B C P L M N : ℝ²) (_hABC : AffineIndependent ℝ ![A, B, C])
    (_hP : P ∈ interior (convexHull ℝ ({A, B, C} : Set ℝ²)))
    (_hN : N ∈ line[ℝ, A, B])
    (_hPN : line[ℝ, P, N].direction ⟂ line[ℝ, A, B].direction)
    (_hM : M ∈ line[ℝ, B, C])
    (_hPM : line[ℝ, P, M].direction ⟂ line[ℝ, B, C].direction)
    (_hL : L ∈ line[ℝ, C, A])
    (_hPL : line[ℝ, P, L].direction ⟂ line[ℝ, C, A].direction),
    dist P A + dist P B + dist P C ≥ 2 * (dist P M + dist P N + dist P L)

/--
Resolved true: Resolved externally by L. J. Mordell and D. F. Barrow. This repository records
the statement, not an internal proof; a pinned external Lean proof is cited below. Source: Paul
Erdős, L. J. Mordell, and David F. Barrow, Problem 3740, American Mathematical Monthly 44
(1937), 252–254, https://doi.org/10.2307/2300713. Moved from
`OpenConjectures/Geometry/ErdosProblem898`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Geometry.ErdosProblem898Wanted
