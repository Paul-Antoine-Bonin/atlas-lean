/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 63
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Circumference
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.ENat.Basic

@[expose] public section

open SimpleGraph

namespace MathlibExt.GraphTheory.ErdosProblem63Wanted

/-! Source record `FC-ErdosProblem63`, ported from FormalConjectures
`ErdosProblems/63.lean` (`theorem erdos_63`) and checked against
erdosproblems.com/63. `cycleLengths` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`); `chromaticNumber` is Mathlib's. The
`answer(True)` wrapper is elaborated to a direct proposition. Status:
resolved true (Mihók–Erdős conjecture, solved via Liu–Montgomery [LiMo20]). -/

/-- Infinite chromatic number forces `2^n` cycle lengths infinitely often. -/
def conjecture : Prop :=
  ∀ {V : Type*} (G : SimpleGraph V), G.chromaticNumber = ⊤ →
    ∀ N : ℕ, ∃ n ≥ N, 2 ^ n ∈ G.cycleLengths

/--
Resolved true: Resolved true (Liu–Montgomery [LiMo20]), per erdosproblems.com/63. Source:
Liu–Montgomery [LiMo20], per erdosproblems.com/63, https://www.erdosproblems.com/63. Moved from
`OpenConjectures/GraphTheory/ErdosProblem63`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.GraphTheory.ErdosProblem63Wanted
