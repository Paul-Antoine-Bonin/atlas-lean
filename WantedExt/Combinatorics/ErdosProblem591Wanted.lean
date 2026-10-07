/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 591
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.SetTheory.Cardinal.SimpleGraph
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

open Cardinal Ordinal

universe u

namespace MathlibExt.Combinatorics.ErdosProblem591Wanted

/-! Source record `FC-ErdosProblem591`, ported from FormalConjectures
`ErdosProblems/591.lean` (`theorem erdos_591`) and checked against
erdosproblems.com/591. `OrdinalCardinalRamsey` is MathlibExt's (ported from
FC's `FormalConjecturesForMathlib`). The `answer(True)` wrapper is elaborated
to a direct proposition. Status: resolved true (Schipperus [Sc10] and Darby,
independently). -/

/-- Every red/blue colouring of `K_{ω^ω²}` has a red `K_α` or a blue `K₃`. -/
def conjecture : Prop :=
  OrdinalCardinalRamsey (ω ^ ω ^ 2 : Ordinal.{u}) (ω ^ ω ^ 2 : Ordinal.{u}) (3 : Cardinal.{u})

/--
Resolved true: Resolved true (Schipperus [Sc10] and Darby, independently), per
erdosproblems.com/591. Source: Schipperus [Sc10] and Darby, independently, per
erdosproblems.com/591, https://www.erdosproblems.com/591. Moved from
`OpenConjectures/Combinatorics/ErdosProblem591`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem591Wanted
