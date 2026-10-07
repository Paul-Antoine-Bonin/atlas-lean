/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Realizing countable dense sets as fibers of an entire function (AMR-022-2031)

Erdos asked whether, for any two countable dense plane sets `A` and `B`,
some entire function takes values in `B` exactly on `A`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Set.Countable
public import Mathlib.Topology.Defs.Basic

@[expose] public section

namespace MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted

/-! Source record `AMR-022-2031`. -/

/-- [AMR-022-2031] For any two countable dense sets `A`, `B` in the plane,
there is an entire function `f` with `f z ∈ B ↔ z ∈ A` for all `z`. -/
def conjecture : Prop :=
  ∀ A B : Set ℂ, A.Countable → Dense A → B.Countable → Dense B →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f Set.univ ∧ ∀ z, (f z ∈ B ↔ z ∈ A)

/--
Resolved true: Hayman update 2.31 reports that Barth and Schneider constructed functions
satisfying exactly these conditions (affirmative resolution). Source: K. F. Barth and W. J.
Schneider, Entire functions mapping arbitrary countable dense sets and their complements onto
each other, J. London Math. Soc. (2) 4 (1972), 482-488, https://doi.org/10.1112/jlms/s2-4.3.482.
Moved from `OpenConjectures/Analysis/ErdosEntireFunctionCountableDensePreimage`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.ErdosEntireFunctionCountableDensePreimageWanted
