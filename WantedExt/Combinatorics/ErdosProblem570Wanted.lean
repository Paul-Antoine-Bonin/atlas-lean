/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 570
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.SimpleGraph.Ramsey
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic

@[expose] public section

open Filter SimpleGraph

namespace MathlibExt.Combinatorics.ErdosProblem570Wanted

/-! Source record `FC-ErdosProblem570`, ported from FormalConjectures
`ErdosProblems/570.lean` (`theorem erdos_570`) and checked against
erdosproblems.com/570. `graphPairRamsey` is MathlibExt's (ported from FC's
`FormalConjecturesForMathlib`); `cycleGraph` is Mathlib's. The `answer(True)`
wrapper is elaborated to a direct proposition. Status: resolved true (even
`k` by Erdős–Faudree–Rousseau–Schelp; `k = 3`, `k = 5`, and all odd `k ≥ 7`
by Goddard–Kleitman, Sidorenko, Jayawardene, and Cambie–Freschi–Morawski–
Petrova–Pokrovskiy). -/

/-- `R(Cₖ,H) ≤ 2m + ⌊(k-1)/2⌋` for large `m` and all `k ≥ 3`. -/
def conjecture : Prop :=
  ∀ (k : ℕ) (_ : 3 ≤ k),
    ∀ᶠ (m : ℕ) in atTop,
      ∀ (W : Type) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
        (∀ v, 0 < H.degree v) →
        H.edgeSet.ncard = m →
        graphPairRamsey (cycleGraph k) H ≤ 2 * m + (k - 1) / 2

/--
Resolved true: Resolved true: R(C_k,H) <= 2m + (k-1)/2 for large m (EFRS93, GoKl94, Si91, Ja99,
CFMPP26). Source: S. Cambie, A. Freschi, P. Morawski, K. Petrova, A. Pokrovskiy, Ramsey number
of a cycle versus a graph of a given size, arXiv:2601.10238 (2026),
https://arxiv.org/abs/2601.10238. Moved from `OpenConjectures/Combinatorics/ErdosProblem570`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.ErdosProblem570Wanted
