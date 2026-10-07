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
# Erdős Problem 1034
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Basic

@[expose] public section

open Filter

namespace MathlibExt.GraphTheory.ErdosProblem1034Wanted

/-! Source record `FC-ErdosProblem1034`, ported from FormalConjectures
`ErdosProblems/1034.lean` (`def JoinedToTwo`, `theorem erdos_1034`,
`lower_bound`, `upper_bound`, `k4_free`) and checked against
erdosproblems.com/1034. A conjecture of Erdős and Faudree (stronger than
[905]). Status: resolved false (Ma–Tang; formalized in Lean). The
historical positive claim is preserved as `conjecture` (disproved); its
negation is the unregistered companion `disprovedForm`. The book lower
bound and the Ma–Tang and K₄-free upper bounds are unregistered
established companions. -/

/-- `JoinedToTwo G T Y` holds when every vertex of `Y` is joined to at least
two (distinct) vertices of `T`. -/
def JoinedToTwo {V : Type*} (G : SimpleGraph V) (T Y : Finset V) : Prop :=
  ∀ y ∈ Y, ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ G.Adj y u ∧ G.Adj y v

/-- The historical Erdős–Faudree claim (disproved): dense graphs join more
than `(1/2 - ε)n` vertices doubly to some triangle. -/
def conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
    (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
      ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
        JoinedToTwo G T Y ∧ (1 / 2 - ε) * (n : ℝ) < (Y.card : ℝ)

/-- Its disproof (companion). -/
def disprovedForm : Prop := ¬ conjecture

/-- Book lower bound (established companion): some triangle always joins at
least `(1/6 - ε)n` vertices doubly. -/
def bookLowerBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∀ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) →
        ∃ T : Finset (Fin n), G.IsNClique 3 T ∧ ∃ Y : Finset (Fin n),
          JoinedToTwo G T Y ∧ (1 / 6 - ε) * (n : ℝ) ≤ (Y.card : ℝ)

/-- Ma–Tang upper bound (established companion): some dense graphs join at
most `(2 - √(5/2) + ε)n` vertices doubly to every triangle. -/
def maTangUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n),
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 - Real.sqrt (5 / 2) + ε) * (n : ℝ)

/-- K₄-free upper bound (established companion): the refutation persists
under a `K₄`-free hypothesis, with constant `2√3 - 3`. -/
def k4FreeUpperBound : Prop :=
  ∀ (ε : ℝ), 0 < ε →
    ∀ᶠ (n : ℕ) in atTop, ∃ G : SimpleGraph (Fin n), G.CliqueFree 4 ∧
      (n : ℝ) ^ 2 / 4 < (G.edgeSet.ncard : ℝ) ∧
        ∀ T : Finset (Fin n), G.IsNClique 3 T → ∀ Y : Finset (Fin n),
          JoinedToTwo G T Y →
          (Y.card : ℝ) ≤ (2 * Real.sqrt 3 - 3 + ε) * (n : ℝ)

/--
Resolved false: Disproved by Ma and Tang (formalized in Lean), per erdosproblems.com/1034.
Source: Ma and Tang (disproof with upper bound (2-√(5/2)+o(1))n; K₄-free sketch with
(2√3-3+o(1))n), per erdosproblems.com/1034, https://www.erdosproblems.com/1034. Moved from
`OpenConjectures/GraphTheory/ErdosProblem1034`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GraphTheory.ErdosProblem1034Wanted
