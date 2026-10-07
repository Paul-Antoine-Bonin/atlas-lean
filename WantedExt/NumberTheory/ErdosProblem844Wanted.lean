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
# Erdős Problem 844
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem844Wanted

/-! Source record `FC-ErdosProblem844`, ported from FormalConjectures
`ErdosProblems/844.lean` and checked against erdosproblems.com/844.
The upstream `answer(True)` is dropped. Status: resolved true externally;
this repository records the statement but not a Lean proof. -/

/-- Even numbers together with odd non-squarefree numbers up to `N`. -/
def evenOrOddNonSquarefree (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 2 ∣ n ∨ ¬ Squarefree n)

/-- The even/odd-non-squarefree set is the extremal non-squarefree-product
set. -/
def conjecture : Prop :=
  ∀ N : ℕ,
    IsGreatest {k : ℕ | ∃ A ⊆ Finset.Icc 1 N,
      (∀ a ∈ A, ∀ b ∈ A, ¬ Squarefree (a * b)) ∧ A.card = k}
      (evenOrOddNonSquarefree N).card

/--
Resolved true: Resolved affirmatively by Desmond Weisenberg and independently by Alexeev, Mixon,
and Sawin; this repository records the statement but not either proof. Source: B. Alexeev, D.
Mixon, and W. Sawin, The independence and clique cover numbers of the squarefree graph,
arXiv:2507.01928 (2025), https://arxiv.org/abs/2507.01928; Erdős Problems, Problem 844
(including Desmond Weisenberg's proof), https://www.erdosproblems.com/latex/844. Moved from
`OpenConjectures/NumberTheory/ErdosProblem844`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem844Wanted
