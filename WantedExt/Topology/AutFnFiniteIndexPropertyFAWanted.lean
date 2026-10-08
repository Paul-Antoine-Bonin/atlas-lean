/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Property FA for finite-index subgroups of Aut(Fₙ) [AMR-109-0276]

Source: Farb, Problems on Mapping Class Groups and Related Topics,
Question 2.8, PDF p. 331.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

namespace MathlibExt.Topology.AutFnFiniteIndexPropertyFAWanted

/-!
[AMR-109-0276] Farb Question 2.8.
Source: Farb, Problems on Mapping Class Groups and Related Topics,
Question 2.8, PDF p. 331,
`https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf`.

Clause list (every item below appears in the formal text):
1. `n : ℕ` (rank of the free group `Fₙ`).
2. `4 ≤ n` (numeric threshold, closed below at 4).
3. `Fₙ = FreeGroup (Fin n)`.
4. `Aut(Fₙ) = MulAut (FreeGroup (Fin n))`.
5. `H : Subgroup (MulAut (FreeGroup (Fin n)))` (subgroup of `Aut(Fₙ)`).
6. `H.FiniteIndex` (finite index side condition).
7. `HasPropertyFA ↥H` (Serre's Property FA: every simplicial action
   without edge inversion on a simplicial tree has a global fixed
   vertex).
8. Status: posed as a question-Prop; the file asserts no answer.
-/

universe u

/-- Serre's Property FA for a group `G`: every simplicial action of `G`
on a simplicial tree, acting by adjacency-preserving permutations without
edge inversion, has a global fixed vertex [AMR-109-0276] (Question 2.8,
PDF p. 331). -/
def HasPropertyFA (G : Type u) [Group G] : Prop :=
  ∀ (V : Type u) (T : SimpleGraph V), T.IsTree →
    ∀ (α : G →* Equiv.Perm V),
      (∀ g : G, ∀ u v : V, T.Adj (⇑(α g) u) (⇑(α g) v) ↔ T.Adj u v) →
      (∀ g : G, ∀ u v : V, T.Adj u v → ⇑(α g) u = v → ⇑(α g) v ≠ u) →
      ∃ v : V, ∀ g : G, ⇑(α g) v = v

/-- Farb Question 2.8 [AMR-109-0276] (PDF p. 331): for `n ≥ 4`, do
subgroups of finite index in `Aut(Fₙ)` have Serre's Property FA? -/
def conjecture : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ∀ H : Subgroup (MulAut (FreeGroup (Fin n))),
      H.FiniteIndex → HasPropertyFA ↥H

/--
Resolved true: Aut(F_n) has Kazhdan's property (T) for n >= 4: Kaluba–Kielak–Nowak (Ann. of
Math. 193 (2021), arXiv:1812.03456) for n >= 6, Kaluba–Nowak–Ozawa for n = 5, Nitsche
(arXiv:2009.05134) for n = 4. Property (T) passes to finite-index subgroups and implies Serre's
FA (Watatani). Source: Marek Kaluba, Dawid Kielak and Piotr W. Nowak, On property (T) for
Aut(F_n) and SL_n(Z), Ann. of Math. 193 (2021), arXiv:1812.03456,
https://arxiv.org/abs/1812.03456; Martin Nitsche, Computer proofs for Property (T), and SDP
duality, arXiv:2009.05134v3 (2022), https://arxiv.org/abs/2009.05134. Moved from
`OpenConjectures/Topology/AutFnFiniteIndexPropertyFA`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Topology.AutFnFiniteIndexPropertyFAWanted
