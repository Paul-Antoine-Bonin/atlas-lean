/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AMR 11 Question 33: return-probability gap for Cayley graphs
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic

open scoped BigOperators

@[expose] public section

namespace MathlibExt.GraphTheory.AMR11Problem33Wanted

/-! Source record `AMR-011-0033`. -/

namespace AMR11Q33

universe u

/-!
# Clause inventory for [AMR-011-0033] Some Questions — Question 33

- `k` is a natural number with `1 < k`.
- `G` is a group (Cayley graph over a group).
- `gen : Finset G` is the finite generating set.
- Symmetry: `s ∈ gen` implies `s⁻¹ ∈ gen`.
- `1 ∉ gen`.
- Generation (connectedness): every `g : G` is `l.prod` for some `l : List G`
  with all entries in `gen`.
- `k`-regularity: `gen.card = k`.
- Words of length `n` over `gen`, as `Fin n → ↥Γ.gen`.
- Word evaluation via `(List.ofFn fun i => (w i : G)).prod`.
- First-return words: product equals `1` with no shorter nonempty prefix
  product equal to `1`.
- First-return probability at time `n`: card of first-return words divided
  by `(k : ℝ) ^ n` (`0` when `n = 0`).
- Return probability: `∑' n, firstReturnProb Γ n`.
- Transient: `returnProb Γ < 1`.
- `C : ℝ` depends only on `k` and satisfies `C < 1`.
- Uniform bound: every transient graph satisfies `returnProb Γ ≤ C`.
-/

/-- Finite symmetric `k`-regular Cayley generating data for [AMR-011-0033] Question 33. -/
structure RegularCayleyGraph (G : Type u) [Group G] [DecidableEq G]
    (k : ℕ) where
  gen : Finset G
  symm_mem : ∀ s ∈ gen, s⁻¹ ∈ gen
  one_not_mem : (1 : G) ∉ gen
  connected : ∀ g : G, ∃ l : List G, (∀ s ∈ l, s ∈ gen) ∧ l.prod = g
  regular : gen.card = k

/-- First-return probability at time `n` for [AMR-011-0033] Question 33. -/
noncomputable def firstReturnProb {G : Type u} [Group G]
    [DecidableEq G] {k : ℕ} (Γ : RegularCayleyGraph G k) (n : ℕ) : ℝ := by
  classical
  exact if 0 < n then
    (Fintype.card
      { w : Fin n → Γ.gen //
        (List.ofFn fun i => (w i : G)).prod = 1 ∧
        ∀ (m : ℕ) (hm : m ∈ Finset.range n), 0 < m →
          (List.ofFn fun (i : Fin m) =>
            (w (Fin.castLE (Nat.le_of_lt (Finset.mem_range.mp hm)) i) : G)).prod ≠
            1 } : ℝ) / (k : ℝ) ^ n
    else 0

/-- Simple random walk ever-return probability for [AMR-011-0033] Question 33. -/
noncomputable def returnProb {G : Type u} [Group G] [DecidableEq G]
    {k : ℕ} (Γ : RegularCayleyGraph G k) : ℝ :=
  ∑' n, firstReturnProb Γ n

/-- Uniform return-probability gap question for [AMR-011-0033] Question 33. -/
def returnProbUniformGap : Prop :=
  ∀ (k : ℕ), 1 < k →
    ∃ C : ℝ, C < 1 ∧
      ∀ (G : Type u) [Group G] [DecidableEq G]
        (Γ : RegularCayleyGraph G k),
        returnProb Γ < 1 → returnProb Γ ≤ C

end AMR11Q33

/--
Resolved true: Tessera and Tointon (arXiv:2001.01467, 2020; v2 2024), Corollary 1.3, prove a
universal c>0 such that simple random walk on every connected locally finite vertex-transitive
graph is recurrent or escapes with probability at least c, so C(k)=1-c works for all transient
k-regular Cayley graphs. Source: Romain Tessera and Matthew Tointon, Sharp relations between
volume growth, isoperimetry and escape probability in vertex-transitive graphs, arXiv preprint
(2020, v2 2024), arXiv:2001.01467, https://arxiv.org/abs/2001.01467. Moved from
`OpenConjectures/GraphTheory/AMR11Problem33`.
-/
public theorem_wanted returnProbUniformGap_holds : AMR11Q33.returnProbUniformGap

end MathlibExt.GraphTheory.AMR11Problem33Wanted
