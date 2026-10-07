/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős problem 429
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem429Wanted

open Filter

def erdos429 : Prop :=
  ∃ f : ℕ → ℕ, Filter.Tendsto f Filter.atTop Filter.atTop ∧
    ∀ A : Set ℕ, A.Infinite → (∀ N : ℕ, (A ∩ Set.Icc 1 N).ncard ≤ f N) →
      (∀ p : ℕ, p.Prime → ∃ b : ZMod p, ∀ a ∈ A, (a : ZMod p) ≠ b) →
      ∃ n : ℤ, ∀ a ∈ A, (n + (a : ℤ)).toNat.Prime

/--
Resolved false: Disproved by Weisenberg (2024); ported as a formal statement. Source: D.
Weisenberg, Sparse Admissible Sets and a Problem of Erdős and Graham, Integers (2024). Moved
from `OpenConjectures/NumberTheory/ErdosProblem429`.
-/
public theorem_wanted erdos429_refuted : ¬ erdos429

end MathlibExt.NumberTheory.ErdosProblem429Wanted
