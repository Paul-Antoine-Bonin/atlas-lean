/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.FiniteAbelianDual
import Mathlib.SetTheory.Cardinal.Finite

open MathlibExt.GroupTheory.FiniteAbelianDualWanted

-- Self-duality gives equality of the underlying finite cardinalities.
example (α : Type*) [AddCommGroup α] [Finite α] :
    Nat.card (AddChar α ℂ) = Nat.card α := by
  obtain ⟨e⟩ := finite_abelian_dual_iso α
  exact (Nat.card_congr e.toEquiv).symm

-- Applying the product equivalence twice decomposes three factors.
example (α β γ : Type*) [AddCommGroup α] [AddCommGroup β] [AddCommGroup γ] :
    Nonempty
      (AddChar ((α × β) × γ) ℂ ≃+
        ((AddChar α ℂ × AddChar β ℂ) × AddChar γ ℂ)) := by
  obtain ⟨e₁⟩ := dual_prod (α × β) γ
  obtain ⟨e₂⟩ := dual_prod α β
  exact ⟨e₁.trans (e₂.prodCongr (AddEquiv.refl _))⟩
