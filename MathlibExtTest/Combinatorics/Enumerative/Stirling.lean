/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Stirling

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.Stirling

open MetaMathlibExt

-- The identity permutation on three elements has three one-cycles.
example : cycleQuotientCount (1 : Equiv.Perm (Fin 3)) = 3 := by
  simp [cycleQuotientCount_eq]

-- There are eleven permutations of four elements with two cycles.
example :
    Fintype.card {σ : Equiv.Perm (Fin 4) //
      Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 2} = 11 := by
  simpa [Nat.stirlingFirst] using card_perm_cycleCount_eq_stirlingFirst 4 2

end MathlibExtTest.Combinatorics.Enumerative.Stirling
