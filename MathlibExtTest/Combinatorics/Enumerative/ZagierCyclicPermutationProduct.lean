/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Combinatorics.Enumerative.ZagierCyclicPermutationProduct

open MetaMathlibExt

-- For four elements, the product has two cycles with probability 5/6.
example :
    ((Fintype.card {p : Equiv.Perm (Fin 4) × Equiv.Perm (Fin 4) //
        Multiset.card p.1.cycleType + Fintype.card (Function.fixedPoints p.1) = 1 ∧
        Multiset.card p.2.cycleType + Fintype.card (Function.fixedPoints p.2) = 1 ∧
        Multiset.card (p.1 * p.2).cycleType +
            Fintype.card (Function.fixedPoints (p.1 * p.2)) = 2}) : ℚ) /
      ((Fintype.card {σ : Equiv.Perm (Fin 4) //
          Multiset.card σ.cycleType + Fintype.card (Function.fixedPoints σ) = 1}) : ℚ) ^ 2 =
      5 / 6 := by
  rw [zagier_probability_product_two_cyclic_permutations 4 2 (by omega) (by omega)
    (by omega)]
  norm_num [Nat.stirlingFirst, Nat.factorial]

end MathlibExtTest.Combinatorics.Enumerative.ZagierCyclicPermutationProduct
