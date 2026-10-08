/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.TransferMatrixOfGRH

namespace MetaMathlibExt

example : zykovZeroIndicator 0 = true := rfl
example : zykovZeroIndicator 1 = false := rfl

example : relationPairing (V := Fin 2) (W := Fin 2) (fun _ _ => True)
    (fun _ => true) (fun _ => true) = 4 := rfl

example :
    zykovTransferMatrix (⊥ : SimpleGraph (Fin 2)) (⊥ : SimpleGraph (Fin 2))
      (fun _ _ => False)
      ((⟨∅, by simp⟩ :
          {s : Finset (Fin 2) // (⊥ : SimpleGraph (Fin 2)).IsIndepSet (↑s : Set (Fin 2))}),
        (⟨∅, by simp⟩ :
          {s : Finset (Fin 2) // (⊥ : SimpleGraph (Fin 2)).IsIndepSet (↑s : Set (Fin 2))})) =
      true := rfl

#print axioms zykovZeroIndicator
#print axioms independentSetCharacteristic
#print axioms relationPairing
#print axioms zykovTransferMatrix

end MetaMathlibExt
