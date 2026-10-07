/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.FrobeniusRestriction

/-!
# Tests for Frobenius restriction in a tower (ATLAS N402, Stage C2b)
-/

@[expose] public noncomputable section

open NumberField

namespace N402FrobeniusRestrictionTest

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [NumberField K] [NumberField L] [NumberField M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsAbelianGalois K L] [IsGalois K M]

/-- Restriction of the chosen Frobenius agrees on the abelian subextension. -/
example (m : Modulus K) (hL : m.IsUnramifiedOutside L)
    (hM : m.IsUnramifiedOutside M) (p : m.CoprimePrimes) :
    AlgEquiv.restrictNormalHom L
        (m.frobeniusAtCoprimePrime (L := M) hM p) =
      m.frobeniusAtCoprimePrime (L := L) hL p := by
  simpa only using
    m.restrictNormalHom_frobeniusAtCoprimePrime (L := L) (M := M) hL hM p

end N402FrobeniusRestrictionTest
