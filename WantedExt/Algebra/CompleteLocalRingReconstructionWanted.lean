/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
OWR-1453-004: Reconstructing complete local rings from finite quotients.
If complete local Noetherian rings `A`, `B` satisfy `A/𝔪^r ≅ B/𝔫^r`
for every natural number `r`, must `A ≅ B`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

@[expose] public section

namespace MathlibExt.Algebra.CompleteLocalRingReconstructionWanted

/-! Source record `OWR-1453-004__30000671`. -/

/-- [OWR-1453-004] Two complete local Noetherian rings with pairwise
isomorphic finite quotients are isomorphic. Completeness is `I`-adic
completeness at the maximal ideal. -/
def conjecture : Prop :=
  ∀ (A B : Type*) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B],
    (∀ r : ℕ, Nonempty (A ⧸ (IsLocalRing.maximalIdeal A) ^ r ≃+*
      B ⧸ (IsLocalRing.maximalIdeal B) ^ r)) →
    Nonempty (A ≃+* B)

/--
Resolved false: Van den Dries (Proc. AMS 136 (2008), 3435-3448) proves the answer is yes when
the residue field is algebraic over its prime field and reports examples by Gabber showing the
answer is no in general, refuting the unrestricted implication formalized here. Source: Lou van
den Dries, Isomorphism of complete local noetherian rings and strong approximation, Proc. Amer.
Math. Soc. 136 (2008), 3435-3448, https://doi.org/10.1090/S0002-9939-08-09401-X. Moved from
`OpenConjectures/Algebra/CompleteLocalRingReconstruction`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.CompleteLocalRingReconstructionWanted
