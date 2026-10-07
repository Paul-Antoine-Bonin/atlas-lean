/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Complex.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RepresentationTheory.Character
public import Mathlib.SetTheory.Cardinal.Basic

open CategoryTheory

namespace MetaMathlibExt

@[expose] public section

/-- The irreducible complex characters of `G` of `p'`-degree, as a set of
functions: the characters of simple finite-dimensional complex representations
whose dimension is not divisible by `p`. Two simple representations have equal
characters exactly when they are isomorphic, so this set is in canonical
bijection with the set `Irr_{p'}(G)` counted by the McKay conjecture. -/
def pPrimeCharacters (G : Type*) [Group G] (p : ℕ) : Set (G → ℂ) :=
  {χ | ∃ V : FDRep ℂ G, Simple V ∧ V.character = χ ∧ ¬p ∣ Module.finrank ℂ V}

/-- The **McKay conjecture**, now the theorem of Cabanes and Späth: for every
finite group `G`, every prime `p`, and every Sylow `p`-subgroup `P` of `G`, the
irreducible complex characters of `G` of degree not divisible by `p` are
equinumerous with those of the normalizer of `P` in `G`.

Source: M. Cabanes and B. Späth, *The McKay conjecture*,
Ann. of Math. 203(3) (2026), arXiv:2410.20392, doi:10.4007/annals.2026.203.3.5. -/
theorem_wanted mckay_irr_equicardinal (G : Type*) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    Cardinal.mk (pPrimeCharacters G p) =
      Cardinal.mk (pPrimeCharacters (Subgroup.normalizer (P : Set G)) p)

end

end MetaMathlibExt
