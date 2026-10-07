/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Exotic units in the integral group ring of C₂ × C₂ × C₂ × C₆

`OWR-11129-005` (Computational Group Theory (2012)): does the integral
group ring `ℤG` of `G = C₂ × C₂ × C₂ × C₆` contain a unit that is not
of the trivial form `±g`?
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted

/-- The group `C₂ × C₂ × C₂ × C₆` from `OWR-11129-005`
(Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37): exact cyclic factors of orders 2, 2, 2, 6. -/
abbrev OWRGroup : Type := ZMod 2 × ZMod 2 × ZMod 2 × ZMod 6

/-- The integral group ring `ℤG` of `OWRGroup` from `OWR-11129-005`
(Computational Group Theory (2012), Oberwolfach Reports,
DOI 10.4171/owr/2011/37). -/
abbrev OWRGroupRing : Type := AddMonoidAlgebra ℤ OWRGroup

/-- The open question of `OWR-11129-005` (Computational Group Theory (2012),
Oberwolfach Reports, DOI 10.4171/owr/2011/37): whether the integral group
ring of `C₂ × C₂ × C₂ × C₆` contains an exotic unit, i.e. a unit that is not
of the trivial form `±g` for any `g ∈ G` and any sign in `ℤˣ`. -/
def conjecture : Prop :=
  ∃ u : OWRGroupRingˣ, ∀ g : OWRGroup, ∀ s : ℤˣ,
    (↑u : OWRGroupRing) ≠ AddMonoidAlgebra.single g (↑s : ℤ)

/--
Resolved false: Classical: G. Higman (1940) showed the integral group ring of an abelian group
of exponent dividing 4 or 6 has only the units ±g. Via the cut-group criterion in Bächle
(arXiv:1701.04347, Prop. 2.2), C2^3 x C6 (exponent 6) is an abelian cut group, so every unit of
ZG is trivial and no exotic unit exists. Source: Andreas Bächle, Integral group rings of
solvable groups with trivial central units, Forum Math. 30 (2018), arXiv:1701.04347,
https://arxiv.org/abs/1701.04347. Moved from `OpenConjectures/Algebra/ExoticUnitsC2C2C2C6`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.ExoticUnitsC2C2C2C6Wanted
