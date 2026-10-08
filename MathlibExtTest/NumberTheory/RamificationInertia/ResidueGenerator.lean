/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RamificationInertia.ResidueGenerator

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- Generic API: canonical map on residue algebras is surjective. -/
example (q : Ideal B) (π : B) (hπ : π ∈ q)
    (hgen : Algebra.adjoin A {π} = ⊤) :
    Function.Surjective
      (algebraMap (A ⧸ q.comap (algebraMap A B)) (B ⧸ q)) :=
  Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top q π hπ hgen

/-- Generic API: inertia degree is `1` under the same hypotheses. -/
example (q : Ideal B) [q.IsMaximal] [(q.under A).IsMaximal] (π : B)
    (hπ : π ∈ q) (hgen : Algebra.adjoin A {π} = ⊤) :
    q.inertiaDeg A = 1 :=
  Ideal.inertiaDeg_eq_one_of_adjoin_singleton_eq_top q π hπ hgen

/-- Concrete `ℤ`-algebra generator: every integer lies in the adjoin. -/
private theorem adjoin_singleton_two_eq_top :
    Algebra.adjoin ℤ ({(2 : ℤ)} : Set ℤ) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  have h : algebraMap ℤ ℤ x ∈ Algebra.adjoin ℤ ({(2 : ℤ)} : Set ℤ) :=
    Subalgebra.algebraMap_mem _ x
  simpa using h

/-- Concrete quotient-map check at `A = B = ℤ`, `q = span {2}`, `π = 2`. -/
example : Function.Surjective
    (algebraMap
      (ℤ ⧸ (Ideal.span ({(2 : ℤ)} : Set ℤ)).comap (algebraMap ℤ ℤ))
      (ℤ ⧸ Ideal.span ({(2 : ℤ)} : Set ℤ))) :=
  Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top _
    2 (Ideal.mem_span_singleton_self 2) adjoin_singleton_two_eq_top

#print axioms Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top
#print axioms Ideal.inertiaDeg_eq_one_of_adjoin_singleton_eq_top
