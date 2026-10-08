/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.RamificationInertia.Inseparable

@[expose] public section

open Ideal

attribute [local instance] Ideal.Quotient.field

example {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
    [IsDomain A] [IsDomain B] [Module.Finite A B] [Module.Flat A B]
    {p : Ideal A} [p.IsMaximal] (P : Ideal B) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (P.inertia G) = ramificationIdxIn p B *
      Field.finInsepDegree (A ⧸ p) (B ⧸ P) :=
  Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree G P

example {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B] {p : Ideal A} [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal] :
    Nat.card (P.inertia G) = ramificationIdxIn p B *
      Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
  let _ : Module.Flat A B := inferInstance
  exact Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree G P

example {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsDomain A] [IsDomain B]
    [Module.Finite A B] [Module.Flat A B] {p : Ideal A} [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal] :
    ramificationIdxIn p B ∣ Nat.card (P.inertia G) :=
  ⟨Field.finInsepDegree (A ⧸ p) (B ⧸ P),
    Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree G P⟩

example {A B : Type*} [CommRing A]
    [CommRing B] [Algebra A B] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G B] [IsGaloisGroup G A B] [IsDomain A] [IsDomain B]
    [Module.Finite A B] [Module.Flat A B] {p : Ideal A} [p.IsMaximal]
    (P : Ideal B) [P.LiesOver p] [P.IsMaximal] [Algebra.IsSeparable (A ⧸ p) (B ⧸ P)] :
    Nat.card (P.inertia G) = ramificationIdxIn p B := by
  rw [Ideal.card_inertia_eq_ramificationIdxIn_mul_finInsepDegree
      (A := A) (B := B) (p := p) G P,
    (isSeparable_iff_finInsepDegree_eq_one (A ⧸ p) (B ⧸ P)).mp inferInstance, mul_one]

end
