/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive
public import MathlibExt.CategoryTheory.Monoidal.Tor.Additive

/-!
# Compile-time checks for additivity of `Tor`

Typeclass inference provides additivity and finite (co)product preservation
for each functor `(Tor C n).obj M`, and additivity of left-derived functors
of additive functors.
-/

@[expose] public section

namespace CategoryTheory

universe v u

section TorObj

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [HasProjectiveResolutions C]

example (n : ℕ) (M : C) : Functor.Additive ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteBiproducts ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteProducts ((Tor C n).obj M) := inferInstance

example (n : ℕ) (M : C) :
    Limits.PreservesFiniteCoproducts ((Tor C n).obj M) := inferInstance

end TorObj

section ModuleCatTorObj

variable (R : Type u) [CommRing R]

example (n : ℕ) (M : ModuleCat R) :
    Functor.Additive ((CategoryTheory.Tor (ModuleCat R) n).obj M) :=
  inferInstance

end ModuleCatTorObj

section LeftDerived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasProjectiveResolutions C]
variable {D : Type*} [Category* D] [Abelian D]

example (F : C ⥤ D) [F.Additive] (n : ℕ) :
    Functor.Additive (F.leftDerived n) := inferInstance

end LeftDerived

end CategoryTheory
