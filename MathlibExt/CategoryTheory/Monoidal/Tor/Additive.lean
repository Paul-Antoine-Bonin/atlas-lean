/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
import MathlibExt.CategoryTheory.Abelian.LeftDerived.Additive

/-!
# Additivity of `Tor`

For a monoidal abelian preadditive category with projective resolutions,
`Tor C n` left-derives the tensor product in the second variable. Since
tensoring with a fixed object is additive and left-derived functors of additive
functors are additive, each functor `(Tor C n).obj M` is additive.
-/

@[expose] public section

namespace CategoryTheory

universe v u

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C]
  [MonoidalPreadditive C] [HasProjectiveResolutions C]

/-- Each functor `(Tor C n).obj M` is additive. -/
instance Tor.obj_additive (n : ℕ) (M : C) :
    Functor.Additive ((Tor C n).obj M) := by
  dsimp [Tor]
  infer_instance

end CategoryTheory
