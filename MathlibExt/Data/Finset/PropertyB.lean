/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic

/-!
# Property B for families of finite sets

A family of finite sets has property B (equivalently, it is `2`-colourable,
i.e. its chromatic number is at most `2`)
if there is a `2`-colouring of the ground set under which no member of the
family is monochromatic.
-/

@[expose] public section

namespace Finset

/-- A family `F` of finite sets has **property B** (equivalently, it is
`2`-colourable, i.e. its chromatic number is at most `2`) if there is a
`2`-colouring of the ground set under which no
member of `F` is monochromatic. -/
def HasPropertyB {α : Type*} (F : Finset (Finset α)) : Prop :=
  ∃ f : α → Fin 2, ∀ A ∈ F, ∃ x ∈ A, ∃ y ∈ A, f x ≠ f y

end Finset
