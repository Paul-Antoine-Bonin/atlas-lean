/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.Finite
public import Mathlib.Computability.Language

@[expose] public section

/-!
# Client tests for finite regular languages

Smoke tests applying `Cslib.Language.IsRegular.of_finite` and its corollaries,
plus an axiom audit for the new API.
-/

set_option autoImplicit false

open Cslib.Language

variable {Symbol : Type*} [Finite Symbol]

/-- Singleton word languages are regular. -/
example (w : List Symbol) : ({w} : Language Symbol).IsRegular :=
  IsRegular.singleton_word w

/-- The one-word language `1` is regular by bounded length. -/
example : ((1 : Language Symbol)).IsRegular := by
  refine IsRegular.of_length_le 0 ?_
  intro w hw
  rw [Language.mem_one] at hw
  subst hw
  exact Nat.zero_le _

/-- A concrete two-word language is regular. -/
example (a b : Symbol) : ({[a], [b]} : Language Symbol).IsRegular := by
  refine IsRegular.of_finite ?_
  exact Set.Finite.insert [a] (Set.finite_singleton [b])

#print axioms Cslib.Language.IsRegular.singleton_word
#print axioms Cslib.Language.IsRegular.of_finite
#print axioms Cslib.Language.IsRegular.of_length_le
