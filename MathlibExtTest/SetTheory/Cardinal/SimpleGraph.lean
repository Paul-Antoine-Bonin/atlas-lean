/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.SetTheory.Cardinal.SimpleGraph

@[expose] public section

open Ordinal Cardinal

-- Normal API use: the ordinal-cardinal Ramsey predicate accepts two
-- ordinals and a cardinal.
noncomputable example : Prop :=
  OrdinalCardinalRamsey (ω ^ ω : Ordinal.{0}) (ω ^ ω : Ordinal.{0}) (3 : Cardinal.{0})

-- Semantic check: the zero-color Ramsey statement holds via the empty
-- blue clique.
example : OrdinalCardinalRamsey (ω : Ordinal.{0}) (ω : Ordinal.{0}) (0 : Cardinal.{0}) := by
  intro red blue _
  right
  refine ⟨∅, fun x hx y hy _ => False.elim hx, ?_⟩
  simp
