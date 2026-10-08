/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Data.Set.Interval
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

-- Normal API use: set–interval intersections are fintypes.
noncomputable example (S : Set ℕ) (a b : ℕ) : Fintype (S ∩ Set.Icc a b : Set ℕ) :=
  inferInstance

noncomputable example (S : Set ℕ) (b : ℕ) : Fintype (S ∩ Set.Iio b : Set ℕ) :=
  inferInstance
