/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.BurnsidePaqb
public import Mathlib.Data.ZMod.Basic

@[expose] public section

/-!
# Compile-time tests for Burnside's `p^a q^b` theorem

Authors: Muse Spark 1.3
-/

open BurnsidePaqb

-- Exact API shape of the headline theorem.
example {G : Type*} [Group G] [Fintype G]
    (p q a b : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hcard : Fintype.card G = p ^ a * q ^ b) : Group.IsSolvable G :=
  burnside_paqb p q a b hp hq hcard

-- Boundary convention `p = q`: a group of order `2 ^ 1 * 2 ^ 1`.
example : Group.IsSolvable (Multiplicative (ZMod 4)) :=
  burnside_paqb 2 2 1 1 (by decide) (by decide) (by decide)

-- Boundary convention with zero exponent `a = 0`: order `2 ^ 0 * 3 ^ 1`.
example : Group.IsSolvable (Multiplicative (ZMod 3)) :=
  burnside_paqb 2 3 0 1 (by decide) (by decide) (by decide)

-- Trivial group with `a = b = 0`: order `2 ^ 0 * 3 ^ 0`.
example : Group.IsSolvable Unit :=
  burnside_paqb 2 3 0 0 (by decide) (by decide) (by simp)
