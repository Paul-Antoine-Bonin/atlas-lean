/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GroupTheory.GroupAction.UniformFixedPoints
import Mathlib.Algebra.Group.Action.TypeTags
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.GroupTheory.GroupAction.UniformFixedPoints

-- Translation by a nonzero element of `ZMod 5` has no fixed points and hence one orbit.
example :
    Nat.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod 5)) (ZMod 5)) = 1 := by
  have h := MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    (Multiplicative (ZMod 5)) (ZMod 5) 0 (by
      intro g hg
      simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset,
        MulAction.mem_fixedBy, Finset.card_eq_zero, Finset.filter_eq_empty_iff,
        Finset.mem_univ, forall_const]
      intro x hx
      change g.toAdd + x = x at hx
      apply hg
      apply Multiplicative.ext
      simpa using hx)
  norm_num [Nat.card_eq_fintype_card] at h
  omega

end MathlibExtTest.GroupTheory.GroupAction.UniformFixedPoints
