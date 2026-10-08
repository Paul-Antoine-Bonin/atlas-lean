/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Ring.JacobsonCommutativity

@[expose] public section

namespace MathlibExt.Algebra.Ring.JacobsonCommutativity

-- Exact-signature API invocation: generic `Ring` with pointwise exponent hypothesis.
example {R : Type*} [Ring R]
    (h : ∀ x : R, ∃ n : Nat, 1 < n ∧ x ^ n = x) :
    ∀ x y : R, x * y = y * x :=
  jacobson_commutativity h

end MathlibExt.Algebra.Ring.JacobsonCommutativity
