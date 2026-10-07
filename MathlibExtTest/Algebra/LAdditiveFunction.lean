/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.LAdditiveFunction
public import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

example : IsLAdditive (fun _ : Int ↦ 0) := by
  intro m n
  simp

example {K : Type*} [Ring K] {f : K → K} (h : IsLAdditive f) (m n : K) :
    f (m * n) = f m * n + f n * m :=
  h m n

example {K : Type*} [Ring K] {f : K → K}
    (h : ∀ m n, f (m * n) = f m * n + f n * m) : IsLAdditive f :=
  h

example : ¬ IsLAdditive (fun x : Int ↦ x) := by
  intro h
  have h11 := h 1 1
  norm_num at h11

end MetaMathlibExt
