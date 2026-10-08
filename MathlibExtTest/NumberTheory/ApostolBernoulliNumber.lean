/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ApostolBernoulliNumber

namespace MetaMathlibExt

example {α : ℂ} {β : ℕ → ℂ} (h : IsApostolBernoulliSequence α β) : α ≠ 0 := h.1

example {α : ℂ} {β : ℕ → ℂ} (h : IsApostolBernoulliSequence α β) : α ≠ 1 :=
  h.2.1

example {α : ℂ} {β : ℕ → ℂ} (h : IsApostolBernoulliSequence α β)
    {t : ℂ} (ht : ‖t‖ < ‖Complex.log α‖) :
    HasSum (fun k : ℕ => β k * t ^ k / (Nat.factorial k : ℂ))
      (t / (α * Complex.exp t - 1)) :=
  h.2.2 t ht

#print axioms IsApostolBernoulliSequence

end MetaMathlibExt
