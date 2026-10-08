/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Polynomial.FormalOrthogonality

namespace MetaMathlibExt.Polynomial

/-- Unfolding check: the witness also supplies every degree clause. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) :
    ∀ n, (p n).natDegree = n := by
  unfold IsFormallyOrthogonal at h
  obtain ⟨_, hdeg, _, _⟩ := h
  exact hdeg

/-- Off-diagonal projection: the witness kills mixed products. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) {n m : ℕ} (hnm : n ≠ m) :
    ∃ L : Polynomial R →ₗ[R] R, L (p n * p m) = 0 := by
  obtain ⟨L, _, horth, _⟩ := h
  exact ⟨L, horth n m hnm⟩

/-- Diagonal projection: the witness does not kill any square. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) (n : ℕ) :
    ∃ L : Polynomial R →ₗ[R] R, L (p n ^ 2) ≠ 0 := by
  obtain ⟨L, _, _, hdiag⟩ := h
  exact ⟨L, hdiag n⟩

/-- The identically-zero family is not formally orthogonal, since it
violates the degree clause at index 1. -/
theorem not_isFormallyOrthogonal_zero (R : Type*) [Field R] :
    ¬ IsFormallyOrthogonal (fun _ => (0 : Polynomial R)) := by
  intro h
  obtain ⟨_, hdeg, _, _⟩ := h
  have h1 : ((0 : Polynomial R)).natDegree = 1 := hdeg 1
  rw [Polynomial.natDegree_zero] at h1
  exact zero_ne_one h1

end MetaMathlibExt.Polynomial
