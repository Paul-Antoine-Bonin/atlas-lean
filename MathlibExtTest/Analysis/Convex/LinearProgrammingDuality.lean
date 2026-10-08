/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.LinearProgrammingDuality

/-!
# Tests for strong linear programming duality

Focused checks for `LPDuality.strong_linear_programming_duality`: an ordinary
one-dimensional program whose optimum value is pinned down, plus the two
empty-index boundary cases (no primal variables, no constraints).
-/

@[expose]
public section

namespace LinearProgrammingDualityTest

/-- Constraint matrix `(1)` of the one-dimensional test program, given an
explicit matrix type so that dot notation resolves to `Matrix.mulVec`. -/
private def oneDimA : Matrix (Fin 1) (Fin 1) ℝ := ![![1]]

/-- The constraint matrix acts as the identity. -/
private theorem oneDimA_mulVec (x : Fin 1 → ℝ) (j : Fin 1) :
    oneDimA.mulVec x j = x 0 := by
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp [oneDimA, Matrix.mulVec, dotProduct]

/-- The transposed constraint matrix acts as the identity. -/
private theorem oneDimA_transpose_mulVec (y : Fin 1 → ℝ) (i : Fin 1) :
    (oneDimA.transpose.mulVec y) i = y 0 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  unfold oneDimA
  have h11 : (Matrix.transpose (![![1]] : Matrix (Fin 1) (Fin 1) ℝ)) 0 0 = 1 := rfl
  simp [Matrix.mulVec, dotProduct, h11]

/-- One-dimensional program `max { 2 * x | 0 ≤ x ≤ 5 }`: feasible and bounded. -/
private theorem oneDim_feas :
    ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      ∀ j, oneDimA.mulVec x j ≤ ![5] j := by
  refine ⟨![5], Fin.forall_fin_one.mpr ?_, fun j => ?_⟩
  · simp
  · rw [oneDimA_mulVec]
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp

/-- One-dimensional program `max { 2 * x | 0 ≤ x ≤ 5 }`: bounded above by `10`. -/
private theorem oneDim_bdd (x : Fin 1 → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hAx : ∀ j, oneDimA.mulVec x j ≤ ![5] j) :
    (fun _ => (2 : ℝ)) ⬝ᵥ x ≤ 10 := by
  have h5 : x 0 ≤ 5 := by
    have h := hAx 0
    rw [oneDimA_mulVec] at h
    simpa using h
  have hnn : 0 ≤ x 0 := hx 0
  have hval : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := by
    simp [dotProduct]
  rw [hval]
  linarith

/-- One-dimensional optimum: the attained value equals `10`. -/
example :
    ∃ x : Fin 1 → ℝ, (∀ i, 0 ≤ x i) ∧
      (∀ j, oneDimA.mulVec x j ≤ ![5] j) ∧
      (fun _ => (2 : ℝ)) ⬝ᵥ x = 10 := by
  obtain ⟨x, y, hx, hAx, hy, hAy, heq⟩ :=
    MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
      oneDimA ![5] (fun _ => 2)
      oneDim_feas ⟨10, oneDim_bdd⟩
  have hxx : x 0 ≤ 5 := by
    have h := hAx 0
    rw [oneDimA_mulVec] at h
    simpa using h
  have hyy : 2 ≤ y 0 := by
    have h := hAy 0
    rw [oneDimA_transpose_mulVec] at h
    simpa using h
  have hval : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := by
    simp [dotProduct]
  refine ⟨x, hx, hAx, ?_⟩
  rw [hval]
  have hub : 2 * x 0 ≤ 10 := by linarith [hxx, hx 0]
  have hlb : 10 ≤ 2 * x 0 := by
    have hb : ![5] ⬝ᵥ y = 5 * y 0 := by
      simp [dotProduct]
    have hcc : (fun _ => (2 : ℝ)) ⬝ᵥ x = 2 * x 0 := hval
    rw [hcc, hb] at heq
    linarith [hyy, hy 0]
  linarith

/-- No primal variables (`n = 0`): feasible and bounded, hence optimal pair. -/
example :
    ∃ x : Fin 0 → ℝ, ∃ y : Fin 1 → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, (0 : Matrix (Fin 1) (Fin 0) ℝ).mulVec x j ≤ ![7] j) ∧
      (∀ j, 0 ≤ y j) ∧
      (∀ i, (0 : Fin 0 → ℝ) i ≤
        ((0 : Matrix (Fin 1) (Fin 0) ℝ).transpose.mulVec y) i) ∧
      (0 : Fin 0 → ℝ) ⬝ᵥ x = ![7] ⬝ᵥ y := by
  apply MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
  · exact ⟨0, fun i => i.elim0, Fin.forall_fin_one.mpr (by simp)⟩
  · exact ⟨0, fun x _ _ => by simp⟩

/-- No constraints (`m = 0`): feasible and bounded, hence optimal pair. -/
example :
    ∃ x : Fin 1 → ℝ, ∃ y : Fin 0 → ℝ,
      (∀ i, 0 ≤ x i) ∧
      (∀ j, (0 : Matrix (Fin 0) (Fin 1) ℝ).mulVec x j ≤ ![] j) ∧
      (∀ j, 0 ≤ y j) ∧
      (∀ i, (![0] : Fin 1 → ℝ) i ≤
        ((0 : Matrix (Fin 0) (Fin 1) ℝ).transpose.mulVec y) i) ∧
      (![0] : Fin 1 → ℝ) ⬝ᵥ x = ![] ⬝ᵥ y := by
  apply MathlibExt.Analysis.Convex.LPDuality.strong_linear_programming_duality
  · exact ⟨0, fun i => by simp, fun j => j.elim0⟩
  · exact ⟨0, fun x _ _ => by simp [dotProduct]⟩

end LinearProgrammingDualityTest
