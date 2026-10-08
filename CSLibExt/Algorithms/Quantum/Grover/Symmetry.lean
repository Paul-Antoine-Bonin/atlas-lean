/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Grover.Diffusion

/-!
# The symmetric subspace of Grover search

A state is symmetric when every marked outcome has one common amplitude and
every unmarked outcome has another. The standard Grover step preserves this
two-dimensional subspace. The recurrence here is the finite-state form of the
recurrence in Boyer, Brassard, Høyer, and Tapp.
-/

@[expose] public section

open scoped BigOperators

namespace Cslib.Grover

/-- An amplitude vector constant on the marked and unmarked outcomes. -/
def symmetricAmplitude {α : Type*} [DecidableEq α] (marked : Finset α)
    (markedAmplitude unmarkedAmplitude : ℝ) : Amplitude α :=
  fun x => if x ∈ marked then markedAmplitude else unmarkedAmplitude

@[simp]
theorem symmetricAmplitude_apply_of_mem {α : Type*} [DecidableEq α]
    (marked : Finset α) (a b : ℝ) {x : α} (hx : x ∈ marked) :
    symmetricAmplitude marked a b x = a := by
  simp [symmetricAmplitude, hx]

@[simp]
theorem symmetricAmplitude_apply_of_not_mem {α : Type*} [DecidableEq α]
    (marked : Finset α) (a b : ℝ) {x : α} (hx : x ∉ marked) :
    symmetricAmplitude marked a b x = b := by
  simp [symmetricAmplitude, hx]

theorem phaseOracle_symmetricAmplitude {α : Type*} [DecidableEq α]
    (marked : Finset α) (a b : ℝ) :
    phaseOracle marked (symmetricAmplitude marked a b) =
      symmetricAmplitude marked (-a) b := by
  funext x
  by_cases hx : x ∈ marked <;> simp [phaseOracle, symmetricAmplitude, hx]

theorem sum_symmetricAmplitude {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (a b : ℝ) :
    (∑ x, symmetricAmplitude marked a b x) =
      (marked.card : ℝ) * a + (markedᶜ.card : ℝ) * b := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => x ∈ marked) (symmetricAmplitude marked a b)]
  have hmarked : Finset.univ.filter (fun x => x ∈ marked) = marked := by
    ext x
    simp
  have hunmarked : Finset.univ.filter (fun x => x ∉ marked) = markedᶜ := by
    ext x
    simp
  rw [hmarked, hunmarked]
  have hsMarked :
      (∑ x ∈ marked, symmetricAmplitude marked a b x) =
        ∑ _x ∈ marked, a := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [symmetricAmplitude, hx]
  have hsUnmarked :
      (∑ x ∈ markedᶜ, symmetricAmplitude marked a b x) =
        ∑ _x ∈ markedᶜ, b := by
    apply Finset.sum_congr rfl
    intro x hx
    have hnot : x ∉ marked := Finset.mem_compl.mp hx
    simp [symmetricAmplitude, hnot]
  rw [hsMarked, hsUnmarked]
  norm_num [nsmul_eq_mul]

theorem meanAmplitude_symmetricAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (a b : ℝ) :
    meanAmplitude (symmetricAmplitude marked a b) =
      ((marked.card : ℝ) * a + (markedᶜ.card : ℝ) * b) /
        Fintype.card α := by
  rw [meanAmplitude, sum_symmetricAmplitude]

/-- Mean after phase inversion of a symmetric state. -/
noncomputable def oracleMean {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (a b : ℝ) : ℝ :=
  ((markedᶜ.card : ℝ) * b - (marked.card : ℝ) * a) /
    Fintype.card α

theorem meanAmplitude_phaseOracle_symmetricAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (a b : ℝ) :
    meanAmplitude (phaseOracle marked (symmetricAmplitude marked a b)) =
      oracleMean marked a b := by
  rw [phaseOracle_symmetricAmplitude, meanAmplitude_symmetricAmplitude]
  unfold oracleMean
  ring

/-- Common marked amplitude after one Grover step. -/
noncomputable def markedAmplitudeNext {α : Type*} [Fintype α] [DecidableEq α]
    (marked : Finset α) (a b : ℝ) : ℝ :=
  2 * oracleMean marked a b + a

/-- Common unmarked amplitude after one Grover step. -/
noncomputable def unmarkedAmplitudeNext {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (a b : ℝ) : ℝ :=
  2 * oracleMean marked a b - b

theorem groverStep_symmetricAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (a b : ℝ) :
    groverStep marked (symmetricAmplitude marked a b) =
      symmetricAmplitude marked (markedAmplitudeNext marked a b)
        (unmarkedAmplitudeNext marked a b) := by
  funext x
  rw [groverStep_apply, meanAmplitude_phaseOracle_symmetricAmplitude]
  by_cases hx : x ∈ marked
  · simp [phaseOracle, symmetricAmplitude, markedAmplitudeNext, hx]
  · simp [phaseOracle, symmetricAmplitude, unmarkedAmplitudeNext, hx]

theorem markedProbability_symmetricAmplitude {α : Type*} [DecidableEq α]
    (marked : Finset α) (a b : ℝ) :
    markedProbability marked (symmetricAmplitude marked a b) =
      (marked.card : ℝ) * a ^ 2 := by
  unfold markedProbability
  have hs :
      (∑ x ∈ marked, (symmetricAmplitude marked a b x) ^ 2) =
        ∑ _x ∈ marked, a ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [symmetricAmplitude, hx]
  rw [hs]
  norm_num [nsmul_eq_mul]

theorem amplitudeNormSq_symmetricAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) (a b : ℝ) :
    amplitudeNormSq (symmetricAmplitude marked a b) =
      (marked.card : ℝ) * a ^ 2 + (markedᶜ.card : ℝ) * b ^ 2 := by
  unfold amplitudeNormSq
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun x => x ∈ marked) (fun x => (symmetricAmplitude marked a b x) ^ 2)]
  have hmarked : Finset.univ.filter (fun x => x ∈ marked) = marked := by
    ext x
    simp
  have hunmarked : Finset.univ.filter (fun x => x ∉ marked) = markedᶜ := by
    ext x
    simp
  rw [hmarked, hunmarked]
  have hsMarked :
      (∑ x ∈ marked, (symmetricAmplitude marked a b x) ^ 2) =
        ∑ _x ∈ marked, a ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [symmetricAmplitude, hx]
  have hsUnmarked :
      (∑ x ∈ markedᶜ, (symmetricAmplitude marked a b x) ^ 2) =
        ∑ _x ∈ markedᶜ, b ^ 2 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hnot : x ∉ marked := Finset.mem_compl.mp hx
    simp [symmetricAmplitude, hnot]
  rw [hsMarked, hsUnmarked]
  norm_num [nsmul_eq_mul]

theorem uniformAmplitude_eq_symmetricAmplitude {α : Type*} [Fintype α]
    [DecidableEq α] (marked : Finset α) :
    uniformAmplitude α =
      symmetricAmplitude marked (1 / Real.sqrt (Fintype.card α))
        (1 / Real.sqrt (Fintype.card α)) := by
  funext x
  by_cases hx : x ∈ marked <;> simp [symmetricAmplitude, hx]

theorem markedProbability_groverStep_symmetricAmplitude {α : Type*}
    [Fintype α] [DecidableEq α] (marked : Finset α) (a b : ℝ) :
    markedProbability marked
        (groverStep marked (symmetricAmplitude marked a b)) =
      (marked.card : ℝ) * (markedAmplitudeNext marked a b) ^ 2 := by
  rw [groverStep_symmetricAmplitude, markedProbability_symmetricAmplitude]

end Cslib.Grover
