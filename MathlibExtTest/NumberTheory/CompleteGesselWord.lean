/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.CompleteGesselWord

namespace MetaMathlibExt

private theorem eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
    {α : Type*} (a b : α) (w' suffix : List α) (h : w' ++ suffix = [a, b]) :
    w' = [] ∨ w' = [a] ∨ w' = [a, b] := by
  cases w' with
  | nil => exact Or.inl rfl
  | cons head tail =>
    simp only [List.cons_append] at h
    rw [List.cons.injEq] at h
    obtain ⟨rfl, htail⟩ := h
    cases tail with
    | nil => exact Or.inr (Or.inl rfl)
    | cons second rest =>
      simp only [List.cons_append] at htail
      rw [List.cons.injEq] at htail
      obtain ⟨rfl, hrest⟩ := htail
      cases rest with
      | nil => exact Or.inr (Or.inr rfl)
      | cons third rest =>
        have := congrArg List.length hrest
        simp at this

/-- The empty word over the empty alphabet is complete. -/
example : IsCompleteGesselWord 0 [] := by
  refine ⟨?_, ?_⟩
  · intro w' suffix _ k _ hkn
    omega
  · intro i
    nomatch i

/-- The balanced one-letter word `1, bar 1` is complete. -/
example : IsCompleteGesselWord 1 [Sum.inl (0 : Fin 1), Sum.inr (0 : Fin 1)] := by
  refine ⟨?_, ?_⟩
  · intro w' suffix h k hk1 hkn
    have hk : k = 1 := by omega
    subst hk
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hp := eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
      (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1)) w' suffix h
    rcases hp with rfl | rfl | rfl <;> decide
  · decide

/-- The unbalanced one-letter word `1` is not complete. -/
example : ¬ IsCompleteGesselWord 1 [Sum.inl (0 : Fin 1)] := by
  intro h
  obtain ⟨_, hcount⟩ := h
  exact absurd (hcount ⟨0, by decide⟩) (by decide)

end MetaMathlibExt
