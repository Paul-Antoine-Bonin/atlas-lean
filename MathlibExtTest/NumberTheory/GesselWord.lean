module

import MathlibExt.NumberTheory.GesselWord
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

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

/-- The empty word over the empty alphabet is a Gessel word. -/
example : IsGesselWord 0 [] := by
  intro w' suffix _ k _ hkn
  omega

/-- The source's word `2, bar 1` is a Gessel word over `[2]`. -/
example : IsGesselWord 2 [Sum.inl (1 : Fin 2), Sum.inr (0 : Fin 2)] := by
  intro w' suffix h k hk1 hkn
  have hp := eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
    (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)) w' suffix h
  rcases hp with rfl | rfl | rfl <;> interval_cases k <;> decide

/-- The source's word `1, bar 2` is not a Gessel word over `[2]`. -/
example : ¬ IsGesselWord 2 [Sum.inl (0 : Fin 2), Sum.inr (1 : Fin 2)] := by
  intro h
  have hbad := h [Sum.inl (0 : Fin 2), Sum.inr (1 : Fin 2)] [] (by simp) 1
    (by decide) (by decide)
  norm_num [gesselBalance, gesselUnbarredCount, gesselBarredCount] at hbad

end MetaMathlibExt
