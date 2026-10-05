module

import MathlibExt.Combinatorics.JaccardLattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace JaccardLatticeTest

open JaccardLattice

/-- Shifted counting valuation on `ℕ` for compile-time checks. -/
private noncomputable def countVal : ℕ → ℝ := fun n => (n : ℝ) + 1

private theorem countVal_pos : IsStrictlyPositive countVal := by
  intro X
  unfold countVal
  have hnn : (0 : ℝ) ≤ ((X : ℕ) : ℝ) := Nat.cast_nonneg X
  linarith

private theorem countVal_mono : Monotone countVal := by
  intro X Y hXY
  unfold countVal
  have hc : ((X : ℕ) : ℝ) ≤ ((Y : ℕ) : ℝ) := Nat.cast_le.mpr hXY
  linarith

private theorem countVal_mod : IsModularValuation countVal := by
  intro X Y
  rcases le_total X Y with h | h
  · have hSup : X ⊔ Y = Y := le_antisymm (sup_le h le_rfl) le_sup_right
    have hInf : X ⊓ Y = X := le_antisymm inf_le_left (le_inf le_rfl h)
    rw [hSup, hInf]
    exact add_comm _ _
  · have hSup : X ⊔ Y = X := le_antisymm (sup_le le_rfl h) le_sup_left
    have hInf : X ⊓ Y = Y := le_antisymm inf_le_right (le_inf h le_rfl)
    rw [hSup, hInf]

private theorem countVal_01 : jaccardDist countVal 0 1 = 1 / 2 := by
  have hi : (0 : ℕ) ⊓ 1 = 0 :=
    le_antisymm inf_le_left (le_inf le_rfl (Nat.zero_le 1))
  have hs : (0 : ℕ) ⊔ 1 = 1 :=
    le_antisymm (sup_le (Nat.zero_le 1) le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

private theorem countVal_12 : jaccardDist countVal 1 2 = 1 / 3 := by
  have hle : (1 : ℕ) ≤ 2 := by decide
  have hi : (1 : ℕ) ⊓ 2 = 1 := le_antisymm inf_le_left (le_inf le_rfl hle)
  have hs : (1 : ℕ) ⊔ 2 = 2 := le_antisymm (sup_le hle le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

private theorem countVal_02 : jaccardDist countVal 0 2 = 2 / 3 := by
  have hi : (0 : ℕ) ⊓ 2 = 0 :=
    le_antisymm inf_le_left (le_inf le_rfl (Nat.zero_le 2))
  have hs : (0 : ℕ) ⊔ 2 = 2 :=
    le_antisymm (sup_le (Nat.zero_le 2) le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

example : 0 < jaccardDist countVal 0 1 := by
  rw [countVal_01]
  norm_num

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    ≥ jaccardDist countVal 0 2 :=
  jaccardDist_triangle countVal_mod countVal_mono countVal_pos 0 2 1

example : jaccardDist countVal 0 1 + jaccardDist countVal 1 2
    > jaccardDist countVal 0 2 := by
  rw [countVal_01, countVal_12, countVal_02]
  norm_num

end JaccardLatticeTest
