module

public import MathlibExt.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
import Mathlib.Tactic.NormNum

@[expose] public section

open scoped BigOperators

namespace MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder

theorem catalan_recurrence_aux (m : ℕ) :
    catalan (m + 2) = 2 * catalan (m + 1) +
      ∑ k ∈ Finset.range m, catalan (k + 1) * catalan (m - k) := by
  rw [show m + 2 = (m + 1) + 1 by omega, catalan_succ',
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ,
    Finset.sum_range_succ']
  simp only [Nat.add_sub_add_right, Nat.sub_zero, catalan_zero, one_mul, Nat.sub_self, mul_one]
  omega

theorem catalan_recurrence_rat : ∀ n : ℕ, 2 ≤ n →
    (catalan n : ℚ) = 2 * (catalan (n - 1) : ℚ) +
      ∑ k ∈ Finset.range (n - 2),
        (catalan (k + 1) : ℚ) * (catalan (n - k - 2) : ℚ) := by
  intro n hn
  have hnat : catalan n = 2 * catalan (n - 1) +
      ∑ k ∈ Finset.range (n - 2), catalan (k + 1) * catalan (n - k - 2) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hn
    have hn' : n = m + 2 := by omega
    rw [hn']
    have hsum :
        (∑ k ∈ Finset.range (m + 2 - 2),
          catalan (k + 1) * catalan (m + 2 - k - 2)) =
            ∑ k ∈ Finset.range m, catalan (k + 1) * catalan (m - k) := by
      apply Finset.sum_congr
      · congr 1
      · intro k hk
        congr 2
        simp only [Finset.mem_range] at hk
        omega
    rw [hsum]
    simpa only [show m + 2 - 1 = m + 1 by omega] using catalan_recurrence_aux m
  exact_mod_cast hnat

-- The Catalan specialization has `g = 1` and `f = X`.
example :
    PowerSeries.mk (fun n => (catalan n : ℚ)) =
      (1 : PowerSeries ℚ) * PowerSeries.subst PowerSeries.X
        (PowerSeries.mk (fun n => (catalan n : ℚ))) := by
  apply MetaMathlibExt.generalizedCatalanSchroeder_generatingFunction
      (R := ℚ) (s := 2) (t := 1) (p := 1)
  · norm_num
  · norm_num
  · intro n hn
    simpa using catalan_recurrence_rat n hn
  · norm_num
  · norm_num

-- The public recurrence lemma gives the Catalan quadratic functional equation.
example :
    PowerSeries.mk (fun n => (catalan n : ℚ)) - 1 =
      PowerSeries.C (1 : ℚ) * PowerSeries.X +
        PowerSeries.C (2 : ℚ) * PowerSeries.X *
          (PowerSeries.mk (fun n => (catalan n : ℚ)) - 1) +
            PowerSeries.C (1 : ℚ) * PowerSeries.X *
              (PowerSeries.mk (fun n => (catalan n : ℚ)) - 1) ^ 2 := by
  apply MetaMathlibExt.generalizedCatalanSchroeder_recurrence_functionalEquation
  · norm_num
  · norm_num
  · intro n hn
    simpa using catalan_recurrence_rat n hn

end MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
