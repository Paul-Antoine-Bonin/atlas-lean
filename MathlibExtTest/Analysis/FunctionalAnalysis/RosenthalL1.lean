module

import MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1

open MathlibExt.Analysis.FunctionalAnalysis.RosenthalL1Wanted

-- A bounded sequence with no weakly Cauchy subsequence has an `ℓ¹` subsequence.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (x : ℕ → E) (hx : Bornology.IsBounded (Set.range x))
    (hno : ∀ (φ : ℕ → ℕ), StrictMono φ →
      ¬∀ (f : E →L[ℝ] ℝ) (epsilon : ℝ), 0 < epsilon →
        ∃ N, ∀ m n, N ≤ m → N ≤ n →
          ‖f (x (φ m)) - f (x (φ n))‖ < epsilon) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ HasUniformL1LowerBound (𝕜 := ℝ) (x ∘ φ) := by
  obtain ⟨φ, hφ, hweak | hl1⟩ := rosenthal_l1 (𝕜 := ℝ) x hx
  · exact (hno φ hφ hweak).elim
  · exact ⟨φ, hφ, hl1⟩
