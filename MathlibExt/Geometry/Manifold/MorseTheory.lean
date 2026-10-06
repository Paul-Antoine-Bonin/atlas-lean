/-
Authors: @toskua, Avocado, Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FunProp

@[expose] public section

namespace MathlibExt.Geometry.Manifold.MorseTheoryWanted

/-- Morse quadratic form `Q_k(v) = ∑ (if i < k then -1 else 1) * (v i)^2` on `ℝ^n`. -/
def morseQuadratic (k n : ℕ) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1) * (v i) ^ 2

/-- The Morse quadratic form vanishes at the origin. -/
lemma morseQuadratic_zero (k n : ℕ) : morseQuadratic k n 0 = 0 := by
  simp [morseQuadratic]

/-- The Morse quadratic form is smooth. -/
lemma contDiff_morseQuadratic (k n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (morseQuadratic k n) := by
  unfold morseQuadratic
  fun_prop

/-- With index zero the form is the squared norm. -/
lemma morseQuadratic_zero_index (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic 0 n v = ‖v‖ ^ 2 := by
  have hone : ∀ i : Fin n, (if (i : ℕ) < 0 then (-1 : ℝ) else 1) = 1 := by
    intro i
    simp
  simp only [morseQuadratic, hone, one_mul]
  exact (EuclideanSpace.real_norm_sq_eq v).symm

/-- If `n ≤ k` the form is minus the squared norm. -/
lemma morseQuadratic_of_le {k n : ℕ} (h : n ≤ k) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic k n v = -‖v‖ ^ 2 := by
  have hif : ∀ i : Fin n, (if (i : ℕ) < k then (-1 : ℝ) else 1) = -1 := by
    intro i
    simp [lt_of_lt_of_le i.is_lt h]
  simp only [morseQuadratic, hif, neg_one_mul, Finset.sum_neg_distrib]
  rw [EuclideanSpace.real_norm_sq_eq]

end MathlibExt.Geometry.Manifold.MorseTheoryWanted
