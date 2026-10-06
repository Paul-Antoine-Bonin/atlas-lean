module

public import MathlibExt.Geometry.Manifold.MorseTheory

open MathlibExt.Geometry.Manifold.MorseTheoryWanted

@[expose] public section

-- n = 0: the form on the zero-dimensional space is the empty sum, hence zero.
example (k : ℕ) (v : EuclideanSpace ℝ (Fin 0)) : morseQuadratic k 0 v = 0 := by
  simp [morseQuadratic]

-- k = 0 through the squared-norm lemma.
example (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic 0 n v = ‖v‖ ^ 2 :=
  morseQuadratic_zero_index n v

-- k = n through the minus-squared-norm lemma.
example (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    morseQuadratic n n v = -‖v‖ ^ 2 :=
  morseQuadratic_of_le le_rfl v

-- explicit small evaluation at index 1 in dimension 2.
example (v : EuclideanSpace ℝ (Fin 2)) :
    morseQuadratic 1 2 v = -(v 0) ^ 2 + (v 1) ^ 2 := by
  simp [morseQuadratic, Fin.sum_univ_two]

-- the form vanishes at the origin.
example (k n : ℕ) : morseQuadratic k n 0 = 0 :=
  morseQuadratic_zero k n

end
