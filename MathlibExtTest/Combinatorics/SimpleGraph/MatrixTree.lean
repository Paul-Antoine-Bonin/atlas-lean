module

public import MathlibExt.Combinatorics.SimpleGraph.MatrixTree

@[expose] public section

/-!
# Tests for the matrix-tree theorem public API

Exercises the reduced-Laplacian entries and the determinant/count agreement on
boundary cases (singleton, single edge, disconnected graph), using only public
declarations.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

/-- Single edge: the reduced Laplacian entry is the endpoint degree. -/
theorem matrixTreeTest_entry_singleEdge :
    reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by
  decide

/-- Disconnected pair: the reduced Laplacian entry is zero. -/
theorem matrixTreeTest_entry_disconnected :
    reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩ = 0 := by
  decide

/-- Reduced entries agree with Mathlib's `lapMatrix` entries. -/
theorem matrixTreeTest_entry_eq_lapMatrix :
    reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 ⟨1, by decide⟩ ⟨1, by decide⟩
      = (⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ 1 1 := by
  rw [reducedLaplacian_eq_lapMatrix_submatrix, Matrix.submatrix_apply]

/-- Singleton graph: the reduced (empty) Laplacian has determinant one. -/
theorem matrixTreeTest_det_singleton :
    (reducedLaplacian (⊥ : SimpleGraph (Fin 1)) 0).det = 1 := by
  decide

/-- Single edge: the reduced Laplacian has determinant one. -/
theorem matrixTreeTest_det_singleEdge :
    (reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0).det = 1 := by
  decide

/-- Disconnected pair: the reduced Laplacian has determinant zero. -/
theorem matrixTreeTest_det_disconnected :
    (reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0).det = 0 := by
  decide

/-- The promoted theorem applies to a single edge without unfolding proofs. -/
example : (reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0).det
    = (numSpanningTrees (⊤ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree _ _

/-- The `Nonempty`-free theorem applies to a disconnected graph. -/
example : (reducedLaplacian (⊥ : SimpleGraph (Fin 2)) 0).det
    = (numSpanningTrees (⊥ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree_of_root _ _

/-- The `lapMatrix`-stated theorem applies to a single edge. -/
example : (((⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ).submatrix
    (Subtype.val : { v : Fin 2 // v ≠ 0 } → Fin 2)
    (Subtype.val : { v : Fin 2 // v ≠ 0 } → Fin 2)).det
    = (numSpanningTrees (⊤ : SimpleGraph (Fin 2)) : ℤ) :=
  kirchhoff_matrix_tree_lapMatrix _ _

/-- The Laplacian bridge applies to a single edge. -/
example : laplacianInt (⊤ : SimpleGraph (Fin 2)) = (⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ :=
  laplacianInt_eq_lapMatrix _

/-- The reduced-Laplacian bridge applies to a single edge. -/
example : reducedLaplacian (⊤ : SimpleGraph (Fin 2)) 0 =
    ((⊤ : SimpleGraph (Fin 2)).lapMatrix ℤ).submatrix Subtype.val Subtype.val :=
  reducedLaplacian_eq_lapMatrix_submatrix _ _

/-- The count characterization applies to a single edge. -/
example : numSpanningTrees (⊤ : SimpleGraph (Fin 2))
    = Nat.card {H : SimpleGraph (Fin 2) // H ≤ ⊤ ∧ H.IsTree} :=
  numSpanningTrees_eq_card_trees _

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

end
