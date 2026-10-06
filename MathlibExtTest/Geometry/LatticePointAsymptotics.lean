module

import MathlibExt.Geometry.LatticePointAsymptotics

/-!
# Tests for the lattice-point error bound and eventual asymptotics

Concrete checks for `LatticePointAsymptotics`, stated through the canonical
`LatticePointEnumerator.latticeEnumerator`:

- Generic uses of both theorems on abstract sets and chart families.
- A singleton/constant-chart error-bound invocation at `t = 1`.
- The empty set as a final-asymptotics example, exercising the zero-chart case.
- The compatibility bridge: the raw integer subtype agrees with the canonical
  enumerator, and the bridge equiv is mutually inverse on a singleton example.
-/

open LatticePointAsymptotics LatticePointCubeSandwich LipschitzImageCubeCount

namespace LatticePointAsymptoticsTests

/-- Generic use of the canonical error bound. -/
example {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ} (ht : 0 < t)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    ‖(LatticePointEnumerator.latticeEnumerator n S t : ℝ) -
      (MeasureTheory.volume S).toReal * t ^ n‖ ≤
      ∑ i, (Nat.card (integerCubeSet (maps i) t) : ℝ) :=
  lattice_point_count_error_bound S hS maps hCover ht hFinMaps

/-- Generic use of the canonical eventual asymptotics. -/
example {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : Bornology.IsBounded S)
    (hS_bdry : IsLipschitzParametrizable (n - 1) (frontier S)) :
    ∃ C : ℝ, ∀ᶠ t in Filter.atTop,
      ‖(LatticePointEnumerator.latticeEnumerator n S t : ℝ) -
        (MeasureTheory.volume S).toReal * t ^ n‖ ≤ C * t ^ (n - 1) :=
  lattice_point_count_asymptotics S hS hS_bdry

/-- Bridge: the raw integer count equals the canonical enumerator for `0 < t`. -/
example {n : ℕ} (S : Set (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) :
    Nat.card {x : Fin n → ℤ | (fun i => (x i : ℝ) / t) ∈ S} =
      LatticePointEnumerator.latticeEnumerator n S t :=
  card_raw_eq_latticeEnumerator S ht

/-- Constant zero chart out of the 0-dimensional cube. -/
def singletonChart : Fin 1 → (↥(unitCube 0) → (Fin 1 → ℝ)) :=
  fun _ _ => 0

/-- The singleton origin has its frontier covered by the constant chart. -/
theorem cover_singleton :
    frontier ({0} : Set (Fin 1 → ℝ)) ⊆
      ⋃ i, Set.range (singletonChart i) := by
  intro x hx
  rw [Set.mem_iUnion]
  have hcl := frontier_subset_closure hx
  rw [closure_singleton, Set.mem_singleton_iff] at hcl
  exact ⟨0, ⟨0, unitCube_zero_mem 0⟩, by simp [singletonChart, hcl]⟩

/-- Concrete singleton canonical error-bound invocation at `t = 1`. -/
example : ‖(LatticePointEnumerator.latticeEnumerator 1
      ({0} : Set (Fin 1 → ℝ)) 1 : ℝ) -
      (MeasureTheory.volume ({0} : Set (Fin 1 → ℝ))).toReal * 1 ^ 1‖ ≤
      ∑ i : Fin 1, (Nat.card (integerCubeSet (singletonChart i) 1) : ℝ) := by
  refine lattice_point_count_error_bound _ Bornology.isBounded_singleton _
    cover_singleton one_pos ?_
  intro i
  exact finite_integerCubeSet _ 0 (LipschitzWith.const' _) 1 le_rfl

/-- Bridge round-trip on the singleton example at `t = 1`. -/
example (x : {x : Fin 1 → ℤ | (fun i => (x i : ℝ) / 1) ∈
    ({0} : Set (Fin 1 → ℝ))}) :
    (rawSubtypeEquivCanonicalPointSet ({0} : Set (Fin 1 → ℝ)) one_pos).invFun
      ((rawSubtypeEquivCanonicalPointSet ({0} : Set (Fin 1 → ℝ)) one_pos) x) =
      x :=
  Equiv.left_inv _ x

/-- The empty set satisfies the canonical final asymptotics via the zero-chart case. -/
example {n : ℕ} : ∃ C : ℝ, ∀ᶠ t in Filter.atTop,
    ‖(LatticePointEnumerator.latticeEnumerator n (∅ : Set (Fin n → ℝ)) t : ℝ) -
      (MeasureTheory.volume (∅ : Set (Fin n → ℝ))).toReal * t ^ n‖ ≤
      C * t ^ (n - 1) := by
  refine lattice_point_count_asymptotics ∅ ?_ ?_
  · simp
  · simpa using isLipschitzParametrizable_empty (n - 1)

end LatticePointAsymptoticsTests
