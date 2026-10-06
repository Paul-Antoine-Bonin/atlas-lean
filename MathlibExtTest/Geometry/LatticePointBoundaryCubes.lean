module

import MathlibExt.Geometry.LatticePointBoundaryCubes

/-!
# Tests for boundary-cube inclusion and cardinality bound

Concrete checks for `LatticePointBoundaryCubes`:

- Generic uses of both theorems on abstract sets and chart families.
- A singleton/constant-chart example where cube `0` genuinely lies in
  outer-minus-inner, also lies in the chart integer-cube set, and feeds both
  theorems at concrete parameters.
-/

open LatticePointBoundaryCubes LatticePointCubeSandwich
  LipschitzImageCubeCount

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

/-- Cube `0` meets the scaled singleton at `t = 1`. -/
theorem v0_mem_outer :
    (fun _ => (0 : ℤ)) ∈ outerCubeSet ({0} : Set (Fin 1 → ℝ)) 1 := by
  rw [mem_outerCubeSet_iff]
  refine ⟨fun _ => 0, ?_, ?_⟩
  · rw [mem_integerUnitCube_iff]
    intro i
    simp
  · rw [Set.mem_singleton_iff]
    funext i
    simp

/-- Cube `0` is not fully inside the scaled singleton at `t = 1`. -/
theorem v0_not_mem_inner :
    (fun _ => (0 : ℤ)) ∉ innerCubeSet ({0} : Set (Fin 1 → ℝ)) 1 := by
  rw [mem_innerCubeSet_iff]
  push Not
  refine ⟨fun _ => 1 / 2, ?_, ?_⟩
  · rw [mem_integerUnitCube_iff]
    intro i
    norm_num
  · rw [Set.mem_singleton_iff]
    intro h
    have h0 := congr_fun h 0
    norm_num at h0

/-- Cube `0` genuinely witnesses outer-minus-inner for the singleton. -/
theorem v0_mem_diff :
    (fun _ => (0 : ℤ)) ∈ outerCubeSet ({0} : Set (Fin 1 → ℝ)) 1 \
      innerCubeSet ({0} : Set (Fin 1 → ℝ)) 1 :=
  ⟨v0_mem_outer, v0_not_mem_inner⟩

/-- Cube `0` also lies in the constant-chart integer-cube set. -/
example : (fun _ => (0 : ℤ)) ∈ integerCubeSet (singletonChart 0) 1 := by
  rw [mem_integerCubeSet_iff]
  refine ⟨⟨0, unitCube_zero_mem 0⟩, fun i => ?_⟩
  simp [singletonChart]

/-- The witness lands in the chart union via the inclusion theorem. -/
example : (fun _ => (0 : ℤ)) ∈ ⋃ i, integerCubeSet (singletonChart i) 1 :=
  outer_diff_inner_subset_iUnion_integerCubeSet _ _ cover_singleton
    v0_mem_diff

/-- Zero-scale inclusion on the singleton example (exercises `t = 0`). -/
example : outerCubeSet ({0} : Set (Fin 1 → ℝ)) 0 \
    innerCubeSet ({0} : Set (Fin 1 → ℝ)) 0 ⊆
    ⋃ i, integerCubeSet (singletonChart i) 0 :=
  outer_diff_inner_subset_iUnion_integerCubeSet _ _ cover_singleton

/-- Generic use of the boundary inclusion. -/
example {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ} :
    outerCubeSet S t \ innerCubeSet S t ⊆
      ⋃ i, integerCubeSet (maps i) t :=
  outer_diff_inner_subset_iUnion_integerCubeSet S maps hCover

/-- Generic use of the cardinality bound. -/
example {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i))
    {t : ℝ}
    (hFinOuter : (outerCubeSet S t).Finite)
    (hFinMaps : ∀ i, (integerCubeSet (maps i) t).Finite) :
    Nat.card (outerCubeSet S t) ≤ Nat.card (innerCubeSet S t) +
      ∑ i, Nat.card (integerCubeSet (maps i) t) :=
  card_outer_le_card_inner_add_sum S maps hCover hFinOuter hFinMaps

/-- Generic zero-scale use of the inclusion (exercises the `t = 0` branch). -/
example {n d numMaps : ℕ} (S : Set (Fin n → ℝ))
    (maps : Fin numMaps → (↥(unitCube d) → (Fin n → ℝ)))
    (hCover : frontier S ⊆ ⋃ i, Set.range (maps i)) :
    outerCubeSet S 0 \ innerCubeSet S 0 ⊆
      ⋃ i, integerCubeSet (maps i) 0 :=
  outer_diff_inner_subset_iUnion_integerCubeSet S maps hCover

/-- The singleton origin is bounded. -/
theorem singleton_origin_bounded :
    Bornology.IsBounded ({0} : Set (Fin 1 → ℝ)) :=
  Bornology.isBounded_singleton

/-- Concrete cardinality-bound invocation on the singleton example. -/
example : Nat.card (outerCubeSet ({0} : Set (Fin 1 → ℝ)) 1) ≤
    Nat.card (innerCubeSet ({0} : Set (Fin 1 → ℝ)) 1) +
      ∑ i : Fin 1, Nat.card (integerCubeSet (singletonChart i) 1) := by
  apply card_outer_le_card_inner_add_sum _ _ cover_singleton
  · exact finite_outerCubeSet _ singleton_origin_bounded one_pos
  · intro i
    exact finite_integerCubeSet _ 0 (LipschitzWith.const' _) 1 le_rfl
