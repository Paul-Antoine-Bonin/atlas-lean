module
public import MathlibExt.Combinatorics.SetFamily.TuranSystem
open TuranSystem
theorem valid_332 : IsTuranSystem 3 3 2 (completeGraph 3 2) :=
  completeGraph_isTuran 3 3 2 ⟨by decide, by decide, by decide⟩
theorem valid_s_lt_n : IsTuranSystem 4 3 2 (completeGraph 4 2) :=
  completeGraph_isTuran 4 3 2 ⟨by decide, by decide, by decide⟩
theorem uniform_direct : SetFamily.IsUniform (completeGraph 3 2) 2 :=
  completeGraph_uniform 3 2
theorem uniform_iff_use :
    SetFamily.IsUniform (completeGraph 3 2) 2 ↔
      ∀ e ∈ completeGraph 3 2, e.card = 2 :=
  SetFamily.isUniform_iff (completeGraph 3 2) 2
theorem uniform_explicit :
    SetFamily.IsUniform
      ({({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3))} :
        Finset (Finset (Fin 3))) 2 := by
  refine (SetFamily.isUniform_iff _ _).mpr ?_
  decide
theorem reject_empty_uncovered : ¬ IsTuranSystem 3 3 2 ∅ := by
  intro h
  have hcov := cover_of_isTuran 3 3 2 _ h
  have hT : (Finset.univ : Finset (Fin 3)) ∈
      Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  obtain ⟨e, he, _⟩ := hcov _ hT
  simp at he
theorem reject_wrong_card :
    ¬ IsTuranSystem 3 3 2 ({({0} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  intro h
  have hu := uniform_of_isTuran 3 3 2 _ h
  have hmem :
      ({0} : Finset (Fin 3)) ∈
        ({({0} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by simp
  have h2 := hu _ hmem
  have h1 : ({0} : Finset (Fin 3)).card = 1 := by decide
  omega
theorem direction_edge_sub :
    ∃ e ∈ completeGraph 4 2, e ⊆ ({0, 1, 2} : Finset (Fin 4)) ∧
      ¬ ({0, 1, 2} : Finset (Fin 4)) ⊆ e := by
  refine ⟨({0, 1} : Finset (Fin 4)), ?_, ?_, ?_⟩
  · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  · decide
  · decide
theorem reject_r_zero : ¬ IsTuranSystem 3 3 0 (completeGraph 3 0) := by
  intro h
  have hpos := pos_of_isTuran 3 3 0 _ h
  omega
theorem reject_r_ge_s : ¬ IsTuranSystem 3 2 2 (completeGraph 3 2) := by
  intro h
  have hlt := lt_of_isTuran 3 2 2 _ h
  omega
theorem reject_r_gt_s : ¬ IsTuranSystem 3 2 3 (completeGraph 3 3) := by
  intro h
  have hlt := lt_of_isTuran 3 2 3 _ h
  omega
theorem reject_s_gt_n : ¬ IsTuranSystem 2 3 2 (completeGraph 2 2) := by
  intro h
  have hle := le_of_isTuran 2 3 2 _ h
  omega
theorem uncovered_uniform :
    SetFamily.IsUniform
      ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))) 2 :=
  (SetFamily.isUniform_iff _ _).mpr (by decide)
theorem uncovered_nonempty :
    ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))).Nonempty :=
  Finset.singleton_nonempty _
theorem reject_uncovered_only :
    ¬ IsTuranSystem 4 3 2
      ({({0, 1} : Finset (Fin 4))} : Finset (Finset (Fin 4))) := by
  intro h
  have hcov := cover_of_isTuran 4 3 2 _ h
  have hT : ({1, 2, 3} : Finset (Fin 4)) ∈
      Finset.powersetCard 3 (Finset.univ : Finset (Fin 4)) := by
    refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
    decide
  obtain ⟨e, he, hsub⟩ := hcov _ hT
  have heq : e = ({0, 1} : Finset (Fin 4)) := by simpa using he
  rw [heq] at hsub
  have hfalse : ¬ (({0, 1} : Finset (Fin 4)) ⊆ ({1, 2, 3} : Finset (Fin 4))) := by
    decide
  exact hfalse hsub
theorem realized_direct : (completeGraph 3 2).card ∈ realizedCounts 3 3 2 :=
  (mem_realizedCounts 3 3 2 _).mpr ⟨completeGraph 3 2, valid_332, rfl⟩
theorem exists_system_use : ∃ H, IsTuranSystem 3 3 2 H :=
  exists_system 3 3 2 ⟨by decide, by decide, by decide⟩
theorem realized_nonempty_use : ∃ k, k ∈ realizedCounts 3 3 2 :=
  realizedCounts_nonempty 3 3 2 ⟨by decide, by decide, by decide⟩
theorem turan_mem_use : turanNumber 3 3 2 ∈ realizedCounts 3 3 2 :=
  turanNumber_mem 3 3 2 ⟨by decide, by decide, by decide⟩
theorem turan_attains_use :
    ∃ H, IsTuranSystem 3 3 2 H ∧ H.card = turanNumber 3 3 2 :=
  turanNumber_attains 3 3 2 ⟨by decide, by decide, by decide⟩
theorem turan_le_use : turanNumber 3 3 2 ≤ (completeGraph 3 2).card :=
  turanNumber_le 3 3 2 (completeGraph 3 2) valid_332
theorem one_edge_valid :
    IsTuranSystem 3 3 2
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))) := by
  refine ⟨by decide, by decide, by decide, (SetFamily.isUniform_iff _ _).mpr (by decide), ?_⟩
  intro T hT
  have hTcard : T.card = 3 := (Finset.mem_powersetCard.mp hT).2
  have huniv : (Finset.univ : Finset (Fin 3)).card = 3 := by decide
  have hTsub : T ⊆ (Finset.univ : Finset (Fin 3)) :=
    (Finset.mem_powersetCard.mp hT).1
  have hle : (Finset.univ : Finset (Fin 3)).card ≤ T.card := by rw [hTcard, huniv]
  have hTeq : T = Finset.univ := Finset.eq_of_subset_of_card_le hTsub hle
  exact ⟨({0, 1} : Finset (Fin 3)), by simp, by rw [hTeq]; decide⟩
theorem one_le_card_of_valid (H : Finset (Finset (Fin 3)))
    (h : IsTuranSystem 3 3 2 H) : 1 ≤ H.card := by
  by_contra hcon
  push Not at hcon
  have hzero : H.card = 0 := by omega
  have hempty : H = ∅ := Finset.card_eq_zero.mp hzero
  have hcov := cover_of_isTuran 3 3 2 H h
  have hT : (Finset.univ : Finset (Fin 3)) ∈
      Finset.powersetCard 3 (Finset.univ : Finset (Fin 3)) :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, by decide⟩
  obtain ⟨e, he, _⟩ := hcov _ hT
  rw [hempty] at he
  simp at he
theorem turan_lower_one : 1 ≤ turanNumber 3 3 2 := by
  refine le_turanNumber 3 3 2 1 ?_ ⟨by decide, by decide, by decide⟩
  intro k hk
  obtain ⟨H, hH, rfl⟩ := (mem_realizedCounts 3 3 2 k).mp hk
  exact one_le_card_of_valid H hH
theorem turan_upper_one : turanNumber 3 3 2 ≤ 1 := by
  have hle := turanNumber_le 3 3 2 _ one_edge_valid
  have hcard :
      ({({0, 1} : Finset (Fin 3))} : Finset (Finset (Fin 3))).card = 1 := by
    decide
  omega
theorem turan_eq_one : turanNumber 3 3 2 = 1 :=
  Nat.le_antisymm turan_upper_one turan_lower_one
