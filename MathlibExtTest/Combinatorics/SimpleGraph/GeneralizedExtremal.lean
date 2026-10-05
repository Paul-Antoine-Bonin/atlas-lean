module


import MathlibExt.Combinatorics.SimpleGraph.GeneralizedExtremal

open SimpleGraph

variable {α β : Type*} [Fintype α]
variable (T : SimpleGraph α) (H : SimpleGraph β)
variable (n : ℕ)
variable (G : SimpleGraph (Fin n)) (hG : H.Free G)
variable (m : ℕ)

example : G.copyCount T ≤ generalizedExtremalNumber n T H :=
  copyCount_le_generalizedExtremalNumber n T H G hG

open Classical in
example : generalizedExtremalNumber n T H =
    Finset.sup (Finset.univ.filter (fun G : SimpleGraph (Fin n) => H.Free G))
      (fun G => G.copyCount T) :=
  generalizedExtremalNumber_eq_sup n T H

example : generalizedExtremalNumber n T H ≤ m ↔
    ∀ G : SimpleGraph (Fin n), H.Free G → G.copyCount T ≤ m :=
  generalizedExtremalNumber_le_iff n T H m

example : ∃ G : SimpleGraph (Fin n), H.Free G ∧ G.copyCount T = generalizedExtremalNumber n T H :=
  exists_free_copyCount_eq_generalizedExtremalNumber n T H ⟨G, hG⟩

private theorem concrete_K3_free_in_K2 :
    (completeGraph (Fin 3)).Free (completeGraph (Fin 2)) := by
  intro h
  obtain ⟨c⟩ := h
  have hle : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_embedding c.toEmbedding
  exact absurd hle (by decide)

private theorem concrete_K3_free_all_Fin2 (G : SimpleGraph (Fin 2)) :
    (completeGraph (Fin 3)).Free G := by
  intro h
  obtain ⟨c⟩ := h
  have hle : Fintype.card (Fin 3) ≤ Fintype.card (Fin 2) :=
    Fintype.card_le_of_embedding c.toEmbedding
  exact absurd hle (by decide)

example : (completeGraph (Fin 2)).copyCount (completeGraph (Fin 2)) ≤
    generalizedExtremalNumber 2 (completeGraph (Fin 2)) (completeGraph (Fin 3)) :=
  copyCount_le_generalizedExtremalNumber 2 _ _ _ concrete_K3_free_in_K2

open Classical in
example : generalizedExtremalNumber 2 (completeGraph (Fin 2)) (completeGraph (Fin 3)) =
    Finset.sup
      (Finset.univ.filter (fun G : SimpleGraph (Fin 2) => (completeGraph (Fin 3)).Free G))
      (fun G => G.copyCount (completeGraph (Fin 2))) :=
  generalizedExtremalNumber_eq_sup 2 _ _

example : generalizedExtremalNumber 2 (completeGraph (Fin 2)) (completeGraph (Fin 3)) ≤ m ↔
    ∀ G : SimpleGraph (Fin 2),
      (completeGraph (Fin 3)).Free G → G.copyCount (completeGraph (Fin 2)) ≤ m :=
  generalizedExtremalNumber_le_iff 2 _ _ m

example : ∃ G : SimpleGraph (Fin 2), (completeGraph (Fin 3)).Free G ∧
    G.copyCount (completeGraph (Fin 2)) =
    generalizedExtremalNumber 2 (completeGraph (Fin 2)) (completeGraph (Fin 3)) :=
  exists_free_copyCount_eq_generalizedExtremalNumber 2 _ _ ⟨_, concrete_K3_free_in_K2⟩

private theorem concrete_copyCount_K3_on_Fin2_eq_zero (G : SimpleGraph (Fin 2)) :
    G.copyCount (completeGraph (Fin 3)) = 0 :=
  SimpleGraph.copyCount_eq_zero.mpr (concrete_K3_free_all_Fin2 G)

example : generalizedExtremalNumber 2 (completeGraph (Fin 3)) (completeGraph (Fin 2)) = 0 := by
  rw [← Nat.le_zero, generalizedExtremalNumber_le_iff]
  intro G _
  exact (concrete_copyCount_K3_on_Fin2_eq_zero G).le

#print axioms SimpleGraph.copyCount_le_generalizedExtremalNumber
#print axioms SimpleGraph.generalizedExtremalNumber_eq_sup
#print axioms SimpleGraph.generalizedExtremalNumber_le_iff
#print axioms SimpleGraph.exists_free_copyCount_eq_generalizedExtremalNumber
