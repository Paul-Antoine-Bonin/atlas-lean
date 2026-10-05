module

public import MathlibExt.Combinatorics.SelfGeneratingSet

@[expose]
public section

open scoped Classical

namespace MetaMathlibExt.SelfGeneratingSet

/-!
Tests for the self-generating set API using seed `0` and the successor generator.
-/

private theorem succ_strictGrowth : StrictGrowth {fun n => n + 1} := by
  intro f hf x
  have hf' : f = (fun n => n + 1) := Finset.mem_singleton.mp hf
  rw [hf']
  exact Nat.lt_succ_self x

example : (0 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 :=
  Gen.seed_mem

example : (1 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 := by
  have h0 : Gen {fun n => n + 1} 0 0 := Gen.seed_mem
  exact Gen.step 0 h0 (fun n => n + 1) (Finset.mem_singleton_self _)

example : (3 : Nat) ∈ GeneratedSet {fun n => n + 1} 0 := by
  have h0 : Gen {fun n => n + 1} 0 0 := Gen.seed_mem
  have h1 := Gen.step 0 h0 (fun n => n + 1) (Finset.mem_singleton_self _)
  have h2 := Gen.step _ h1 (fun n => n + 1) (Finset.mem_singleton_self _)
  exact Gen.step _ h2 (fun n => n + 1) (Finset.mem_singleton_self _)

example : SG {fun n => n + 1} 0 (GeneratedSet {fun n => n + 1} 0) :=
  generated_isSG

example : FixedPoint {fun n => n + 1} 0 (GeneratedSet {fun n => n + 1} 0) :=
  generated_fixedPoint

example (C : Set Nat) (hC : FixedPoint {fun n => n + 1} 0 C) :
    C = GeneratedSet {fun n => n + 1} 0 :=
  fixedPoint_eq_generated succ_strictGrowth hC

end MetaMathlibExt.SelfGeneratingSet
