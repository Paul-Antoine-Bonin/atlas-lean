module

public import MathlibExt.NumberTheory.AlmostBeattyPartition

namespace MetaMathlibExt

@[expose] public section

public example (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    IsAlmostBeattySequence (fun n => beattyTerm n α) α :=
  beattyTerm_isAlmostBeattySequence α hα0 hα1

public example (n : { n : ℕ // 0 < n }) (α : ℝ) :
    beattyTerm n α = (beattySeq (1 / α) (n.val : ℤ)).toNat := rfl

public example (n : { n : ℕ // 0 < n }) (α : ℝ) :
    beattyTerm n α = Nat.floor ((n.val : ℝ) / α) :=
  beattyTerm_eq_floor n α

public example {s1 s2 s3 : { n : ℕ // 0 < n } → ℕ} (h : IsPositiveNatThreeWayPartition s1 s2 s3)
    (n : { n : ℕ // 0 < n }) : s1 n ≠ 0 := by
  intro h0
  exact (lt_irrefl 0) ((h.2.2.2 0).mp ⟨n, Or.inl h0⟩)

public example {s1 s2 s3 : { n : ℕ // 0 < n } → ℕ} (α1 α2 α3 : ℝ)
    (h : IsAlmostBeattyPartition s1 s2 s3 α1 α2 α3) :
    IsPositiveNatThreeWayPartition s1 s2 s3 :=
  h.2.2.2

end

end MetaMathlibExt
