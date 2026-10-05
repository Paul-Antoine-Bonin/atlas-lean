module

public import MathlibExt.NumberTheory.PRecursiveSequence

namespace MetaMathlibExt

example (r : ℕ) (P : Fin (r + 1) → Polynomial ℤ) :
    IsPRecursiveSequence r P (fun _ => 0) := by
  intro n hn
  simp

end MetaMathlibExt
