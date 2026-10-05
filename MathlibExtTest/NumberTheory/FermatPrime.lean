module

public import MathlibExt.NumberTheory.FermatPrime
public import Mathlib.Tactic.NormNum.Prime

namespace MetaMathlibExt

example : IsFermatPrime 3 := by
  refine ⟨by norm_num, 0, ?_⟩
  rfl

example : IsFermatPrime 5 := by
  refine ⟨by norm_num, 1, ?_⟩
  rfl

end MetaMathlibExt
