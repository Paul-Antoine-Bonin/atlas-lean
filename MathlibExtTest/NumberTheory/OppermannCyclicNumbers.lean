module

import Mathlib.Tactic
public import MathlibExt.NumberTheory.OppermannCyclicNumbers

namespace MetaMathlibExt

example : IsCyclicNumber 15 := by
  unfold IsCyclicNumber
  decide

example : ¬ IsCyclicNumber 4 := by
  unfold IsCyclicNumber
  decide
example : oppermannCyclicCountLeft 2 = 2 := by decide

end MetaMathlibExt
