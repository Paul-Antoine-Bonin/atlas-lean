module

import Mathlib.Tactic
public import MathlibExt.Combinatorics.Enumerative.PartialBellPolynomial

namespace MetaMathlibExt

example : partialBellPolynomial 0 0 (fun _ => (1 : ℕ)) = 1 := by decide
example : partialBellPolynomial 3 2 (fun _ => (1 : ℕ)) = 3 := by decide

end MetaMathlibExt
