module

public import MathlibExt.Combinatorics.Enumerative.EulerSeidelMatrix

namespace MetaMathlibExt

example : eulerSeidelMatrix (fun n : ℕ => n) 2 0 = 2 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 2 2 = 12 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 0 2 = 4 := by
  rw [eulerSeidelMatrix_eq_sum]
  rfl

end MetaMathlibExt
