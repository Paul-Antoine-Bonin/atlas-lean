/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.EulerSeidelMatrix

namespace MetaMathlibExt

example : eulerSeidelMatrix (fun n : ℕ => n) 2 0 = 2 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 2 2 = 12 := by rfl
example : eulerSeidelMatrix (fun n : ℕ => n) 0 2 = 4 := by
  rw [eulerSeidelMatrix_eq_sum]
  rfl

end MetaMathlibExt
