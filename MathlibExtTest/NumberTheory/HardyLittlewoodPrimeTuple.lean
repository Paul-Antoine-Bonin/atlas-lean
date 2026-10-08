/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HardyLittlewoodPrimeTuple

namespace MetaMathlibExt

noncomputable section

example : hardyLittlewoodResidueCount 0 Fin.elim0 2 = 0 := by decide
example : hardyLittlewoodResidueCount 2 (fun i => (i.val : ℤ)) 2 = 2 := by decide

#print axioms hardyLittlewoodResidueCount
#print axioms hardyLittlewoodPrimeTupleCount
#print axioms hardyLittlewoodSingularSeries

end

end MetaMathlibExt
