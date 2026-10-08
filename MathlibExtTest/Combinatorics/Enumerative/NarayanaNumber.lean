/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.NarayanaNumber

namespace MetaMathlibExt

example : narayana ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 := by decide
example : narayana ⟨3, by decide⟩ ⟨2, by decide⟩ = 3 := by decide
example : narayana ⟨3, by decide⟩ ⟨4, by decide⟩ = 0 := by decide

#print axioms narayana_eq_second

end MetaMathlibExt
