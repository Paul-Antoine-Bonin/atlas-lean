/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.Units

@[expose] public section

open NumberField
open scoped NumberField

namespace MathlibExtTest.NumberTheory.Units

/-- For `ℚ` the off-diagonal hypothesis holds vacuously, so the closure of a
constant-one `InfinitePlace ℚ`-indexed family of units has finite index. -/
example :
    (Subgroup.closure (Set.range (fun _ : InfinitePlace ℚ => (1 : (𝓞 ℚ)ˣ)))).FiniteIndex :=
  NumberField.Units.finiteIndex_closure_range_of_lt_one_off_diagonal _ fun v w h =>
    absurd (Subsingleton.elim w v) h

end MathlibExtTest.NumberTheory.Units
