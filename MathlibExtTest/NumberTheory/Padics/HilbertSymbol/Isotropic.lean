/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Isotropic

/-!
# Tests for isotropy of unit diagonal forms over `ℚ_[p]`
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example (a : Fin 3 → ℤ_[3]ˣ) :
    ∃ x : Fin 3 → ℚ_[3], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[3]) : ℚ_[3]) * (x i) ^ 2 = 0 :=
  diagonal_unit_isotropic 3 (by decide) (by decide) a

example (a : Fin 4 → ℤ_[3]ˣ) :
    ∃ x : Fin 4 → ℚ_[3], x ≠ 0 ∧ ∑ i, ((a i : ℤ_[3]) : ℚ_[3]) * (x i) ^ 2 = 0 :=
  diagonal_unit_isotropic 3 (by decide) (by decide) a

end HilbertSymbol
