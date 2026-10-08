/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Padics.HilbertSymbol.Units

/-!
# Tests for Hilbert symbols of p-adic integer units
-/

set_option autoImplicit false

@[expose] public section

namespace HilbertSymbol

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example :
    (unitZpToQp (p := 3) (1 : ℤ_[3]ˣ) : ℚ_[3]) =
      (((1 : ℤ_[3]ˣ) : ℤ_[3]) : ℚ_[3]) :=
  unitZpToQp_coe (1 : ℤ_[3]ˣ)

example :
    ∃ (x₀ y₀ : ℤ_[3]) (z₀ : ℤ_[3]ˣ),
      (z₀ : ℤ_[3]) ^ 2 =
        ((1 : ℤ_[3]ˣ) : ℤ_[3]) * x₀ ^ 2 +
          ((1 : ℤ_[3]ˣ) : ℤ_[3]) * y₀ ^ 2 :=
  chevalley_warning_hensel_lift 3 (by decide) 1 1

example :
    padicHilbertSymbol 3
      (unitZpToQp (1 : ℤ_[3]ˣ))
      (unitZpToQp (1 : ℤ_[3]ˣ)) = 1 :=
  hilbert_symbol_units_eq_one_of_odd 3 (by decide) 1 1

end HilbertSymbol
