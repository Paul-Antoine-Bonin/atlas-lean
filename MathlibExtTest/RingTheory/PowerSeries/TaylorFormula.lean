/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.PowerSeries.TaylorFormula

@[expose] public section

namespace PowerSeriesTaylorFormulaTest

/-- Compile-time consumer of the public Taylor identity. -/
example {R : Type*} [CommRing R] [Algebra ℚ R] (f : PowerSeries R) :
    (fun d : Fin 2 →₀ ℕ =>
      ((d 1).factorial : ℚ)⁻¹ •
        PowerSeries.coeff (d 0) (((PowerSeries.derivative)^[d 1]) f)) =
      MvPowerSeries.subst
        (fun _ : Unit =>
          MvPowerSeries.X (0 : Fin 2) + MvPowerSeries.X (1 : Fin 2)) f :=
  PowerSeries.taylorFormula f

end PowerSeriesTaylorFormulaTest
