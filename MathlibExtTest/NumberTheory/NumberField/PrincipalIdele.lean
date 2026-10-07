/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.PrincipalIdele

@[expose] public section

noncomputable section

open NumberField NumberField.TopologicalIdeleGroup

variable (K : Type*) [Field K] [NumberField K]

example : DiscreteTopology (principalIdeles (𝓞 K) K) :=
  principalIdeles_discrete K

example : IsOpen ({1} : Set (principalIdeles (𝓞 ℚ) ℚ)) := by
  let _ : DiscreteTopology (principalIdeles (𝓞 ℚ) ℚ) :=
    principalIdeles_discrete ℚ
  exact isOpen_discrete _

example (X : Type*) [TopologicalSpace X] (f : principalIdeles (𝓞 K) K → X) :
    Continuous f := by
  let _ : DiscreteTopology (principalIdeles (𝓞 K) K) :=
    principalIdeles_discrete K
  exact continuous_of_discreteTopology
