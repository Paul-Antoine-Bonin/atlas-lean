/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.NumberTheory.NumberField.RayClass.RayGroup

@[expose] public noncomputable section

open scoped Classical nonZeroDivisors
open NumberField

namespace N403RayGroupTest

variable {K : Type*} [Field K] [NumberField K]

example (m : Modulus K) :
    (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) ∈ Modulus.coprimeFractionalIdeals m :=
  one_mem _

example (m : Modulus K) : Modulus.CongruentOneAtFinitePart m 1 :=
  fun _ _ => Or.inl rfl

example (m : Modulus K) : Modulus.PositiveAtInfinitePart m 1 :=
  Modulus.positiveAtInfinitePart_one m

example (m : Modulus K) : Modulus.IsRayElementOne m 1 :=
  Modulus.isRayElementOne_one m

example (m : Modulus K) :
    (⟨toPrincipalIdeal (𝓞 K) K 1,
      Subgroup.mem_comap.mp (Modulus.isRayElementOne_one m).1⟩ :
      Modulus.coprimeFractionalIdeals m) ∈ Modulus.rayGroup m :=
  Modulus.mem_rayGroup_of_isRayElementOne m 1 (Modulus.isRayElementOne_one m)

example (m : Modulus K) : CommGroup (Modulus.coprimeFractionalIdeals m) :=
  inferInstance

example (m : Modulus K) :
    Group (Modulus.coprimeFractionalIdeals m ⧸ Modulus.rayGroup m) :=
  inferInstance

end N403RayGroupTest
