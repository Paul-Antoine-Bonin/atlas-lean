/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.Module.QuillenSuslin

-- A finitely generated projective module over a two-variable rational polynomial ring is free.
example {M : Type*} [AddCommGroup M]
    [Module (MvPolynomial (Fin 2) ℚ) M]
    [Module.Finite (MvPolynomial (Fin 2) ℚ) M]
    [Module.Projective (MvPolynomial (Fin 2) ℚ) M] :
    Module.Free (MvPolynomial (Fin 2) ℚ) M :=
  MathlibExt.Algebra.Module.QuillenSuslinWanted.quillen_suslin
