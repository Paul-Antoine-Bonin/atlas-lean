/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimeCounting.RamanujanPrime

namespace MetaMathlibExt

example {R n : ℕ} (hp : R.Prime)
    (hcount : Nat.primeCounting R - Nat.primeCounting (R / 2) = n) :
    IsRamanujanPrime R n :=
  ⟨hp, hcount⟩

example {R n : ℕ} (h : IsRamanujanPrime R n) : R.Prime := h.1

end MetaMathlibExt
