/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PRecursiveSequence

namespace MetaMathlibExt

example (r : ℕ) (P : Fin (r + 1) → Polynomial ℤ) :
    IsPRecursiveSequence r P (fun _ => 0) := by
  intro n hn
  simp

end MetaMathlibExt
