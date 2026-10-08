/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.VanDerLaanSequence

namespace MetaMathlibExt

example : IsVanDerLaanWindow 1 1 1 2 := by
  unfold IsVanDerLaanWindow
  decide

example : IsVanDerLaanWindow 2 3 4 5 := by
  unfold IsVanDerLaanWindow
  decide

example : ¬ IsVanDerLaanWindow 1 1 1 1 := by
  unfold IsVanDerLaanWindow
  decide

example : IsVanDerLaan (fun _ => 0) :=
  isVanDerLaan_const_iff.mpr rfl

example (k : ℕ) : IsVanDerLaan (fun _ => k) ↔ k = 0 :=
  isVanDerLaan_const_iff

example : IsVanDerLaanWindow 2 3 4 5 ↔ 5 = 2 + 3 :=
  isVanDerLaanWindow_ordered_iff (by omega) (by omega) (by omega)

end MetaMathlibExt
