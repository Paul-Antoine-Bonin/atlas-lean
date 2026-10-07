/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.EventuallyPeriodicSequence
import Mathlib.Data.ZMod.Defs

namespace MetaMathlibExt

example {α : Type*} (a : α) : IsEventuallyPeriodic (fun _ : ℕ => a) :=
  IsEventuallyPeriodic.of_periodic (p := 1) (by decide) fun _ => rfl

example {α : Type*} {u : ℕ → α} :
    IsUltimatelyPeriodic u = IsEventuallyPeriodic u :=
  rfl

example : IsEventuallyPeriodic (fun n : ℕ => ((n : ℕ) : ZMod 3)) :=
  .of_finite_orbit (· + 1) _ fun n => Nat.cast_succ n

end MetaMathlibExt
