/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Data.Finset.PropertyB

-- The empty family has property B vacuously.
example {α : Type*} : (∅ : Finset (Finset α)).HasPropertyB :=
  ⟨fun _ => 0, fun A h => (Finset.notMem_empty A h).elim⟩
