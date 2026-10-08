/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.Elliptic.Function

@[expose] public section

example (L : PeriodPair) (c : ℂ) : L.IsEllipticFunction fun _ ↦ c :=
  PeriodPair.IsEllipticFunction.const L c

example (L : PeriodPair) : L.IsEllipticFunction L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

example {L : PeriodPair} {f g : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (hg : L.IsEllipticFunction g) :
    L.IsEllipticFunction (f + g) :=
  hf.add hg
