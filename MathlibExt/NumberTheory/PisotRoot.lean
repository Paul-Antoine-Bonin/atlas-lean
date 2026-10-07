/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PisotNumber

namespace MetaMathlibExt

@[expose] public section

/-!
# Unique Pisot roots

Source: M. Panju, *Beta expansions for regular Pisot numbers*, Journal of Integer Sequences
14 (2011), Article 11.6.4,
[`panju2.tex`](https://cs.uwaterloo.ca/journals/JIS/VOL14/Panju/panju2.tex).
-/

/-- `r` is the unique Pisot number that is a root of `P`. -/
public def IsUniquePisotRoot (P : Polynomial ℝ) (r : ℝ) : Prop :=
  IsPisotNumber r ∧ P.IsRoot r ∧
    ∀ s, IsPisotNumber s → P.IsRoot s → s = r

end

end MetaMathlibExt
