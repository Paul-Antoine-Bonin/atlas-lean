/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.Manifold.MorseExistence
import Mathlib.Geometry.Manifold.Instances.Sphere

open scoped Manifold

open MathlibExt.Geometry.Manifold.MorseExistenceWanted
open MathlibExt.Geometry.Manifold.ReebSphereWanted

-- The Euclidean plane admits a Morse function.
example : ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
    IsMorseFunction (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))) f :=
  morse_function_exists

-- Every finite-dimensional unit sphere admits a Morse function.
example (n : ℕ) :
    ∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → ℝ,
      IsMorseFunction (I := 𝓡 n) f :=
  morse_function_exists
