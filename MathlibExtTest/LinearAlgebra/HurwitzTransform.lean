/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.HurwitzTransform

@[expose] public section

open MetaMathlibExt

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzTransform a b 0 = a 0 :=
  hurwitzTransform_zero a b

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzTransform a b 1 = a 0 * b 1 - a 1 * b 0 :=
  hurwitzTransform_one a b

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzMatrix a b 2 ⟨0, by decide⟩ ⟨1, by decide⟩ = a 1 := by
  simp [hurwitzMatrix, hurwitzEntry]

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzMatrix a b 2 ⟨1, by decide⟩ ⟨1, by decide⟩ = b 1 := by
  simp [hurwitzMatrix, hurwitzEntry]

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzMatrix a b 2 ⟨2, by decide⟩ ⟨0, by decide⟩ = 0 := by
  simp [hurwitzMatrix, hurwitzEntry]

example {R : Type*} [CommRing R] (a b : ℕ → R) :
    hurwitzMatrix a b 3 ⟨3, by decide⟩ ⟨0, by decide⟩ = 0 := by
  simp [hurwitzMatrix, hurwitzEntry]

example {R : Type*} [CommRing R] (a : ℕ → R) :
    hurwitzSingle a 0 = a 0 := by
  simp [hurwitzSingle, hurwitzTransform_zero]
