/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultipleZeta.Index

namespace MetaMathlibExt.MultipleZeta

private def emptyIndex : Index :=
  ⟨0, ⟨[], by simp, by simp⟩⟩

private def oneIndex : Index :=
  ⟨1, ⟨[1], by simp, by simp⟩⟩

private def twoIndex : Index :=
  ⟨2, ⟨[2], by simp, by simp⟩⟩

private def heightExample : Index :=
  ⟨5, ⟨[1, 2, 2], by simp, by decide⟩⟩

example : emptyIndex.entries = [] := rfl
example : emptyIndex.depth = 0 := rfl
example : emptyIndex.height = 0 := rfl
example : ¬emptyIndex.IsAdmissible := by
  simp [emptyIndex, Index.IsAdmissible]

example : ¬oneIndex.IsAdmissible := by
  simp [oneIndex, Index.IsAdmissible]

example : twoIndex.IsAdmissible := by
  simp [twoIndex, Index.IsAdmissible]

example (index : Index) :
    index.IsAdmissible ↔ IsAdmissible index.entries :=
  index.isAdmissible_iff

example : ¬IsAdmissible [] := by
  simp

example : ¬IsAdmissible [1] := by
  simp [IsAdmissible]

example : IsAdmissible [2] := by
  simp [IsAdmissible]

example : IsAdmissible [2, 1] := by
  simp [IsAdmissible]

example : ¬IsAdmissible [2, 0] := by
  simp [IsAdmissible]

example : heightExample.entries = [1, 2, 2] := rfl
example : heightExample.weight = 5 := rfl
example : heightExample.depth = 3 := rfl
example : heightExample.height = 2 := rfl

example (index : Index) : index.entries.sum = index.weight := by
  rcases index with ⟨weight, composition⟩
  exact composition.blocks_sum

private def one : PNat := ⟨1, Nat.zero_lt_succ 0⟩

private def two : PNat := ⟨2, Nat.zero_lt_succ 1⟩

private lemma ofList_replicate (n : ℕ) :
    FreeMonoid.ofList (List.replicate n false) =
      (FreeMonoid.of false) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.replicate_succ, FreeMonoid.ofList_cons, ih, pow_succ']

example : FreeMonoid.toList (hoffmanBlock one) = [true] := by
  simp [one]

example : FreeMonoid.toList (hoffmanBlock two) = [false, true] := by
  simp [two]

example (k : PNat) : 0 < k.val := k.property

example (k : PNat) :
    hoffmanBlock k =
      (FreeMonoid.of false) ^ (k.val - 1) * FreeMonoid.of true := by
  rw [hoffmanBlock, FreeMonoid.ofList_append, ofList_replicate,
    FreeMonoid.ofList_singleton]

end MetaMathlibExt.MultipleZeta
