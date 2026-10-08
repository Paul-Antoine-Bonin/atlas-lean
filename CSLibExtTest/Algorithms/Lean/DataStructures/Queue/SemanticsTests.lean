/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Queue.Semantics

import all Init.Data.Queue

@[expose] public section

/-!
# Tests for `Std.Queue` FIFO semantics

These examples exercise the empty queue, a singleton, repeated enqueueing, and the reversal of
the enqueue list when the first element is dequeued.
-/

namespace Cslib.Algorithms.Lean.Queue.SemanticsTests

private def singleton : Std.Queue Nat :=
  Std.Queue.empty.enqueue 7

private def threeElements : Std.Queue Nat :=
  ((Std.Queue.empty.enqueue 1).enqueue 2).enqueue 3

example : Queue.contents (Std.Queue.empty : Std.Queue Nat) = [] := by
  simp

example : (Std.Queue.empty : Std.Queue Nat).isEmpty = true := by
  simp only [Queue.isEmpty_eq_true_iff, Queue.contents_empty]

example : (Std.Queue.empty : Std.Queue Nat).dequeue? = none := by
  exact (Queue.dequeue?_eq_none_iff _).mpr Queue.contents_empty

example : Queue.contents singleton = [7] := by
  simp [singleton]

example : Queue.contents threeElements = [1, 2, 3] := by
  simp [threeElements]

example : threeElements.toArray.toList = [1, 2, 3] := by
  rw [Queue.toArray_toList]
  simp [threeElements]

example :
    match threeElements.dequeue? with
    | none => False
    | some (head, rest) => head = 1 ∧ Queue.contents rest = [2, 3] := by
  simp [threeElements, Std.Queue.dequeue?, Std.Queue.enqueue, Std.Queue.empty, Queue.contents]

example {q q' : Std.Queue Nat} {head : Nat} (h : q.dequeue? = some (head, q')) :
    Queue.contents q = head :: Queue.contents q' :=
  Queue.contents_eq_cons_of_dequeue?_eq_some h

end Cslib.Algorithms.Lean.Queue.SemanticsTests
