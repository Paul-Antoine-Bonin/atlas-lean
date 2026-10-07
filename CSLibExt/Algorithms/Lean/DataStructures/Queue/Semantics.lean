/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Init.Data.Queue

import all Init.Data.Queue

/-!
# FIFO semantics for `Std.Queue`

This file exposes the logical FIFO sequence represented by Lean's two-list queue and proves the
behavior of the basic queue operations against that sequence. It makes no complexity claims.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.Queue

universe u

variable {α : Type u}

/-- The elements of a queue in FIFO order. -/
def contents (q : Std.Queue α) : List α :=
  q.dList ++ q.eList.reverse

@[simp]
theorem contents_empty : contents (Std.Queue.empty : Std.Queue α) = [] := by
  rfl

/-- Converting a queue to an array preserves its FIFO contents. -/
@[simp]
theorem toArray_toList (q : Std.Queue α) : q.toArray.toList = contents q := by
  simp [Std.Queue.toArray, contents]

/-- Enqueueing places one element at the end of the FIFO contents. -/
@[simp]
theorem contents_enqueue (q : Std.Queue α) (value : α) :
    contents (q.enqueue value) = contents q ++ [value] := by
  simp [Std.Queue.enqueue, contents, List.append_assoc]

/-- A queue reports that it is empty exactly when its FIFO contents are empty. -/
@[simp]
theorem isEmpty_eq_true_iff (q : Std.Queue α) :
    q.isEmpty = true ↔ contents q = [] := by
  cases q with
  | mk eList dList => simp [Std.Queue.isEmpty, contents, Bool.and_eq_true, List.isEmpty_iff]

/-- Dequeueing fails exactly when the FIFO contents are empty. -/
@[simp]
theorem dequeue?_eq_none_iff (q : Std.Queue α) :
    q.dequeue? = none ↔ contents q = [] := by
  cases q with
  | mk eList dList =>
      cases dList with
      | cons head tail => simp [Std.Queue.dequeue?, contents]
      | nil =>
          cases eList with
          | nil => simp [Std.Queue.dequeue?, contents]
          | cons head tail =>
              cases h : tail.reverse <;> simp [Std.Queue.dequeue?, contents, h]

/-- A successful dequeue returns the FIFO head and a queue representing the remaining tail. -/
theorem contents_eq_cons_of_dequeue?_eq_some
    {q : Std.Queue α} {head : α} {rest : Std.Queue α}
    (h : q.dequeue? = some (head, rest)) :
    contents q = head :: contents rest := by
  cases q with
  | mk eList dList =>
      cases dList with
      | cons d ds =>
          simp [Std.Queue.dequeue?] at h
          obtain ⟨hhead, hrest⟩ := h
          cases hhead
          cases hrest
          rfl
      | nil =>
          cases hr : eList.reverse with
          | nil => simp [Std.Queue.dequeue?, hr] at h
          | cons d ds =>
              simp [Std.Queue.dequeue?, hr] at h
              obtain ⟨hhead, hrest⟩ := h
              cases hhead
              cases hrest
              simpa [contents] using hr

end Cslib.Algorithms.Lean.Queue
