/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

namespace MetaMathlibExt

private def probeMorphism : Bool → List Bool
  | false => [false, true]
  | true => [true]

example : morphIterate probeMorphism 0 [false] = [false] := rfl
example : morphIterate probeMorphism 1 [false] = [false, true] := rfl
example : morphIterate probeMorphism 2 [false] = [false, true, true] := rfl
example : IsNonErasing probeMorphism := by intro b; cases b <;> decide

example (n : ℕ) : (morphIterate (fun x : Fin 2 => [x, 1 - x]) n [0]).length = 2 ^ n := by
  rw [morphIterate_length_of_uniform (k := 2) (fun _ => rfl), List.length_singleton, Nat.mul_one]

private def doublingUnitMorphism (_ : Unit) : List Unit := [(), ()]

private def constantUnitWord (_ : Nat) : Unit := ()

private theorem doublingUnitMorphism_length (w : List Unit) :
    (morphExtend doublingUnitMorphism w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp [morphExtend, doublingUnitMorphism]
    omega

private theorem doublingUnitIterate_length (n : Nat) :
    (morphIterate doublingUnitMorphism n [()]).length = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [morphIterate, doublingUnitMorphism_length, ih, pow_succ]
    omega

private theorem self_le_two_pow (n : Nat) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hpos : 0 < 2 ^ n := pow_pos (by omega) n
    omega

/-- Concrete witness exercising both prolongability and omega-limit clauses. -/
example : IsPureMorphic constantUnitWord := by
  refine ⟨doublingUnitMorphism, (), ?_, ?_⟩
  · refine ⟨[()], rfl, ?_⟩
    intro n hnil
    have hlen := congrArg List.length hnil
    rw [doublingUnitIterate_length] at hlen
    simp at hlen
  · constructor
    · intro M
      exact ⟨M, by rw [doublingUnitIterate_length]; exact self_le_two_pow M⟩
    · intro n i h
      exact Subsingleton.elim _ _

#print axioms IsPureMorphic

end MetaMathlibExt
