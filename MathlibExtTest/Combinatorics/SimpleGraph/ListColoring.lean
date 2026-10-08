/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.ListColoring

@[expose] public section

open SimpleGraph

/-- The one-vertex graph is list-colorable from every nonempty list. -/
private theorem finOne_isListColorable :
    (⊥ : SimpleGraph (Fin 1)).IsListColorable 1 := by
  intro C _ lists hlists
  have hnonempty : (lists 0).Nonempty :=
    Finset.card_pos.mp (Nat.zero_lt_one.trans_le (hlists 0))
  let c : C := hnonempty.choose
  refine ⟨⟨fun _ => c, ?_⟩, fun v => ?_⟩
  · simp
  · have hv : v = 0 := Subsingleton.elim _ _
    subst v
    exact hnonempty.choose_spec

/-- The one-vertex graph has choice number one, including the zero boundary. -/
example : (⊥ : SimpleGraph (Fin 1)).IsChoiceNumber 1 := by
  refine ⟨finOne_isListColorable, ?_⟩
  intro q hq
  have hq0 : q = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hq)
  subst q
  intro hzero
  obtain ⟨color, _⟩ := hzero Empty (fun _ => ∅) (by simp)
  exact (color 0).elim

/-- Requiring larger lists preserves list colorability. -/
example {V : Type*} (G : SimpleGraph V) (hG : G.IsListColorable 2) :
    G.IsListColorable 3 :=
  hG.mono (by decide)

/-- The shared notion specializes to ordinary Mathlib vertex colorability. -/
example {V : Type*} (G : SimpleGraph V) (q : ℕ) (hG : G.IsListColorable q) :
    G.Colorable q :=
  hG.colorable

end
