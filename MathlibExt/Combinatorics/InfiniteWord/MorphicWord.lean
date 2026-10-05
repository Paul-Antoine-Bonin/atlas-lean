module

public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

namespace MetaMathlibExt

@[expose] public section

/-- A morphic word is the normalized coding image of a pure morphic word.

Concept `jis_sem_8aa01797a09c6951299c4a2d`; source statements
`jis_305f669a0778b2b0011670ec`, `jis_59581da9ed7395999b79fb6c`,
`jis_d868c1fc64073e778b524189`, and `jis_de6cb6fe1f9e977bace8a77d`. -/
public def IsMorphic {A B : Type*} [Finite A] (u : Nat → A) (coding : A → B) (w : Nat → B) : Prop :=
  IsPureMorphic u ∧ ∀ n, w n = coding (u n)

/-- Pointwise introduction for morphic words (concept
`jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`). -/
public theorem IsMorphic.intro {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (hPure : IsPureMorphic u)
    (hCode : ∀ n, w n = coding (u n)) : IsMorphic u coding w :=
  ⟨hPure, hCode⟩

/-- Left projection for morphic words (concept
`jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`). -/
public theorem IsMorphic.pure {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (h : IsMorphic u coding w) : IsPureMorphic u :=
  h.1

/-- Pointwise elimination for morphic words (concept
`jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`). -/
public theorem IsMorphic.coding_eq {A B : Type*} [Finite A] {u : Nat → A} {coding : A → B}
    {w : Nat → B} (h : IsMorphic u coding w) (n : Nat) : w n = coding (u n) :=
  h.2 n

/-- Every pure morphic word is morphic via the identity coding (concept
`jis_sem_8aa01797a09c6951299c4a2d`; statements `jis_305f669a0778b2b0011670ec`,
`jis_59581da9ed7395999b79fb6c`, `jis_d868c1fc64073e778b524189`, and
`jis_de6cb6fe1f9e977bace8a77d`). -/
public theorem IsMorphic.ofPureMorphic {A : Type*} [Finite A] {u : Nat → A}
    (hu : IsPureMorphic u) : IsMorphic u id u :=
  ⟨hu, fun _ => rfl⟩

end

end MetaMathlibExt
