module

public import MathlibExt.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

import Mathlib.Tactic

@[expose] public section

namespace MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion

open MetaMathlibExt

/-- A concrete nonuniform ternary morphism used to exercise the finite test. -/
public def shortSquarefreeMorphism : TernaryAlphabet → List TernaryAlphabet
  | 0 => [0, 1, 2, 0, 1]
  | 1 => [0, 2, 0, 1, 2, 1]
  | 2 => [0, 2, 1, 2, 0, 2, 1]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- Concrete evaluation expands every prefix of every suffix of images of length at most five.
/-- The complete length-five check for `shortSquarefreeMorphism`. -/
public theorem shortSquarefreeMorphism_test (w : List TernaryAlphabet)
    (hlen : w.length ≤ 5) (hw : IsSquareFreeWord w) :
    IsSquareFreeWord (w.flatMap shortSquarefreeMorphism) := by
  rcases w with _ | ⟨a, w⟩
  · rw [isSquareFreeWord_iff_inits_tails]
    decide
  rcases w with _ | ⟨b, w⟩
  · fin_cases a <;> rw [isSquareFreeWord_iff_inits_tails] <;> decide
  rcases w with _ | ⟨c, w⟩
  · fin_cases a <;> fin_cases b <;>
      simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  rcases w with _ | ⟨d, w⟩
  · fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  rcases w with _ | ⟨e, w⟩
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  rcases w with _ | ⟨g, w⟩
  · fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;>
      simp_all +decide [isSquareFreeWord_iff_inits_tails, shortSquarefreeMorphism]
  · simp at hlen
    omega

-- The length-five test proves that the concrete nonuniform morphism preserves squarefreeness.
example : ∀ w : List TernaryAlphabet, IsSquareFreeWord w →
    IsSquareFreeWord (w.flatMap shortSquarefreeMorphism) :=
  (crochemore_squarefree_test_set shortSquarefreeMorphism).2
    shortSquarefreeMorphism_test

/-- A morphism whose image of `010` contains the square `2020`. -/
public def failingMorphism : TernaryAlphabet → List TernaryAlphabet
  | 0 => [0, 1, 2]
  | 1 => [0, 2]
  | 2 => [1]

-- Infix closure applies nontrivially, while `010` witnesses failure of the other morphism.
example (h : IsSquareFreeWord ([0, 1, 2] : List TernaryAlphabet)) :
    IsSquareFreeWord ([1, 2] : List TernaryAlphabet) ∧
      ¬ IsSquareFreeWord (([0, 1, 0] : List TernaryAlphabet).flatMap failingMorphism) := by
  constructor
  · exact h.of_isInfix ⟨[0], [], by simp⟩
  · intro hout
    apply hout [2, 0, 2, 0]
    · exact ⟨[0, 1], [1, 2], by decide⟩
    · exact ⟨[2, 0], by simp, rfl⟩

end MathlibExtTest.Combinatorics.InfiniteWord.CrochemoreSquarefreeCriterion
