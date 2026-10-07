/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fintype.Defs
public import Mathlib.GroupTheory.FreeGroup.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AutFnAutomaticQuestion73Wanted

/-!
# Question 7.3 — Is Aut(Fn) automatic for n > 3? (AMR-109-0302)

Stable source identifiers:
- Source list: Farb - Problems on Mapping Class Groups and Related Topics
- Source item: Question 7.3, PDF page 339
- Source URL: https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf

Clause list (every hypothesis, side condition, and quantifier domain in the source):
1. `n : ℕ`: rank parameter.
2. `3 < n`: strict threshold from the source ("n > 3"), open at 3.
3. `Fn = FreeGroup (Fin n)`: free group on `n` generators (Mathlib `FreeGroup`).
4. `Aut(Fn) = MulAut (FreeGroup (Fin n))`: automorphism group (Mathlib `MulAut`).
5. `automatic`: standard automatic-group property applied to `Aut(Fn)`.
6. Claim form: question whether (5) holds for all `n` satisfying (1)-(2); posed as open
   in the source, since resolved (see the entry metadata); no proof in this repository.
-/

/-- Automatic-group property for Question 7.3 [AMR-109-0302] (Farb - Problems on Mapping Class Groups and Related Topics, Question 7.3, PDF p. 339, https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf): finite alphabet closed under inversion with evaluation into `G`, a regular language of words recognized by a finite-state automaton, surjection onto `G`, and fellow-traveler bounds for equal and generator-adjacent words.
This is the fellow-traveller characterization of automatic groups (Epstein et al., Word
Processing in Groups, Theorem 2.3.5). -/
def IsAutomaticGroup (G : Type*) [Group G] : Prop :=
  ∃ (A : Type) (_ : Fintype A) (inv : A → A),
    (∀ a, inv (inv a) = a) ∧
    ∃ (eval : A → G),
      (∀ a, eval (inv a) = (eval a)⁻¹) ∧
      ∃ (L : List A → Prop),
        (∃ (State : Type) (_ : Fintype State) (start : State)
            (step : State → A → State) (accept : State → Bool),
            ∀ w : List A, L w ↔ accept (List.foldl step start w) = true) ∧
        (∀ g : G, ∃ w : List A, L w ∧ List.prod (List.map eval w) = g) ∧
        ∃ k : ℕ,
          (∀ u v : List A, L u → L v →
              List.prod (List.map eval u) = List.prod (List.map eval v) →
              ∀ t : ℕ, ∃ w : List A,
                List.length w ≤ k ∧
                  (List.prod (List.map eval (List.take t u)))⁻¹ *
                    List.prod (List.map eval (List.take t v)) =
                    List.prod (List.map eval w)) ∧
          ∀ u v : List A, L u → L v → ∀ a : A,
            List.prod (List.map eval u) * eval a =
              List.prod (List.map eval v) →
            ∀ t : ℕ, ∃ w : List A,
              List.length w ≤ k ∧
                (List.prod (List.map eval (List.take t u)))⁻¹ *
                  List.prod (List.map eval (List.take t v)) =
                  List.prod (List.map eval w)

/-- Question 7.3 [AMR-109-0302] (Farb - Problems on Mapping Class Groups and Related Topics, Question 7.3, PDF p. 339, https://www.math.uchicago.edu/~farb/papers/mcgbook.pdf): is `Aut(Fn)` automatic for `n > 3`, where `Fn = FreeGroup (Fin n)` and `Aut(Fn)` is `MulAut (FreeGroup (Fin n))`? Stated as an open universal implication; proved by nothing. -/
def conjecture : Prop :=
  ∀ n : ℕ, 3 < n → IsAutomaticGroup (MulAut (FreeGroup (Fin n)))

/--
Resolved false: Bridson and Vogtmann (Ann. Inst. Fourier 62 (2012), arXiv:1011.1506), with
Handel-Mosher, proved that Aut(F_n) has exponential Dehn function for every n >= 3; automatic
groups have quadratic Dehn functions (Epstein et al.), so Aut(F_n) is not automatic for any n >
3. Source: M. R. Bridson, K. Vogtmann, The Dehn functions of Out(F_n) and Aut(F_n), Annales de
l'Institut Fourier 62(5) (2012) 1811-1817, arXiv:1011.1506, https://arxiv.org/abs/1011.1506.
Moved from `OpenConjectures/GroupTheory/AutFnAutomaticQuestion73`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.AutFnAutomaticQuestion73Wanted
